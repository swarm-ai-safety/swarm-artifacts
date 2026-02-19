/**
 * fn-synthesize-sweep
 *
 * Triggered by: swarm/sweep.completed
 * Action: Generate vault experiment note, update claims, rebuild index,
 *         then emit vault/synthesis.completed.
 *
 * This is the core "arscontexta as the scientist" pipeline step.
 */

import { inngest } from "../client.js";
import { writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import {
  RUNS_DIR, VAULT_DIR, readJson, readYaml, runScript, fileExists,
} from "../helpers.js";

interface RunYaml {
  run_id: string;
  slug: string;
  created_utc: string;
  experiment: {
    type: string;
    hypothesis?: string;
    scenario_ref?: string;
    swept_parameters?: Record<string, unknown[]>;
    seeds: number[];
    total_runs?: number;
  };
  results: {
    status: string;
    primary_metric?: string;
    primary_result?: string;
    significant_findings?: number;
    total_hypotheses_tested?: number;
  };
  artifacts: Record<string, unknown>;
  tags: string[];
  links?: {
    claims?: string[];
  };
}

export const synthesizeSweep = inngest.createFunction(
  {
    id: "synthesize-sweep",
    retries: 3,
    concurrency: { limit: 2 }, // avoid overwhelming disk I/O
  },
  { event: "swarm/sweep.completed" },
  async ({ event, step, logger }) => {
    const { run_id, total_runs, bonferroni_significant } = event.data;
    const runDir = resolve(RUNS_DIR, run_id);

    // 1. Read run metadata
    const runMeta = await step.run("read-run-yaml", async () => {
      return readYaml<RunYaml>(resolve(runDir, "run.yaml"));
    });

    // 2. Generate experiment note
    const experimentNote = await step.run("generate-experiment-note", async () => {
      const tags = runMeta.tags;
      const swept = runMeta.experiment.swept_parameters ?? event.data.swept_parameters;
      const sweptStr = Object.entries(swept)
        .map(([k, v]) => `- \`${k}\`: ${JSON.stringify(v)}`)
        .join("\n");

      const note = `---
description: "${runMeta.slug}: ${total_runs}-run sweep with ${bonferroni_significant} significant findings"
type: experiment
status: ${runMeta.results.status}
run_id: "${run_id}"
experiment_type: sweep
created: ${runMeta.created_utc.slice(0, 10)}
---

## Design

- **Hypothesis**: ${runMeta.experiment.hypothesis ?? "Not specified"}
- **Type**: Parameter sweep
- **Parameters swept**:
${sweptStr}
- **Seeds**: ${runMeta.experiment.seeds.length > 5 ? `${runMeta.experiment.seeds.length} seeds` : runMeta.experiment.seeds.join(", ")}
- **Total runs**: ${total_runs}

## Key results

- ${bonferroni_significant} Bonferroni-significant findings out of ${event.data.total_hypotheses} hypotheses tested
${runMeta.results.primary_result ? `- Primary: ${runMeta.results.primary_result}` : ""}

## Artifacts

- Summary: \`runs/${run_id}/summary.json\`
${event.data.sweep_csv_path ? `- Sweep CSV: \`${event.data.sweep_csv_path}\`` : ""}

## Reproduction

\`\`\`bash
python -m swarm sweep ${runMeta.experiment.scenario_ref ?? "scenarios/<scenario>.yaml"} --seeds ${runMeta.experiment.seeds.length}
\`\`\`

<!-- topics: ${tags.join(", ")} -->
`;

      const notePath = resolve(VAULT_DIR, "experiments", `${run_id}.md`);
      await writeFile(notePath, note, "utf-8");
      return notePath;
    });

    // 3. Check if any existing claims should be updated
    const claimUpdates = await step.run("check-claim-updates", async () => {
      // Scan vault/claims/ for claims whose tags overlap with this run's tags
      const claimsDir = resolve(VAULT_DIR, "claims");
      const { readdir } = await import("node:fs/promises");

      let claimFiles: string[];
      try {
        claimFiles = (await readdir(claimsDir)).filter(f => f.endsWith(".md"));
      } catch {
        claimFiles = [];
      }

      const updates: { claim_id: string; claim_path: string; overlap: string[] }[] = [];

      for (const file of claimFiles) {
        const content = await import("node:fs/promises").then(fs =>
          fs.readFile(resolve(claimsDir, file), "utf-8")
        );

        // Check tag overlap via topics footer
        const topicsMatch = content.match(/<!-- topics: (.+?) -->/);
        if (!topicsMatch) continue;

        const claimTopics = topicsMatch[1].split(",").map(t => t.trim());
        const overlap = claimTopics.filter(t => runMeta.tags.includes(t));

        if (overlap.length >= 2) {
          updates.push({
            claim_id: file.replace(".md", ""),
            claim_path: resolve(claimsDir, file),
            overlap,
          });
        }
      }

      return updates;
    });

    // 4. Rebuild run index
    await step.run("rebuild-index", async () => {
      const result = await runScript("index-runs.py");
      if (result.exitCode !== 0) {
        throw new Error(`Index rebuild failed: ${result.stderr}`);
      }
    });

    // 5. Emit synthesis completed event
    await step.sendEvent("emit-synthesis-completed", {
      name: "vault/synthesis.completed",
      data: {
        trigger_event: "swarm/sweep.completed",
        trigger_run_id: run_id,
        notes_created: 1,
        claims_updated: claimUpdates.length,
        claims_created: 0,
        claims_weakened: 0,
        index_rebuilt: true,
      },
    });

    return {
      run_id,
      experiment_note: experimentNote,
      claims_checked: claimUpdates.length,
      claim_ids: claimUpdates.map(c => c.claim_id),
    };
  },
);
