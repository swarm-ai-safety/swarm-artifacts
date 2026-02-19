/**
 * fn-synthesize-redteam
 *
 * Triggered by: swarm/redteam.completed
 * Action: Generate vulnerability notes, update governance pages in vault.
 */

import { inngest } from "../client.js";
import { writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import { RUNS_DIR, VAULT_DIR, readJson, runScript } from "../helpers.js";

interface RedteamReport {
  robustness_score: number;
  grade: string;
  attacks_tested: number;
  attacks_successful: number;
  attacks_prevented: number;
  vulnerabilities: {
    vulnerability_id: string;
    severity: string;
    description: string;
    attack_vector: string;
    affected_lever: string;
    mitigation: string;
    potential_damage: number;
  }[];
}

export const synthesizeRedteam = inngest.createFunction(
  {
    id: "synthesize-redteam",
    retries: 3,
  },
  { event: "swarm/redteam.completed" },
  async ({ event, step, logger }) => {
    const { run_id, grade, robustness_score, critical_vulnerabilities } = event.data;
    const runDir = resolve(RUNS_DIR, run_id);

    // 1. Read report
    const report = await step.run("read-report", async () => {
      return readJson<RedteamReport>(resolve(runDir, event.data.report_path));
    });

    // 2. Generate failure pattern notes for critical/high vulnerabilities
    const notesCreated = await step.run("generate-failure-notes", async () => {
      const critical = report.vulnerabilities.filter(
        v => v.severity === "critical" || v.severity === "high"
      );

      let count = 0;
      for (const vuln of critical) {
        const note = `---
description: "${vuln.description}"
type: failure
status: active
severity: ${vuln.severity}
attack_vector: ${vuln.attack_vector}
affected_lever: ${vuln.affected_lever}
source_run: "${run_id}"
created: ${new Date().toISOString().slice(0, 10)}
---

## ${vuln.vulnerability_id}

${vuln.description}

- **Severity**: ${vuln.severity}
- **Attack vector**: ${vuln.attack_vector}
- **Affected lever**: ${vuln.affected_lever}
- **Potential damage**: ${vuln.potential_damage}
- **Exploitation difficulty**: moderate

## Mitigation

${vuln.mitigation}

## Source

Run: \`${run_id}\`
Report: \`${event.data.report_path}\`

<!-- topics: failure, ${vuln.attack_vector}, ${vuln.affected_lever}, redteam -->
`;

        const notePath = resolve(VAULT_DIR, "failures", `${vuln.vulnerability_id}.md`);
        await writeFile(notePath, note, "utf-8");
        count++;
      }
      return count;
    });

    // 3. Generate experiment note
    await step.run("generate-experiment-note", async () => {
      const note = `---
description: "Red-team evaluation: grade ${grade}, score ${robustness_score.toFixed(2)}, ${critical_vulnerabilities} critical vulns"
type: experiment
status: completed
run_id: "${run_id}"
experiment_type: redteam
created: ${new Date().toISOString().slice(0, 10)}
---

## Results

- **Grade**: ${grade}
- **Robustness score**: ${robustness_score.toFixed(2)}
- **Attacks tested**: ${report.attacks_tested}
- **Attacks successful**: ${report.attacks_successful}
- **Attacks prevented**: ${report.attacks_prevented}

## Vulnerabilities found

${report.vulnerabilities.map(v =>
  `- **${v.severity}**: ${v.description} (${v.affected_lever}, damage=${v.potential_damage})`
).join("\n")}

## Artifacts

- Report: \`runs/${run_id}/${event.data.report_path}\`

<!-- topics: redteam, governance, security -->
`;

      const notePath = resolve(VAULT_DIR, "experiments", `${run_id}.md`);
      await writeFile(notePath, note, "utf-8");
    });

    // 4. Rebuild index
    await step.run("rebuild-index", async () => {
      await runScript("index-runs.py");
    });

    // 5. Emit synthesis completed
    await step.sendEvent("emit-synthesis-completed", {
      name: "vault/synthesis.completed",
      data: {
        trigger_event: "swarm/redteam.completed",
        trigger_run_id: run_id,
        notes_created: notesCreated + 1,
        claims_updated: 0,
        claims_created: 0,
        claims_weakened: 0,
        index_rebuilt: true,
      },
    });

    return { run_id, grade, failure_notes_created: notesCreated };
  },
);
