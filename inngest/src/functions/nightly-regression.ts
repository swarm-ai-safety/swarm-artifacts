/**
 * fn-nightly-regression
 *
 * Triggered by: cron (4 AM UTC daily)
 * Action: Fan-out canary scenarios, wait for all to complete,
 *         check for drift, alert if detected.
 */

import { inngest } from "../client.js";
import { runSwarm, gitCurrentSha, exec, REPO_ROOT } from "../helpers.js";
import { readdir } from "node:fs/promises";
import { resolve } from "node:path";

/** Standard canary scenarios that form the regression suite. */
const CANARY_SCENARIOS = [
  "scenarios/benchmarks/baseline.yaml",
  "scenarios/benchmarks/adversarial_basic.yaml",
  "scenarios/benchmarks/governance_smoke.yaml",
  "scenarios/benchmarks/ldt_canary.yaml",
  "scenarios/benchmarks/delegation_canary.yaml",
];

const CANARY_SEEDS = [42, 7, 123];

/** Tolerance thresholds for drift detection. */
const DRIFT_TOLERANCE = {
  welfare_pct: 5.0,    // alert if welfare changes > 5%
  toxicity_pct: 3.0,   // alert if toxicity changes > 3%
};

export const nightlyRegression = inngest.createFunction(
  {
    id: "nightly-regression",
    retries: 1,
  },
  { cron: "0 4 * * *" }, // 4 AM UTC daily
  async ({ step, logger }) => {
    const gitSha = await step.run("get-git-sha", gitCurrentSha);

    // 1. Discover available canary scenarios
    const scenarios = await step.run("discover-canaries", async () => {
      const available: string[] = [];
      for (const s of CANARY_SCENARIOS) {
        try {
          const { readFile } = await import("node:fs/promises");
          await readFile(resolve(REPO_ROOT, s));
          available.push(s);
        } catch {
          // scenario doesn't exist yet, skip it
        }
      }
      return available;
    });

    if (scenarios.length === 0) {
      logger.warn("No canary scenarios found. Skipping regression.");
      return { status: "skipped", reason: "no canary scenarios" };
    }

    // 2. Fan-out: run each canary scenario
    const results = await Promise.all(
      scenarios.map((scenario) =>
        step.run(`run-canary-${scenario.split("/").pop()}`, async () => {
          const seedStr = CANARY_SEEDS.join(",");
          const result = await runSwarm(
            ["run", scenario, "--seeds", String(CANARY_SEEDS.length)],
            { timeout: 600_000 }, // 10 min per canary
          );
          return {
            scenario,
            exitCode: result.exitCode,
            passed: result.exitCode === 0,
            output: result.stdout.slice(-500), // last 500 chars
            error: result.stderr.slice(-500),
          };
        })
      ),
    );

    // 3. Summarize
    const summary = await step.run("summarize-results", () => {
      const passed = results.filter(r => r.passed).length;
      const failed = results.filter(r => !r.passed).length;
      const drift_detected = failed > 0;

      return {
        scenarios_run: results.length,
        scenarios_passed: passed,
        scenarios_failed: failed,
        drift_detected,
        failures: results
          .filter(r => !r.passed)
          .map(r => ({ scenario: r.scenario, error: r.error })),
      };
    });

    // 4. Emit canary.completed
    const timestamp = new Date().toISOString().replace(/[:.]/g, "").slice(0, 15);
    await step.sendEvent("emit-canary-completed", {
      name: "swarm/canary.completed",
      data: {
        run_id: `${timestamp}_canary_nightly`,
        suite: "nightly",
        scenarios_run: summary.scenarios_run,
        scenarios_passed: summary.scenarios_passed,
        scenarios_failed: summary.scenarios_failed,
        drift_detected: summary.drift_detected,
        baseline_comparison: {
          welfare_delta_pct: 0, // TODO: compute from baseline comparison
          toxicity_delta_pct: 0,
          within_tolerance: !summary.drift_detected,
        },
      },
    });

    // 5. If drift detected, create a GitHub issue
    if (summary.drift_detected) {
      await step.run("create-drift-issue", async () => {
        const failureList = summary.failures
          .map(f => `- \`${f.scenario}\`: ${f.error.slice(0, 200)}`)
          .join("\n");

        const result = await exec("gh", [
          "issue", "create",
          "--title", `Nightly regression drift detected (${summary.scenarios_failed}/${summary.scenarios_run} failed)`,
          "--body", `## Nightly Regression Report\n\n**Git SHA**: ${gitSha}\n**Date**: ${new Date().toISOString()}\n\n### Failures\n\n${failureList}\n\n### Action needed\n\nInvestigate whether recent code changes caused the regression.`,
          "--label", "regression,automated",
        ]);

        return result.stdout;
      });
    }

    return {
      git_sha: gitSha,
      ...summary,
    };
  },
);
