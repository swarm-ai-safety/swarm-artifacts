/**
 * fn-post-merge
 *
 * Triggered by: github/pr.merged
 * Action: If the merged PR contains a new scenario, trigger the
 *         benchmark suite against it.
 */

import { inngest } from "../client.js";
import { runSwarm, gitCurrentSha } from "../helpers.js";

export const postMerge = inngest.createFunction(
  {
    id: "post-merge",
    retries: 1,
  },
  {
    event: "github/pr.merged",
    if: "event.data.contains_new_scenario == true",
  },
  async ({ event, step, logger }) => {
    const { pr_number, merge_sha, files_changed } = event.data;

    // 1. Find the new scenario files
    const newScenarios = await step.run("find-new-scenarios", () => {
      return files_changed.filter(
        f => f.startsWith("scenarios/") && f.endsWith(".yaml")
      );
    });

    if (newScenarios.length === 0) {
      logger.info("No new scenarios in merged PR, skipping");
      return { status: "skipped" };
    }

    logger.info(`PR #${pr_number} merged with ${newScenarios.length} new scenarios`);

    // 2. Run each new scenario with the standard seed set
    const results = await Promise.all(
      newScenarios.map((scenario) =>
        step.run(`benchmark-${scenario.split("/").pop()}`, async () => {
          const result = await runSwarm(
            ["run", scenario, "--seed", "42", "--epochs", "10", "--steps", "10"],
            { timeout: 600_000 },
          );
          return {
            scenario,
            passed: result.exitCode === 0,
            output: result.stdout.slice(-300),
          };
        })
      ),
    );

    // 3. If any failed, comment on the PR
    const failures = results.filter(r => !r.passed);
    if (failures.length > 0) {
      await step.run("comment-on-pr", async () => {
        const { exec: execHelper } = await import("../helpers.js");
        const body = `## Post-merge benchmark results\n\n${failures.length} scenario(s) failed:\n\n${failures.map(f => `- \`${f.scenario}\``).join("\n")}`;
        await execHelper("gh", [
          "pr", "comment", String(pr_number),
          "--body", body,
        ]);
      });
    }

    return {
      pr_number,
      scenarios_tested: results.length,
      scenarios_passed: results.filter(r => r.passed).length,
      scenarios_failed: failures.length,
    };
  },
);
