/**
 * fn-validate-run
 *
 * Triggered by: swarm/run.completed
 * Action: Validate run.yaml against schemas, report violations.
 */

import { inngest } from "../client.js";
import { RUNS_DIR, runScript, fileExists } from "../helpers.js";
import { resolve } from "node:path";

export const validateRun = inngest.createFunction(
  {
    id: "validate-run",
    retries: 2,
  },
  { event: "swarm/run.completed" },
  async ({ event, step, logger }) => {
    const { run_id } = event.data;
    const runDir = resolve(RUNS_DIR, run_id);

    // 1. Check run.yaml exists
    const hasRunYaml = await step.run("check-run-yaml", async () => {
      return fileExists(resolve(runDir, "run.yaml"));
    });

    if (!hasRunYaml) {
      logger.warn(`run.yaml missing for ${run_id}, generating via backfill`);
      await step.run("backfill-run-yaml", async () => {
        const result = await runScript("backfill-run-yaml.py", ["--run-id", run_id]);
        if (result.exitCode !== 0) {
          throw new Error(`Backfill failed: ${result.stderr}`);
        }
        return result.stdout;
      });
    }

    // 2. Validate against schemas
    const validation = await step.run("validate-schemas", async () => {
      const result = await runScript("validate-run.py", [runDir]);
      return {
        exitCode: result.exitCode,
        output: result.stdout + result.stderr,
        passed: result.exitCode === 0,
      };
    });

    // 3. Rebuild index
    await step.run("rebuild-index", async () => {
      const result = await runScript("index-runs.py");
      if (result.exitCode !== 0) {
        throw new Error(`Index rebuild failed: ${result.stderr}`);
      }
      return result.stdout;
    });

    return {
      run_id,
      validated: validation.passed,
      details: validation.output,
    };
  },
);
