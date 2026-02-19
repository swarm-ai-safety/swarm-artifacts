/**
 * fn-retry-run
 *
 * Triggered by: swarm/run.failed
 * Action: Retry with the same seeds, up to 3 attempts.
 *         Uses exponential backoff between retries.
 */

import { NonRetriableError } from "inngest";
import { inngest } from "../client.js";
import { runSwarm, readYaml, RUNS_DIR } from "../helpers.js";
import { resolve } from "node:path";

const MAX_RETRIES = 3;

export const retryRun = inngest.createFunction(
  {
    id: "retry-run",
    retries: 0, // We handle retries ourselves via event re-emission
  },
  { event: "swarm/run.failed" },
  async ({ event, step, logger }) => {
    const { run_id, error, experiment_type, last_seed } = event.data;

    // 1. Determine retry count from run history
    const retryAttempt = await step.run("check-retry-count", async () => {
      // Look for retry markers in run.yaml
      const runYamlPath = resolve(RUNS_DIR, run_id, "run.yaml");
      try {
        const meta = await readYaml<{ _retry_attempt?: number }>(runYamlPath);
        return (meta._retry_attempt ?? 0) + 1;
      } catch {
        return 1;
      }
    });

    if (retryAttempt > MAX_RETRIES) {
      logger.error(`Run ${run_id} exhausted ${MAX_RETRIES} retries. Giving up.`);
      throw new NonRetriableError(
        `Run ${run_id} failed after ${MAX_RETRIES} retries: ${error}`
      );
    }

    // 2. Compute backoff delay
    const delaySec = Math.min(60 * Math.pow(2, retryAttempt - 1), 600);
    logger.info(`Retry ${retryAttempt}/${MAX_RETRIES} for ${run_id} after ${delaySec}s`);

    await step.sleep("backoff-wait", `${delaySec}s`);

    // 3. Read original scenario to re-run with same config
    const scenario = await step.run("read-scenario", async () => {
      const runYamlPath = resolve(RUNS_DIR, run_id, "run.yaml");
      try {
        const meta = await readYaml<{ experiment: { scenario_ref: string; seeds: number[] } }>(
          runYamlPath
        );
        return {
          scenario_ref: meta.experiment.scenario_ref,
          seeds: meta.experiment.seeds,
        };
      } catch {
        return null;
      }
    });

    if (!scenario || scenario.scenario_ref === "unknown") {
      throw new NonRetriableError(
        `Cannot retry ${run_id}: no scenario_ref in run.yaml`
      );
    }

    // 4. Re-run the experiment
    const result = await step.run("rerun-experiment", async () => {
      const seedArgs = scenario.seeds.length === 1
        ? ["--seed", String(scenario.seeds[0])]
        : ["--seeds", String(scenario.seeds.length)];

      const cmdArgs = experiment_type === "sweep"
        ? ["sweep", scenario.scenario_ref, ...seedArgs]
        : ["run", scenario.scenario_ref, ...seedArgs];

      return runSwarm(cmdArgs, { timeout: 1_800_000 }); // 30 min timeout
    });

    if (result.exitCode !== 0) {
      // Emit another failed event to trigger the next retry
      await step.sendEvent("emit-retry-failure", {
        name: "swarm/run.failed",
        data: {
          run_id,
          experiment_type,
          status: "failed",
          error: result.stderr.slice(0, 500),
          run_yaml_path: event.data.run_yaml_path,
        },
      });

      return { run_id, retry_attempt: retryAttempt, status: "failed_again" };
    }

    return { run_id, retry_attempt: retryAttempt, status: "recovered" };
  },
);
