/**
 * fn-check-drift
 *
 * Triggered by: swarm/canary.completed
 * Action: Compare canary results against stored baselines,
 *         alert if drift exceeds tolerance.
 */

import { inngest } from "../client.js";

export const checkDrift = inngest.createFunction(
  {
    id: "check-drift",
    retries: 1,
  },
  { event: "swarm/canary.completed" },
  async ({ event, step, logger }) => {
    const {
      run_id,
      suite,
      scenarios_passed,
      scenarios_failed,
      drift_detected,
      baseline_comparison,
    } = event.data;

    if (!drift_detected && baseline_comparison.within_tolerance) {
      logger.info(`Canary ${run_id}: all clear, ${scenarios_passed} passed`);
      return { status: "ok", run_id };
    }

    // Drift was detected — the nightly-regression function already
    // creates a GitHub issue, so here we just log the structured alert
    // and could emit to Slack/PagerDuty/etc.
    const alert = await step.run("generate-alert", () => {
      return {
        severity: scenarios_failed > 2 ? "critical" : "warning",
        message: `Regression detected in ${suite} suite: ${scenarios_failed}/${scenarios_passed + scenarios_failed} canaries failed`,
        welfare_delta_pct: baseline_comparison.welfare_delta_pct,
        toxicity_delta_pct: baseline_comparison.toxicity_delta_pct,
      };
    });

    logger.error(`DRIFT ALERT: ${alert.message}`);

    return { status: "drift", run_id, alert };
  },
);
