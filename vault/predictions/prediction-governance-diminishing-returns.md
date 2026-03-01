---
description: Welfare cost vs governance intensity should show convex curve with inflection near moderate governance level
type: prediction
status: open
source_claim: "theory-governance-cost-universality"
hypothesis: "If governance intensity is defined as (number of active mechanisms x mean parameter strength) and plotted against welfare cost, the curve will be convex with an inflection point near moderate governance, beyond which marginal cost per unit safety gain accelerates"
test_protocol: "Systematically vary governance intensity from 0 (ungoverned) through individual mechanisms to full stack. 5+ intensity levels, 20 seeds each, baseline governance scenario. Plot welfare cost (ungoverned minus governed welfare) vs safety gain (ungoverned minus governed toxicity). Fit convex curve and locate inflection point."
created: 2026-02-28

_schema:
  required: [description, type, status, source_claim, hypothesis, created]
  optional: [test_protocol, resolution, updated]
  enums:
    type: [prediction]
    status: [open, confirmed, refuted, expired]
    outcome: [confirmed, refuted, inconclusive]
  constraints:
    description: "max 200 chars, no trailing period"
    hypothesis: "must be a precise if-then statement"
    source_claim: "must reference a valid claim or theory ID"
---

# Marginal welfare cost per unit safety gain accelerates beyond moderate governance intensity

## Source

Derived from [[theory-governance-cost-universality]]. The theory synthesizes 6 claims showing that full governance stacks impose costs exceeding safety benefits, while moderate governance Pareto-dominates.

## Hypothesis

If governance intensity is measured as a composite index (number of active mechanisms x mean parameter strength, normalized 0-1), the welfare-safety tradeoff curve should be convex:

- **Low intensity (0-0.3):** each unit of governance buys meaningful safety at modest welfare cost
- **Moderate intensity (0.3-0.5):** welfare cost rises but safety gains continue; optimal operating point
- **High intensity (0.5-1.0):** welfare cost per unit safety gain accelerates sharply; marginal safety gains approach zero while costs continue compounding

The inflection point — where marginal returns turn negative — should occur near the "moderate governance" configuration that Pareto-dominates in existing experiments ([[claim-moderate-governance-pareto-dominates-welfare-toxicity-frontier]]).

## Test protocol

- **Scenario:** Baseline governance, small-world topology (k=4, p=0.15), 8 agents
- **Governance levels (6 points minimum):**
  1. Ungoverned (intensity 0)
  2. Quality gate only (~0.15)
  3. CB + audit (~0.30)
  4. Moderate: CB + audit + 5% tax (~0.45)
  5. Full: all mechanisms at default (~0.70)
  6. Full aggressive: all mechanisms at max (~1.0)
- **Seeds:** 20 per configuration (120 total runs)
- **Adversarial fractions:** 0%, 25%, 50% (test whether inflection shifts with adversarial pressure)
- **Metrics:** welfare (mean agent wealth), toxicity rate, safety score (1 - toxicity)
- **Analysis:** Plot welfare cost (ungoverned welfare minus governed welfare) vs safety gain. Fit quadratic and exponential models. Identify inflection via second derivative.
- **Statistical test:** Pairwise Welch's t-test between adjacent intensity levels, Bonferroni-corrected

## Resolution

_Fill this section when the prediction is tested._

| Field | Value |
|-------|-------|
| Run | `` |
| Outcome | |
| Detail | |

## Implications

**If confirmed:** Provides a quantitative governance design tool — the inflection point defines the optimal governance intensity. Practitioners can calibrate to the curve rather than sweeping parameters.

**If refuted:** The welfare-safety tradeoff is linear or concave, meaning more governance always helps (at constant or decreasing marginal cost). This would weaken the entire governance cost universality theory.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, welfare, cost-benefit, prediction -->
