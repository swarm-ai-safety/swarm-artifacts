---
description: Below 10-20% architectural minority fraction, governance effects are null; above it, governance effects become significant
type: prediction
status: open
source_claim: "theory-architecture-over-governance"
hypothesis: "If populations are composed of honest+adversarial agents with adversarial fraction swept 0-50%, there exists a critical minority fraction (estimated 10-20%) below which governance has no detectable effect (d<0.2 on all metrics) and above which governance effects are significant (d>0.5)"
test_protocol: "Sweep adversarial fraction at 0%, 5%, 10%, 15%, 20%, 25%, 50% with moderate governance on/off at each level. 20 seeds per cell (280 total runs). Baseline governance scenario, 8 agents, small-world. Measure governance effect size (d) at each adversarial fraction. Fit logistic curve to d vs adversarial fraction and locate the transition point."
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

# Population diversity threshold exists below which governance has null effect on all metrics

## Source

Derived from [[theory-architecture-over-governance]]. The theory argues that architectural homogeneity makes governance irrelevant because there is no differential selection pressure between agent types.

## Hypothesis

There exists a critical minority fraction of architecturally different agents — estimated at 10-20% based on the composition boundary study — below which governance has no detectable effect on any metric (welfare, toxicity, payoff) and above which governance effects become significant.

The mechanism: in near-homogeneous populations, all agents occupy similar behavioral attractors, so governance signals affect all agents equally and preserve relative standings. Once a sufficient minority of architecturally different agents is present, governance creates differential selection pressure that separates agent types.

Existing evidence: the composition boundary study ([[20260227_203024_composition_boundary_study]]) shows governance effects emerge between 0% and 25% adversarial, but the exact threshold is not characterized at fine resolution.

## Test protocol

- **Scenario:** Baseline governance, small-world topology (k=4, p=0.15), 8 agents
- **Adversarial fractions:** 0%, 5%, 10%, 15%, 20%, 25%, 50% (7 levels)
- **Governance:** moderate governance on/off at each level (2 x 7 = 14 cells)
- **Seeds:** 20 per cell (280 total runs)
- **Key metrics:** welfare, toxicity rate, mean honest payoff, mean adversarial payoff
- **Analysis:**
  1. Compute Cohen's d for governance effect (on vs off) at each adversarial fraction
  2. Fit logistic curve to d vs adversarial fraction
  3. Define threshold as the adversarial fraction where d crosses 0.5 (medium effect)
- **Statistical test:** Welch's t-test at each fraction, Bonferroni-corrected (k=7)
- **Power analysis:** N=20 seeds gives 80% power to detect d=0.8 at alpha=0.05/7

## Resolution

_Fill this section when the prediction is tested._

| Field | Value |
|-------|-------|
| Run | `` |
| Outcome | |
| Detail | |

## Implications

**If confirmed:** Provides a practical design rule: if population is expected to be >X% adversarial, deploy governance; below X%, governance is pure overhead. Connects [[theory-architecture-over-governance]] to [[theory-governance-cost-universality]] by identifying the regime boundary.

**If refuted:** Either governance always matters (even at 0% adversarial, contradicting the memori and mesa null results) or never matters (even at 50% adversarial, contradicting the collusion tax evidence). Either case would force revision of the architecture-over-governance theory.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: agent-behavior, architecture, governance, prediction -->
