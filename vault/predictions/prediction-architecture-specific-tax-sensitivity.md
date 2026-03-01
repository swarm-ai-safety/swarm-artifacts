---
description: In mixed populations, tax effect sizes should differ by agent architecture — RLM > RLHF > LDT
type: prediction
status: open
source_claim: "theory-architecture-over-governance"
hypothesis: "If architecture determines governance sensitivity, then in a mixed population under uniform tax, RLM agents should show the largest payoff decline (d>1.0), RLHF agents intermediate (d=0.3-0.8), and LDT agents the smallest (d<0.3), measured as within-type payoff change from 0% to 10% tax"
test_protocol: "Run mixed population (equal thirds: RLM + RLHF + LDT) at 0% and 10% tax. 20 seeds per condition. Compare within-type payoff Cohen's d across architectures. One-way ANOVA on architecture x tax interaction."

resolution:
  run: ""
  outcome: ""
  detail: ""

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

# Tax governance creates architecture-specific effect sizes in mixed populations

## Source

Derived from [[theory-architecture-over-governance]]. The theory predicts that different architectures absorb governance signals differently, creating differential sensitivity in mixed populations.

## Hypothesis

In a mixed population containing equal proportions of RLM, RLHF, and LDT agents, a uniform 10% transaction tax should produce architecture-specific payoff effects:

1. **RLM agents: largest decline (d>1.0).** RLM agents already suffer from depth-dependent payoff decline ([[claim-smarter-agents-earn-less]]). Tax compounds this by reducing the already-thin margins from strategic depth. Partially supported: [[claim-tax-disproportionately-punishes-rlm-agents]] shows 2x payoff impact on RLM vs honest.

2. **RLHF agents: intermediate decline (d=0.3-0.8).** RLHF training creates robust cooperative attractors ([[claim-rlhf-persona-invariant]]) but does not protect against economic extraction. Tax reduces payoff but does not change behavior.

3. **LDT agents: smallest decline (d<0.3).** LDT cooperation outcomes are insensitive to parameter variation ([[claim-acausality-depth-does-not-affect-cooperation-outcomes]]). If this extends to economic parameters, LDT agents should be least affected by tax.

The critical test is the architecture x tax interaction: if architecture moderates tax sensitivity, the interaction term should be significant (F>4, p<0.05).

## Test protocol

- **Scenario:** Baseline governance, small-world topology (k=4, p=0.15), 9 agents (3 each: RLM, RLHF, LDT)
- **Tax rates:** 0%, 10%
- **Seeds:** 20 per condition (40 total runs)
- **Key metrics:** per-agent-type mean payoff, within-type payoff Cohen's d (0% vs 10% tax)
- **Statistical test:**
  1. 2-way ANOVA: architecture (3 levels) x tax (2 levels) on payoff
  2. Bonferroni-corrected pairwise comparisons of within-type tax effects
- **Power analysis:** N=20 seeds x 3 agents per type = 60 observations per cell, >80% power for d=0.5

## Resolution

_Fill this section when the prediction is tested._

| Field | Value |
|-------|-------|
| Run | `` |
| Outcome | |
| Detail | |

## Implications

**If confirmed:** Validates the theory that architecture modulates governance sensitivity. Opens a design space for architecture-targeted governance — mechanisms calibrated to the agent types expected in the population.

**If refuted (all architectures equally affected):** Architecture determines baseline behavior but not governance response. The homogeneous-population null effect is about lack of adversarial pressure, not architectural insulation. The theory's mechanism section would need revision.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: agent-behavior, architecture, governance, transaction-tax, prediction -->
