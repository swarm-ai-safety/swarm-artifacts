---
description: Collusion penalty multiplier above 1.5x increases toxicity (d=-1.12, p<0.0001) with no welfare benefit
type: claim
status: active
confidence: medium
domain: collusion
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: toxicity
    detail: "2.0x penalty toxicity 0.342 vs 0.334 at 0.5x, d=-1.12, p=1.1e-05, Bonferroni-significant across 60 hypotheses. N=160, 10 seeds per config"
  weakening: []
  boundary_conditions:
  - 12 RLM agents at depths 1/3/5, 30 epochs, collusion detection enabled
sensitivity:
  topology: Tested on default topology; penalty effects may differ under ring or complete graphs where collusion channels
    are structurally constrained
  agent_count: 12 agents; penalty calibration may need adjustment for larger populations with more potential collusion pairs
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-rlhf-persona-invariant
- claim-collusion-penalty-has-no-economic-effect
- claim-tax-and-penalty-effects-are-orthogonal
- claim-high-tax-increases-toxicity
- claim-tax-penalty-interaction-on-toxicity-uncharacterized
- claim-welfare-non-normality-at-extreme-tax
- claim-captcha-difficulty-and-collusion-penalty-have-no-governance-effect
created: 2026-02-19
updated: 2026-02-21
aliases:
- collusion-penalty-destabilizes
- collusion-penalty-multiplier-above-15x-increases
cssclasses:
- claim
- claim-medium
tags:
- governance
- collusion
- penalty
- toxicity
graph-group: claim
---

# collusion penalty multiplier above 1.5x increases toxicity with no welfare benefit

Collusion penalty multipliers above 1.5x paradoxically increase toxicity with no compensating welfare benefit. At a 2.0x multiplier, mean toxicity rises to 0.342 compared to 0.334 at 0.5x (d = -1.12, p < 0.0001).

**Evidence summary.** In a study of 160 runs with 12 RLM agents at reasoning depths 1, 3, and 5, collusion penalties were swept from 0.5x to 2.0x. Below 1.5x, the penalty had a modest deterrent effect. Above 1.5x, the penalty induced behavioral distortions: agents shifted toward individually toxic but non-collusive strategies to avoid the penalty, producing a net increase in ecosystem toxicity. Welfare showed no statistically significant improvement at any penalty level.

**Boundary conditions.** The result is established for 12 agents with heterogeneous reasoning depths and collusion detection enabled. The penalty mechanism assumes accurate collusion detection; if detection has false positives, the destabilization effect may be amplified. The 30-epoch horizon may not capture long-run adaptation where agents learn to avoid the penalty without increasing toxicity.

**Open questions.**
- Is there an optimal penalty multiplier in the 1.0–1.5x range that reduces collusion without destabilizing?
- Does the destabilization effect depend on the collusion detection accuracy?
- How does reasoning depth interact with penalty sensitivity?

<!-- topics: governance, collusion, penalty, toxicity -->
