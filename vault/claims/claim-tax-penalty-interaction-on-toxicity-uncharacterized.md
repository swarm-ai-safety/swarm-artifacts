---
description: Tax x penalty interaction on toxicity is super-additive (F=53.3, p<0.0001, eta2=0.41) — 41% of toxicity variance
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: toxicity_rate
    detail: "2-way ANOVA: tax x penalty interaction F=53.335, p<0.0001, partial eta2=0.413 (41% of toxicity variance). Tax main F=65.98 p<1e-26, penalty main F=113.47 p<1e-37. N=160, 10 seeds per cell, 4x4 factorial"
  weakening: []
  boundary_conditions:
  - 4x4 factorial design, 10 seeds per cell, 2-way ANOVA with Type II SS
  - Interaction explains more variance (eta2=0.41) than either main effect alone
sensitivity:
  topology: untested
  agent_count: untested
  governance_interaction: this IS the interaction question
supersedes: []
superseded_by: []
related_claims:
- claim-tax-and-penalty-effects-are-orthogonal
- claim-high-tax-increases-toxicity
- claim-collusion-penalty-destabilizes
- claim-collusion-penalty-has-no-economic-effect
- claim-tax-disproportionately-punishes-rlm-agents
- claim-welfare-non-normality-at-extreme-tax
- claim-governance-cost-paradox
created: 2026-02-20
updated: 2026-02-21
aliases:
- tax-penalty-interaction-on-toxicity-uncharacterized
cssclasses:
- claim
- claim-medium
tags:
- governance
- transaction-tax
- collusion
- interaction
- open-question
graph-group: claim
---

# tax and penalty interaction on toxicity is super-additive, explaining 41% of variance

## Evidence summary

Formal 2-way ANOVA on the [[20260213-221500_collusion_tax_effect]] sweep (160 runs, 4x4 factorial, 10 seeds/cell) reveals a massive tax x penalty interaction on toxicity: **F=53.3, p<0.0001, partial eta2=0.413**. The interaction explains more variance than either main effect alone (tax F=66.0, penalty F=113.5), confirming that combined high tax + high penalty produces toxicity far exceeding the sum of individual effects.

This directly contradicts [[claim-tax-and-penalty-effects-are-orthogonal]], which found zero cross-domain interaction in marginal analysis. The resolution: tax and penalty are orthogonal on **economic** outcomes (welfare, payoffs) but super-additive on **toxicity**. The orthogonality claim should be bounded to economics only.

The individual channels are well-established: [[claim-high-tax-increases-toxicity]] (d=-0.86 on toxicity) and [[claim-collusion-penalty-destabilizes]] (d=-1.12 on toxicity). The formal ANOVA shows their combination is worse than additive — a critical governance design constraint.

## Open questions

- Is the mechanism resource scarcity (from tax) amplifying behavioral distortion (from penalty)? [[claim-tax-disproportionately-punishes-rlm-agents]] suggests tax effects are agent-type-specific
- Does the interaction extend to welfare, or is it toxicity-specific? [[claim-collusion-penalty-has-no-economic-effect]] suggests no
- Is the interaction monotonic or does it plateau at extreme combinations?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[collusion-penalty-multiplier]]
- [[transaction-tax-rate]]

<!-- topics: governance, transaction-tax, collusion, interaction, open-question -->
