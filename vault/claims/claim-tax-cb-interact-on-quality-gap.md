---
description: Tax and circuit breaker interact significantly on quality gap (range=0.77) but not on welfare (CB d=0.008)
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260213-202050_baseline_governance_v2
    metric: quality_gap
    detail: "Tax x CB interaction: quality_gap effect size range=0.77 across conditions. CB main effect on welfare d=0.008 (null)"
  - run: 20260213-202050_baseline_governance_v2
    metric: multiple
    detail: "Significant tax x CB interactions on 5 metrics: toxicity_rate, quality_gap, honest_payoff, opportunistic_payoff, deceptive_payoff"
  weakening: []
  boundary_conditions:
  - 8 agents, small-world topology, 7 tax levels x 2 CB levels, 50 seeds
  - CB tested as binary on/off only; threshold variation not explored
  - Interaction detected in council review but formal 2-way ANOVA not reported
sensitivity:
  topology: small-world k=4 p=0.15; interaction may differ under other topologies
  agent_count: 8 agents; interaction may strengthen with more agents
  governance_interaction: this IS the interaction finding
supersedes: []
superseded_by: []
related_claims:
- claim-tax-dominates-cb-kernel
- claim-circuit-breakers-dominate
- claim-tax-and-penalty-effects-are-orthogonal
- claim-cb-null-may-reflect-design-limitation
created: 2026-02-20
updated: 2026-02-20
aliases:
- tax-cb-interact-on-quality-gap
cssclasses:
- claim
- claim-medium
tags:
- governance
- transaction-tax
- circuit-breaker
- interaction
graph-group: claim
---

# transaction tax and circuit breaker interact significantly on quality gap but not on welfare

## Evidence summary

In the [[20260213-202050_baseline_governance_v2]] sweep (700 runs, 7 tax levels x 2 CB levels x 50 seeds), circuit breakers show zero main effect on welfare (d=0.008, p=0.92). However, the council review identifies significant tax x CB interactions on 5 metrics: toxicity_rate, quality_gap, honest_payoff, opportunistic_payoff, and deceptive_payoff. Quality gap shows the strongest interaction (effect size range=0.77 across conditions).

This complicates [[claim-tax-dominates-cb-kernel]], which treats tax and CB as having independent effects. While CB has no main effect on welfare, it modulates how tax affects quality and agent-type-specific payoffs. The interaction pattern parallels [[claim-tax-and-penalty-effects-are-orthogonal]] — governance mechanisms appear orthogonal on aggregate welfare but interact on distributional and quality metrics.

## Mechanism

Circuit breakers freeze high-toxicity agents, removing them from the transaction pool. At low tax rates, this has minimal impact because the ecosystem is healthy. At high tax rates, removing agents from an already-stressed ecosystem has outsized effects on the quality of remaining interactions — fewer agents means less competition for remaining opportunities, changing the quality gap.

## Boundary conditions

- CB tested as binary on/off; the interaction may be threshold-dependent
- Interaction identified in review but formal ANOVA with interaction term not reported
- Quality gap is a derived metric; interaction may not reflect a fundamental mechanism

## Open questions

- Run formal 2-way ANOVA with interaction term to quantify the tax x CB interaction
- Does the interaction persist when CB threshold is varied (not just on/off)?
- Is quality gap the primary interaction channel, or are agent-type payoffs more fundamental?
- How does this relate to the tax x penalty interaction explored in [[claim-tax-penalty-interaction-on-toxicity-uncharacterized]]?

---

Topics:
- [[_index]]

<!-- topics: governance, transaction-tax, circuit-breaker, interaction -->
