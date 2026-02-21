---
description: Tax x CB interaction on quality gap is marginal (ANOVA F=2.065, p=0.055, eta2=0.018) — not significant after formal testing
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260213-202050_baseline_governance_v2
    metric: quality_gap
    detail: "Council review noted quality_gap effect size range=0.77 across conditions. CB main effect on welfare d=0.008 (null)"
  - run: 20260213-202050_baseline_governance_v2
    metric: multiple
    detail: "Council review flagged tax x CB interactions on 5 metrics: toxicity_rate, quality_gap, honest_payoff, opportunistic_payoff, deceptive_payoff"
  weakening:
  - run: 20260213-202050_baseline_governance_v2
    metric: quality_gap
    detail: "Formal 2-way ANOVA (Type II SS): tax x CB interaction on quality_gap F=2.065, p=0.055, partial eta2=0.018. Marginal — does NOT reach significance at alpha=0.05. N=700, 7 tax x 2 CB x 50 seeds"
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
- claim-welfare-plateaus-above-12pct-tax
- claim-tax-hurts-honest-more-than-opportunistic
- claim-high-tax-increases-toxicity
- claim-governance-cost-paradox
created: 2026-02-20
updated: 2026-02-20
aliases:
- tax-cb-interact-on-quality-gap
cssclasses:
- claim
- claim-low
tags:
- governance
- transaction-tax
- circuit-breaker
- interaction
graph-group: claim
---

# transaction tax and circuit breaker interact significantly on quality gap but not on welfare

## Evidence summary

In the [[20260213-202050_baseline_governance_v2]] sweep (700 runs, 7 tax levels x 2 CB levels x 50 seeds), circuit breakers show zero main effect on welfare (d=0.008, p=0.92). The council review identified potential tax x CB interactions on 5 metrics including quality_gap (effect size range=0.77 across conditions).

**However**, formal 2-way ANOVA (Type II SS) on quality_gap yields F=2.065, p=0.055, partial eta2=0.018 — **marginal but not significant** at alpha=0.05. The interaction explains only 1.8% of quality_gap variance. This weakens the original council review assessment: the tax x CB interaction on quality gap is suggestive but not statistically confirmed.

This partially validates [[claim-tax-dominates-cb-kernel]]: not only does CB have null main effect on welfare, but the CB interaction with tax on quality gap is also not significant. The pattern weakly parallels [[claim-tax-and-penalty-effects-are-orthogonal]], which found orthogonality on economics (though super-additive interaction on toxicity per [[claim-tax-penalty-interaction-on-toxicity-uncharacterized]]).

## Mechanism

Circuit breakers freeze high-toxicity agents, removing them from the transaction pool. At low tax rates, this has minimal impact because the ecosystem is healthy. At high tax rates, removing agents from an already-stressed ecosystem has outsized effects on the quality of remaining interactions — fewer agents means less competition for remaining opportunities, changing the quality gap.

The agent-type payoff interactions (honest, opportunistic, deceptive) channel through [[claim-tax-hurts-honest-more-than-opportunistic]]: because honest agents bear disproportionate tax burden, CB-induced agent removal at high tax rates shifts the remaining population composition, amplifying quality gap effects. This also connects to [[claim-high-tax-increases-toxicity]] — the quality gap interaction may be the distributional mechanism through which tax increases toxicity, as CB modulates which agents remain active in a toxicity-stressed ecosystem.

The interaction complicates [[claim-governance-cost-paradox]]: governance cost-benefit analysis assuming independent mechanism effects underestimates the true cost when interaction terms are non-zero.

## Boundary conditions

- CB tested as binary on/off; the interaction may be threshold-dependent
- Interaction identified in review but formal ANOVA with interaction term not reported
- Quality gap is a derived metric; interaction may not reflect a fundamental mechanism

## Open questions

- Run formal 2-way ANOVA with interaction term to quantify the tax x CB interaction
- Does the interaction persist when CB threshold is varied (not just on/off)?
- Is quality gap the primary interaction channel, or are agent-type payoffs more fundamental?
- How does this relate to the tax x penalty interaction explored in [[claim-tax-penalty-interaction-on-toxicity-uncharacterized]]?
- Does the interaction change character in the [[claim-welfare-plateaus-above-12pct-tax]] plateau regime, where the ecosystem is already at minimum viable state?
- [[failure-threshold-dancing]] shows adversaries can learn CB thresholds — does the interaction disappear if adversaries successfully evade CB, leaving only the tax main effect?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[transaction-tax-rate]]

<!-- topics: governance, transaction-tax, circuit-breaker, interaction -->
