---
description: Tax dominates economic outcomes while collusion penalty affects only toxicity — no cross-domain interaction detected
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: all
    detail: "Tax accounts for all 17 Bonferroni-sig economic findings; penalty accounts for 3 Bonferroni-sig toxicity findings. Zero cross-domain significance in 60 hypotheses tested"
  weakening:
  - run: 20260213-221500_collusion_tax_effect
    metric: toxicity_rate
    detail: "Formal 2-way ANOVA reveals MASSIVE tax x penalty interaction on toxicity: F=53.3, p<0.0001, partial eta2=0.413. Orthogonality holds for economics but NOT for toxicity. See claim-tax-penalty-interaction-on-toxicity-uncharacterized"
  boundary_conditions:
  - 4x4 factorial design (tax 0-10%, penalty 0.5-2.0x), 10 seeds per cell
  - 12 agents, default topology
  - "CRITICAL: Orthogonality is domain-specific — holds for economic outcomes (welfare, payoffs) but NOT for toxicity, where the interaction is super-additive (eta2=0.41)"
sensitivity:
  topology: untested beyond default
  agent_count: 12 agents; orthogonality may break with different population compositions
  governance_interaction: this IS the interaction claim — establishes that tax and penalty operate independently
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-collusion-penalty-destabilizes
- claim-collusion-penalty-has-no-economic-effect
- claim-tax-disproportionately-punishes-rlm-agents
- claim-high-tax-increases-toxicity
- claim-tax-penalty-interaction-on-toxicity-uncharacterized
- claim-governance-cost-paradox
- claim-quality-gate-dominates
created: 2026-02-20
updated: 2026-02-20
aliases:
- tax-and-penalty-effects-are-orthogonal
cssclasses:
- claim
- claim-medium
tags:
- governance
- transaction-tax
- collusion
- interaction
- factorial
graph-group: claim
---

# transaction tax and collusion penalty have orthogonal effects on ecosystem outcomes

## Evidence summary

The [[20260213-221500_collusion_tax_effect]] factorial sweep (4 tax rates x 4 penalty multipliers x 10 seeds = 160 runs) tested 60 hypotheses across 5 metrics. The results partition cleanly:

| Parameter | Economic effects (welfare, payoffs) | Safety effects (toxicity) | Quality gap |
|-----------|--------------------------------------|---------------------------|-------------|
| **Tax rate** | 17 Bonferroni-significant | 1 Bonferroni-significant (d=-0.86) | None |
| **Penalty multiplier** | 0 significant | 3 Bonferroni-significant (d≈-1.0) | None |

Tax rate explains all detected economic variance. Penalty multiplier explains all detected toxicity variance (excluding the smaller tax-toxicity effect). Neither parameter has significant effects in the other's primary domain. Quality gap shows no response to either parameter.

**Important boundary condition**: formal 2-way ANOVA ([[claim-tax-penalty-interaction-on-toxicity-uncharacterized]]) reveals that orthogonality **does not hold for toxicity**. The tax x penalty interaction on toxicity is super-additive (F=53.3, p<0.0001, eta2=0.41), meaning combined high tax + high penalty produces toxicity far exceeding the sum of individual effects. The orthogonality claim must be bounded to **economic outcomes only**.

For economics, governance designers can tune welfare (via tax) and detect collusion (via penalty) independently. The clean economic partition is grounded by [[claim-collusion-penalty-has-no-economic-effect]] and [[claim-tax-disproportionately-punishes-rlm-agents]]. But for toxicity, the super-additive interaction means governance designers cannot independently tune tax and penalty — their combined effect on toxicity is worse than the sum of parts. This is a critical governance design constraint: configurations that appear safe on each dimension individually may produce dangerous toxicity in combination.

## Mechanism

Tax operates on transaction economics — it extracts resources proportionally and reduces net payoffs. Penalty operates on behavioral detection — it identifies and punishes collusive patterns. These mechanisms target different aspects of agent behavior (economic vs strategic), explaining why their effects do not interact. This mechanistic separation validates the [[factorial-sweep]] design: because the parameters are orthogonal, main effects can be interpreted without conditioning on the other parameter's level. The orthogonality also implies that [[claim-quality-gate-dominates]] can be evaluated independently of collusion penalty settings.

## Boundary conditions

- Single factorial sweep; interaction terms not formally tested (only marginal effects)
- Raw data suggests possible super-additive toxicity at tax=10% + penalty=2.0x (>0.35 toxicity)
- Orthogonality may break at parameter ranges beyond those tested

## Open questions

- Does formal interaction analysis (2-way ANOVA) confirm orthogonality or reveal hidden interactions?
- Does orthogonality hold when adding a third governance parameter (circuit breakers, staking)?
- Is the clean partition an artifact of the limited parameter range, or a fundamental property of these mechanisms?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[transaction-tax-rate]]
- [[collusion-penalty-multiplier]]

<!-- topics: governance, transaction-tax, collusion, interaction, factorial -->
