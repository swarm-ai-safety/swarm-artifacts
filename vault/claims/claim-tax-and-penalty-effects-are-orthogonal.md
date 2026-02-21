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
  weakening: []
  boundary_conditions:
  - 4x4 factorial design (tax 0-10%, penalty 0.5-2.0x), 10 seeds per cell
  - 12 agents, default topology
  - Single run; interaction may emerge at extreme parameter combinations
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

This orthogonality means governance designers can tune economic outcomes (via tax) and safety outcomes (via penalty) independently — but given that both mechanisms produce negative side effects at high levels ([[claim-tax-welfare-tradeoff]], [[claim-collusion-penalty-destabilizes]]), the optimal configuration may be low values of both. The clean partition is grounded by [[claim-collusion-penalty-has-no-economic-effect]], which establishes the penalty's economic null result, and by [[claim-tax-disproportionately-punishes-rlm-agents]], which shows tax's economic effects are agent-type-specific but purely economic. However, [[claim-tax-penalty-interaction-on-toxicity-uncharacterized]] raises a tension: the orthogonality may break at extreme parameter combinations where tax-induced and penalty-induced toxicity compound super-additively.

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
