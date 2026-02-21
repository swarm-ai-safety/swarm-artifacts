---
description: Collusion penalty multiplier (0.5-2.0x) has no significant effect on welfare, honest payoff, or RLM payoff
type: claim
status: active
confidence: medium
domain: collusion
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: welfare
    detail: "24 pairwise comparisons on welfare/honest_payoff/rlm_payoff/quality_gap: none reach BH significance. Largest d=0.34, p=0.13"
  weakening: []
  boundary_conditions:
  - 12 agents, default topology, penalty range 0.5-2.0x, 10 seeds per cell
  - Collusion detection enabled throughout
  - Tax rate varying simultaneously (0-10%) but effects are orthogonal
sensitivity:
  topology: untested beyond default; penalty may matter more in topologies that facilitate collusion (ring, complete)
  agent_count: 12 agents; larger populations with more collusion pairs may show economic effects
  governance_interaction: tax dominates economic outcomes; penalty only affects toxicity
supersedes: []
superseded_by: []
related_claims:
- claim-collusion-penalty-destabilizes
- claim-tax-and-penalty-effects-are-orthogonal
- claim-governance-cost-paradox
- claim-collusion-wealth-destruction
- claim-tax-penalty-interaction-on-toxicity-uncharacterized
- claim-high-tax-increases-toxicity
created: 2026-02-20
updated: 2026-02-20
aliases:
- collusion-penalty-has-no-economic-effect
cssclasses:
- claim
- claim-medium
tags:
- governance
- collusion
- penalty
- null-result
graph-group: claim
---

# collusion penalty multiplier has no significant effect on economic outcomes

## Evidence summary

In the [[20260213-221500_collusion_tax_effect]] sweep (160 runs, 4x4 factorial design), none of the 24 pairwise comparisons of collusion penalty multiplier (0.5x, 1.0x, 1.5x, 2.0x) on welfare, honest payoff, RLM payoff, or quality gap reach even BH significance. The largest observed effect is welfare at 1.5x vs 2.0x with d=0.34 (p=0.13).

This null result is informative: it establishes that the collusion penalty mechanism operates exclusively on the toxicity dimension (see [[claim-collusion-penalty-destabilizes]]) with zero detectable economic spillover. This directly grounds [[claim-tax-and-penalty-effects-are-orthogonal]] by establishing the penalty side of the partition — tax handles economics, penalty handles toxicity only. Combined with the penalty's paradoxical toxicity increase above 1.5x, this suggests the penalty mechanism provides no net benefit at any tested level, strengthening [[claim-governance-cost-paradox]]: collusion penalties are pure governance overhead with costs (toxicity destabilization) but no compensating economic benefits.

## Mechanism

The collusion penalty targets detected collusive behavior patterns but does not directly modify transaction economics. Penalized agents shift strategies (increasing toxicity) but maintain similar transaction volumes and values. The economic ecosystem absorbs the behavioral shift without aggregate welfare change, because the penalty redistributes collusion gains rather than destroying them.

## Boundary conditions

- Tested across 0.5–2.0x penalty range with 10 seeds per cell
- Collusion detection accuracy assumed constant; false positive rates could introduce economic effects
- The 12-agent population may have insufficient collusion pairs to generate detectable economic signals

## Open questions

- Would penalty effects emerge in topologies that structurally facilitate collusion (complete graph, ring)?
- Is the null result robust to larger populations where collusion is more prevalent?
- Does the null result extend to penalty multipliers above 2.0x, or does extreme penalty eventually destroy economic value?
- This strengthens [[claim-governance-cost-paradox]] — is collusion penalty governance purely overhead?
- Contrast with [[claim-collusion-wealth-destruction]] — detection + tax can destroy collusive wealth (137x gap), but the penalty multiplier alone does not move economic metrics. The mechanism distinction matters: detection flags behavior, tax extracts resources, but the penalty scalar has no independent economic force.
- Does [[claim-tax-penalty-interaction-on-toxicity-uncharacterized]] suggest that even though penalty has no marginal economic effect, its toxicity effect may compound with tax-induced toxicity?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[collusion-penalty-multiplier]]

<!-- topics: governance, collusion, penalty, null-result -->
