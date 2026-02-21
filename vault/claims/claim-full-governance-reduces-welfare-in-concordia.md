---
description: Full defense governance stack reduces welfare by d≈2.0 vs baseline in Concordia scenario, with toxicity unchanged
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260211-012350_concordia_sweep
    metric: welfare
    detail: "Full defense welfare 55.8±5.8 vs baseline 67.7±5.8, d≈2.0 (very large). All full_defense runs froze 5 agents. 5 seeds x 8 mechanisms = 40 runs"
  - run: 20260211-011507_concordia_sweep
    metric: welfare
    detail: "Replicates in 2-seed study: full_defense 32.1-37.3 vs baseline 37.3-43.2, d≈1.0. 2 seeds x 8 mechanisms = 16 runs"
  - run: 20260211-012350_concordia_sweep
    metric: toxicity_rate
    detail: "Toxicity invariant across all 8 mechanisms (0.334-0.391). Governance imposes welfare cost with zero toxicity benefit"
  weakening: []
  boundary_conditions:
  - "Concordia scenario (Concordia framework integration); 8 governance regimes tested"
  - "Full defense freezes 4-5 agents, drastically reducing active population"
  - "Tax-only and light_defense impose 2-4% welfare cost with unchanged toxicity"
  - "CB shows marginal welfare buffering (d≈0.3) but no toxicity effect"
sensitivity:
  topology: untested
  agent_count: untested beyond Concordia default
  governance_interaction: "8 regimes compared: baseline, tax_only, reputation, circuit_breaker, audits, collusion_detection, light_defense, full_defense"
supersedes: []
superseded_by: []
related_claims:
- claim-governance-cost-paradox
- claim-circuit-breakers-dominate
- claim-staking-backfires
- claim-tax-welfare-tradeoff
created: 2026-02-21
updated: 2026-02-21
aliases:
- full-governance-reduces-welfare-in-concordia
cssclasses:
- claim
- claim-medium
tags:
- governance
- concordia
- welfare
- mechanism-comparison
graph-group: claim
---

# full governance stack reduces welfare ~18% in Concordia with zero toxicity benefit

## Evidence summary

Two Concordia governance sweeps compared 8 governance regimes:

**5-seed study** ([[20260211-012350_concordia_sweep]], 40 runs):

| Regime | Welfare (mean±SD) | Frozen agents |
|--------|-------------------|---------------|
| Baseline | 67.7 ± 5.8 | 0 |
| Tax only | 65.8 ± 5.4 | 0 |
| Circuit breaker | 69.2 ± 4.9 | 0-1 |
| Light defense | 65.3 ± 5.6 | 0-1 |
| **Full defense** | **55.8 ± 5.8** | **5** |

The full defense regime reduces welfare by d≈2.0 (very large effect) while freezing 5 agents. Critically, **toxicity is invariant** across all 8 regimes (range 0.334-0.391), meaning the welfare cost produces zero safety benefit.

The 2-seed study ([[20260211-011507_concordia_sweep]], 16 runs) replicates the direction with a smaller effect size (d≈1.0).

This is the strongest direct evidence for [[claim-governance-cost-paradox]]: in the Concordia scenario, the full governance stack is purely costly. Tax-only and light_defense impose modest welfare costs (2-4%) for no toxicity improvement. Only circuit breakers show marginal welfare benefit (d≈0.3), consistent with [[claim-circuit-breakers-dominate]] but not statistically robust.

The mechanism: full defense freezes 4-5 of ~8 agents, reducing the active population by >50%. The welfare cost comes from lost transactions, not from governance extracting resources. This suggests the CB threshold calibration issue ([[claim-cb-null-may-reflect-design-limitation]]) — the default CB configuration is too aggressive in Concordia, freezing legitimate agents alongside adversarial ones.

## Open questions

- Is the Concordia toxicity invariance a property of the scenario or the agent architecture?
- Would CB threshold tuning (less aggressive freezing) preserve welfare while maintaining security?
- Does this generalize beyond Concordia, or is it scenario-specific?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, concordia, welfare, mechanism-comparison -->
