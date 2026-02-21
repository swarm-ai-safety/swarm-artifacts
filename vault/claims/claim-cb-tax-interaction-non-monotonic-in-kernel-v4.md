---
description: CB improves welfare at 5% tax (+2.42) but harms welfare at 0% (-2.02), 10% (-2.15), and 15% (-7.65) in kernel v4
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260214-113750_kernel_v4_code_sweep
    metric: welfare
    detail: "CB welfare delta by tax: 0%=-2.02, 5%=+2.42, 10%=-2.15, 15%=-7.65. N=5 seeds per cell, no significance testing"
  weakening: []
  boundary_conditions:
  - kernel_market_v4_code scenario, 8 agents, 5 seeds per config, 5 epochs
  - Severely underpowered; high variance (std/mean = 21-67%)
  - Could be noise; council flagged for expanded replication
sensitivity:
  topology: untested
  agent_count: 8 agents
  governance_interaction: this IS the interaction finding
supersedes: []
superseded_by: []
related_claims:
- claim-tax-cb-interact-on-quality-gap
- claim-cb-null-may-reflect-design-limitation
- claim-tax-welfare-direction-is-scenario-dependent
- claim-governance-cost-paradox
- claim-optimal-tax-range-0-to-5pct
- claim-welfare-plateaus-above-12pct-tax
- claim-write-cap-amplifies-tau-rejection
created: 2026-02-20
updated: 2026-02-20
aliases:
- cb-tax-interaction-non-monotonic-in-kernel-v4
cssclasses:
- claim
- claim-low
tags:
- governance
- circuit-breaker
- transaction-tax
- interaction
- kernel-market
graph-group: claim
---

# circuit breaker and tax rate interact non-monotonically on welfare in kernel v4 code markets

## Evidence summary

In the [[20260214-113750_kernel_v4_code_sweep]] (40 runs, 4 tax x 2 CB x 5 seeds), the CB welfare effect reverses direction depending on tax rate:

| Tax rate | CB off welfare | CB on welfare | Delta |
|----------|---------------|---------------|-------|
| 0% | 12.18 | 10.16 | -2.02 |
| 5% | 11.80 | 14.22 | +2.42 |
| 10% | 11.25 | 9.10 | -2.15 |
| 15% | 16.96 | 9.31 | -7.65 |

CB helps at 5% tax but harms at all other rates, with the most severe harm at 15% (-7.65). This extends [[claim-tax-cb-interact-on-quality-gap]] from the baseline governance context to kernel markets, but with a different pattern: the baseline study showed CB interacting on quality_gap but not welfare, while this study shows welfare-level interaction. The non-monotonic interaction means [[claim-governance-cost-paradox]] cannot be evaluated from main effects alone — governance cost-benefit depends on the specific parameter combination. The CB benefit at 5% tax coincides with the safe operating range identified in [[claim-optimal-tax-range-0-to-5pct]], suggesting that the tax safe range may also be the region where CB adds value. The severe harm at 15% occurs in what [[claim-welfare-plateaus-above-12pct-tax]] identifies as the collapsed ecosystem regime, where CB removal of agents from an already-depleted system is maximally destructive. The tau x k_max interaction in [[claim-write-cap-amplifies-tau-rejection]] shows the same pattern in the memory domain: governance parameters that are independently manageable become destructive when combined at their boundary conditions.

## Open questions

- Replicate with 20-30 seeds to determine if the 5% sweet spot is real or noise
- Why does CB help specifically at 5% tax? Is it the phase transition boundary?
- Does this pattern persist across kernel market versions (v1, v2, v3)?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[transaction-tax-rate]]

<!-- topics: governance, circuit-breaker, transaction-tax, interaction, kernel-market -->
