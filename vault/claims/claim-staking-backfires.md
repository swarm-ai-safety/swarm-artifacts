---
description: Staking requirement hurts honest agents more than adversarial agents, reducing system welfare
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260211-000149_kernel_market_governance_comparison
    metric: welfare
    detail: 'Staking-only: welfare 10.65 vs no-governance 12.70. Honest agents lose disproportionately.'
  weakening: []
  boundary_conditions:
  - Tested in kernel market domain with 8 agents
  - Small-world topology (k=4, p=0.15)
  - Fixed stake amount (min_stake_to_participate=10.0)
  - Single run comparison within 7-regime sweep
sensitivity:
  topology: untested beyond small_world
  stake_amount: only tested at default (10.0)
  agent_wealth_distribution: uniform starting conditions only
supersedes: []
superseded_by: []
related_claims:
- claim-circuit-breakers-dominate
- claim-tax-disproportionately-punishes-rlm-agents
created: 2026-02-11
updated: 2026-02-18
aliases:
- staking-backfires
- staking-requirement-hurts-honest-agents-more
cssclasses:
- claim
- claim-medium
graph-group: claim
---

# staking requirement hurts honest agents more than adversarial agents

## Evidence summary

In the kernel market governance comparison (70 runs, 7 regimes):

| Regime | Welfare | vs Baseline |
|--------|---------|-------------|
| No governance | 12.70 | — |
| Staking only | 10.65 | -16% |
| Staking + audits | 14.20 | +12% |
| Audits only | 15.02 | +18% |

Staking *alone* makes things worse than no governance. Adding staking to audits performs worse than audits alone.

## Mechanism

Honest agents, who haven't accumulated capital through exploitative strategies, struggle to meet the stake requirement. Adversarial agents who successfully game proxy signals accumulate resources faster and can afford the stake. The mechanism perversely gates participation by honesty rather than by trustworthiness.

## Caveats

Confidence is medium because:
- This is from a single 7-regime comparison (10 seeds per regime)
- The stake amount (10.0) was not swept — different amounts might change the picture
- Agent starting wealth is uniform; heterogeneous starting conditions are untested

## Open questions

1. Does a very low stake (e.g., 1.0) avoid the backfire while still providing some governance benefit?
2. Does the effect reverse if agents start with heterogeneous wealth?
3. Would dynamic staking (adjusting stake to reputation) fix the problem?

---

Topics:
- [[_index]]
