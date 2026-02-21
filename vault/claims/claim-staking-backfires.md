---
description: Staking requirement hurts honest agents more than adversarial agents, reducing system welfare
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260211-000149_kernel_market_governance_comparison
    metric: welfare
    detail: "Staking-only: welfare 10.65 vs no-governance 12.70 (-16%), d=0.41, p=0.37 (not significant). Staking+audits 14.20 vs audits-only 15.02 (-5%). N=10 seeds per regime, 70 runs total across 7 regimes. Directionally consistent but underpowered"
  - run: 20260208-215902_sweep_reputation_decay
    metric: welfare
    detail: "Stake=10.0 welfare 4.75 vs stake=0.0 welfare 7.2 (-34%). Independent confirmation of staking backfire. 36 runs, 12 configs x 3 seeds, descriptive comparison"
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
  scenario: untested beyond kernel market governance comparison
supersedes: []
superseded_by: []
related_claims:
- claim-circuit-breakers-dominate
- claim-tax-disproportionately-punishes-rlm-agents
- claim-cb-audit-sufficient-for-solo-exploits
- claim-spawn-infrastructure-may-amplify-sybil-surface
- claim-write-cap-below-12-destroys-welfare
- claim-governance-cost-paradox
- claim-tax-welfare-tradeoff
created: 2026-02-11
updated: 2026-02-21
aliases:
- staking-backfires
- staking-requirement-hurts-honest-agents-more
cssclasses:
- claim
- claim-low
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

Confidence is low because:
- The main comparison (staking vs no-governance) is not statistically significant (d=0.41, p=0.37)
- Directionally replicated in the [[20260208-215902_sweep_reputation_decay]] (stake=10 vs 0: -34% welfare) but also lacks formal tests
- The stake amount was not swept — different amounts might change the picture
- Agent starting wealth is uniform; heterogeneous starting conditions are untested

## Open questions

1. Does a very low stake (e.g., 1.0) avoid the backfire while still providing some governance benefit?
2. Does the effect reverse if agents start with heterogeneous wealth?
3. Would dynamic staking (adjusting stake to reputation) fix the problem?
4. Does staking interact with the tax phase transition ([[claim-tax-phase-transition]])? At high tax rates, capital scarcity from taxation may compound the staking barrier.

## Update history

**2026-02-20** — backward-pass update:
- Added related claims: claim-governance-cost-paradox (staking backfire is a specific instance of the governance cost paradox), claim-tax-welfare-tradeoff (staking and tax both disproportionately harm honest agents).
- Added sensitivity note for scenario scope.
- Confidence remains **medium** — still based on a single 7-regime comparison (10 seeds per regime). Priority: stake amount sweep.

**2026-02-21** — Gate 2 statistical rigor fix:
- Added Cohen's d=0.41, p=0.37 to evidence — main welfare comparison NOT significant.
- Added corroborating evidence from reputation decay sweep (stake=10 vs 0: -34% welfare).
- Downgraded **medium → low**: directionally replicated across 2 independent sweeps but neither has formal significance. Upgrade requires stake amount sweep with ≥20 seeds.

---

Topics:
- [[_index]]
