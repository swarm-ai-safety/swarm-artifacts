---
description: Requires agents to lock collateral before participating, intended to deter bad actors but empirically backfires
type: governance
status: active
mechanism: staking
parameters:
- name: staking_enabled
  type: bool
  default: true
  range: toggle; meaningful only when min_stake > 0
- name: min_stake_to_participate
  type: float
  default: 10.0
  range: 0.0–50.0, higher = more exclusionary
- name: stake_slash_rate
  type: float
  default: 0.15
  range: 0.0–1.0, fraction of stake burned per violation
created: 2026-02-19
updated: 2026-02-19
aliases:
- staking
- collateral-requirement
cssclasses:
- governance
graph-group: governance
tags:
- governance
- staking
- welfare
- capital
- exclusion
---

# staking requirements paradoxically penalize honest agents who lack accumulated capital

## How it works

Before an agent can participate in interactions, it must lock `min_stake_to_participate` units of wealth as collateral. If the agent is caught violating governance rules (via audit or collusion detection), a fraction `stake_slash_rate` of the staked amount is burned. The stake is returned in full if the agent exits cleanly or completes an epoch without violations.

The design rationale mirrors real-world deposit systems: agents with "skin in the game" should self-police. In practice, the mechanism creates a regressive barrier that filters on capital rather than intent.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `staking_enabled` | bool | true | toggles the mechanism |
| `min_stake_to_participate` | float | 10.0 | collateral required to interact |
| `stake_slash_rate` | float | 0.15 | fraction burned per detected violation |

## Evidence

The kernel market governance comparison (70 runs, 7 regimes, 10 seeds each) directly tested staking as an isolated mechanism. Staking-only produced welfare of 10.65 vs. 12.70 under no governance — a 16% welfare *reduction*. Adding staking to audits degraded audit-only performance from 15.02 to 14.20.

- [[claim-staking-backfires]] — the primary finding: honest agents cannot afford the stake because they haven't accumulated capital through exploitative strategies
- [[20260211-000149_kernel_market_governance_comparison]] — the 7-regime comparison experiment

The adversarial red-team runs ([[20260208-214603_adversarial_redteam_optimized_seed42]], [[20260208-215712_adversarial_redteam_v2_seed42]], [[20260208-220218_adversarial_redteam_v3_seed42]]) tested staking within a full governance stack (stake=10.0, slash_rate=0.15). In these runs, staking was always bundled with circuit breakers, audits, and collusion detection, making isolation of its contribution difficult.

The full governance stack experiments ([[20260213-173805_baseline_governance]], [[20260213-202050_baseline_governance_v2]]) further confirmed that governance bundles including staking impose welfare costs exceeding their safety benefits at all adversarial penetration levels tested ([[claim-governance-cost-paradox]]).

## Interactions

- **With circuit breaker**: staking *undermines* circuit breaker effectiveness. Honest agents who can't afford the stake are excluded from the population before the circuit breaker can protect them.
- **With audits**: compound negative effect. Staking + audits performs worse than audits alone (14.20 vs. 15.02), because the stake requirement filters out cooperative agents who would benefit from audit protection.
- **With transaction tax**: both mechanisms extract resources from honest agents. The combination creates a double tax on participation.

## Known failure modes

- **Regressive exclusion**: the core failure. Agents with low wealth are excluded regardless of behavioral quality, creating a plutocratic filter.
- **Adversarial capital accumulation**: adversarial agents who successfully exploit proxy signals in early epochs accumulate enough capital to easily afford the stake, defeating its purpose.
- **Slash-rate insensitivity**: at the tested slash_rate of 0.15, the penalty is too small to deter well-capitalized adversaries and too large for marginal honest agents.

## Open questions

1. Does a very low stake (e.g., 1.0) avoid the backfire while still providing governance benefit?
2. Would dynamic staking — adjusting the required stake to an agent's reputation score — fix the regressive exclusion problem?
3. Does the effect reverse if agents start with heterogeneous wealth distributions?
4. Can stake requirements be made progressive (higher stake for higher-wealth agents)?
5. The stake amount was tested only at the default of 10.0 — a parameter sweep is needed.

---

Topics:
- [[_index]]

<!-- topics: governance, staking, welfare, capital, exclusion -->