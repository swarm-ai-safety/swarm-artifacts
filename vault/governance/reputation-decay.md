---
description: Applies temporal decay to reputation scores so agents must maintain good behavior continuously rather than coasting
  on history
type: governance
status: active
mechanism: reputation-decay
parameters:
- name: reputation_decay_rate
  type: float
  default: 0.95
  range: 0.0–1.0, per-epoch multiplicative decay (1.0 = no decay, lower = faster decay)
created: 2026-02-19
updated: 2026-02-19
aliases:
- reputation-decay
- temporal-reputation-decay
- reputation-half-life
cssclasses:
- governance
graph-group: governance
tags:
- governance
- reputation
- decay
- temporal
- adversarial
---

# reputation decay forces ongoing good behavior but was optimized to 1.0 (no decay) in adversarial red-team tuning

## How it works

Each epoch, every agent's reputation score is multiplied by `reputation_decay_rate`. A rate of 0.95 means an agent retains 95% of its reputation per epoch, creating a half-life of approximately 14 epochs. A rate of 1.0 disables decay entirely — reputation becomes cumulative. Lower rates force agents to continuously demonstrate good behavior to maintain standing; higher rates allow agents to coast on historical reputation.

Reputation feeds into multiple downstream mechanisms: it weights payoff calculations (via `w_rep`), influences partner selection in dynamic networks, and interacts with staking requirements in governance stacks that couple collateral to standing.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `reputation_decay_rate` | float | 0.95 | per-epoch multiplicative decay factor |

## Evidence

The reputation decay sweep ([[20260208-215902_sweep_reputation_decay]]) is the primary parameter exploration, testing multiple decay rates across seeds. This sweep was completed on Feb 8 and informed subsequent red-team optimization.

The adversarial red-team series reveals a critical finding about decay rate optimization:

- **v2** ([[20260208-215712_adversarial_redteam_v2_seed42]]) used `reputation_decay_rate: 0.95` (the default)
- **v3** ([[20260208-220218_adversarial_redteam_v3_seed42]]) changed to `reputation_decay_rate: 1.0` (no decay), described as "fully optimized" based on sweep results

This progression suggests the reputation decay sweep found that decay *hurts* system performance in adversarial settings — the optimized configuration disabled it entirely. The scenario changelog explicitly lists `reputation_decay_rate: 0.95 -> 1.0` as an optimization step derived from the reputation decay sweep.

The full governance stack experiments ([[20260213-173805_baseline_governance]], [[20260213-202050_baseline_governance_v2]]) did not independently sweep reputation decay, but the mechanism was active in the red-team runs that contributed to [[claim-governance-cost-paradox]].

The adversarial red-team optimized run ([[20260208-214603_adversarial_redteam_optimized_seed42]]) used the original `reputation_decay_rate: 0.95` alongside the full governance stack, with `w_rep: 2.5` as the reputation weight in payoff calculations.

## Interactions

- **With circuit breaker**: reputation decay and circuit breakers address the same problem (sustained bad behavior) through different mechanisms. Decay is gradual; circuit breakers are discrete. When both are active, the circuit breaker dominates because it removes agents entirely, making the gradual reputation loss moot for frozen agents.
- **With staking**: if stake requirements are coupled to reputation, decay creates a compounding exclusion effect — agents whose reputation decays may lose staking eligibility and be locked out. This amplifies the regressive exclusion documented in [[claim-staking-backfires]].
- **With transaction tax**: decay affects the reputation-weighted payoff component but does not directly interact with the tax mechanism. However, agents with decayed reputation receive lower payoffs, reducing the tax base.
- **With audits**: audits impose discrete penalties; decay imposes continuous ones. Decay may cause an audited agent's reputation to fall faster than intended, creating a double-punishment effect.

## Known failure modes

- **Optimized to inactivity**: the red-team optimization process set decay to 1.0 (no decay), suggesting the mechanism is net-harmful in adversarial settings. This is the most important finding: the system performs better without it.
- **Half-life mismatch**: at the default rate of 0.95, the half-life is ~14 epochs. In 30-epoch simulations, this means an agent's starting reputation is nearly irrelevant by mid-run. This may be appropriate for long simulations but could be too aggressive for shorter ones.
- **Honest agent erosion**: even consistently cooperative agents lose reputation to decay during epochs where they have few interactions (e.g., when frozen or when partners are unavailable), creating artificial vulnerability.

## Open questions

1. Why does disabling decay improve adversarial robustness? Is it because decay erodes honest agents' reputations during freeze periods, or because adversarial agents exploit the "clean slate" effect of decayed bad history?
2. What is the optimal decay rate if any? The sweep explored the parameter space but the conclusion appears to be "no decay is best" — is this robust across domains beyond the kernel market?
3. Would asymmetric decay (faster decay for negative reputation, slower for positive) outperform uniform decay?
4. How does decay interact with the reputation weight `w_rep`? At high `w_rep` values, even small decay rates could have outsized effects.
5. The sweep was conducted with a single scenario — does the finding generalize to non-adversarial settings where reputation history is more informative?

---

Topics:
- [[_index]]

<!-- topics: governance, reputation, decay, temporal, adversarial -->