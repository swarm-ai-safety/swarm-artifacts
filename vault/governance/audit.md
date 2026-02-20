---
description: Probabilistic inspection of agent behavior with penalties for detected violations, effective alone but marginal
  atop circuit breakers
type: governance
status: active
mechanism: audit
parameters:
- name: audit_enabled
  type: bool
  default: true
  range: toggle
- name: audit_probability
  type: float
  default: 0.15
  range: 0.0–1.0, fraction of interactions audited per epoch
- name: audit_penalty_multiplier
  type: float
  default: 1.0
  range: 0.5–5.0, multiplier on base penalty when audit catches violation
- name: audit_threshold_p
  type: float
  default: 0.4
  range: 0.0–1.0, p-value threshold for flagging suspicious behavior
created: 2026-02-19
updated: 2026-02-19
aliases:
- audit
- probabilistic-audit
- random-audit
cssclasses:
- governance
graph-group: governance
tags:
- governance
- audit
- detection
- penalty
- welfare
---

# probabilistic audits add marginal detection power but do not improve outcomes when circuit breakers are already active

## How it works

Each epoch, a random subset of interactions is selected for audit with probability `audit_probability`. The audit evaluates whether the interaction's behavioral signals exceed a suspicion threshold (`audit_threshold_p`). If a violation is detected, the offending agent receives a penalty scaled by `audit_penalty_multiplier` applied to the base violation cost. The mechanism operates independently of other governance layers — an agent can be both audited and circuit-broken simultaneously.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `audit_enabled` | bool | true | toggles auditing |
| `audit_probability` | float | 0.15 | per-interaction audit chance |
| `audit_penalty_multiplier` | float | 1.0 | scales the penalty on detection |
| `audit_threshold_p` | float | 0.4 | statistical threshold for flagging |

## Evidence

The audit rate sweep ([[20260210-235049_kernel_market_audit_rate]]) tested 60 runs across varying `audit_probability` levels. This is the primary experiment exploring the audit parameter space in isolation.

In the kernel market governance comparison (70 runs, 7 regimes), audits alone produced welfare of 15.02 vs. 12.70 baseline — an 18% improvement, outperforming staking-only (10.65) and approaching circuit-breaker-only performance. However, adding audits to an active circuit breaker did not produce statistically significant additional benefit.

- [[20260210-235049_kernel_market_audit_rate]] — the dedicated audit rate sweep
- [[20260211-000149_kernel_market_governance_comparison]] — the 7-regime comparison
- [[claim-circuit-breakers-dominate]] — establishes that CB alone outperforms, with audits adding marginal value

The audit penalty multiplier was optimized in the adversarial red-team series. The original value of 2.5 was reduced to 1.0 based on sweep results ([[20260208-214603_adversarial_redteam_optimized_seed42]]). High penalty multipliers did not improve detection or deterrence but increased variance in outcomes.

Full governance stacks incorporating audits ([[20260213-173805_baseline_governance]], [[20260213-202050_baseline_governance_v2]]) confirmed the [[claim-governance-cost-paradox]]: the bundle imposes welfare costs exceeding toxicity reduction at all adversarial penetration levels.

## Interactions

- **With circuit breaker**: audits add marginal detection power but do not improve welfare or toxicity outcomes when the circuit breaker is already active. The circuit breaker catches the same agents faster through direct toxicity monitoring.
- **With staking**: audits + staking (welfare 14.20) underperforms audits alone (welfare 15.02), because staking excludes honest agents before they can benefit from audit protection.
- **With collusion detection**: audits and collusion detection operate on different signals (individual behavior vs. pairwise correlation). They are complementary in principle, but their combined overhead has not been isolated from the full governance stack.

## Known failure modes

- **Penalty calibration sensitivity**: the audit_penalty_multiplier was reduced from 2.5 to 1.0 in the optimized red-team runs because high multipliers increased outcome variance without improving deterrence.
- **Threshold gaming**: at `audit_threshold_p` = 0.4, adversaries near the boundary may be missed. The threshold has not been swept independently.
- **Audit evasion**: adaptive adversaries in red-team runs learned to modulate behavior on audited interactions while exploiting unaudited ones.

## Open questions

1. What is the optimal `audit_probability` — does the audit rate sweep reveal a phase transition similar to the tax rate's 5% threshold?
2. Is there a penalty multiplier in the 1.0–2.0 range that improves deterrence without increasing variance?
3. Can audits be made targeted (reputation-weighted probability) rather than purely random?
4. What is the false positive rate at `audit_threshold_p` = 0.4, and how does it interact with honest agent welfare?

---

Topics:
- [[_index]]

<!-- topics: governance, audit, detection, penalty, welfare -->