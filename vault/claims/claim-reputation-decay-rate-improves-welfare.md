---
description: Higher reputation decay (1.0 vs 0.9) increases welfare 12% while lower minimum stake reduces welfare 8-10%, replicated across 3 seeds
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260208-215902_sweep_reputation_decay
    metric: welfare
    detail: "Decay 1.0 vs 0.9: welfare_per_epoch 7.2 vs 5.9 (+12%). Best config: decay=1.0, stake=0.0. Worst: decay=0.9, stake=10.0, welfare=4.75. 48% spread. 36 runs, 12 configs x 3 seeds"
  - run: 20260208-215902_sweep_reputation_decay
    metric: toxicity_rate
    detail: "Best config (decay=1.0, stake=0.0) also minimizes toxicity: 0.170 (lowest in sweep). Consistent across 3 seeds"
  weakening: []
  boundary_conditions:
  - "Decay rates: 0.9, 0.95, 0.98, 1.0. Min stake: 0.0, 5.0, 10.0"
  - "3 seeds — replicated but limited power for interaction effects"
  - "8 agents, default topology"
  - "Decay=1.0 means no decay (full reputation persistence)"
sensitivity:
  topology: untested
  agent_count: untested beyond 8
  governance_interaction: "Stake interacts with decay; untested with tax or CB"
supersedes: []
superseded_by: []
related_claims:
- claim-staking-backfires
- claim-governance-cost-paradox
- claim-circuit-breakers-dominate
created: 2026-02-21
updated: 2026-02-21
aliases:
- reputation-decay-rate-improves-welfare
cssclasses:
- claim
- claim-low
tags:
- governance
- reputation-decay
- staking
- parameter-sensitivity
graph-group: claim
---

# full reputation persistence (no decay) improves welfare 12% while minimum stake requirements reduce it

## Evidence summary

The [[20260208-215902_sweep_reputation_decay]] swept reputation decay rate (0.9-1.0) x minimum stake (0.0-10.0) across 36 runs with 3 seeds per config.

The strongest finding: decay rate 1.0 (full persistence, no decay) with zero stake requirement produces the best welfare (7.2/epoch) and lowest toxicity (0.170). The worst configuration (decay=0.9, stake=10.0) produces welfare 4.75/epoch — a 48% spread between best and worst.

**Reputation decay direction:** Higher decay values (slower decay, more persistence) improve welfare. This is counterintuitive if one expects fast decay to "reset" bad actors — instead, reputation persistence allows good actors to build durable trust, improving cooperation quality.

**Stake interaction:** Higher minimum stakes reduce welfare, consistent with [[claim-staking-backfires]]. The reputation decay sweep provides independent confirmation that staking requirements hurt honest agents more than they protect the ecosystem.

The combination of "no decay + no stake" achieving both best welfare and lowest toxicity challenges [[claim-governance-cost-paradox]]: this specific configuration achieves security and welfare simultaneously, suggesting the paradox may be resolvable through parameter optimization rather than fundamental tradeoff.

## Open questions

- Does the reputation persistence benefit hold with adversarial agents who game reputation?
- Is decay=1.0 actually optimal, or would even higher persistence (with reputation caps) be better?
- How does reputation decay interact with circuit breaker thresholds?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, reputation-decay, staking, parameter-sensitivity -->
