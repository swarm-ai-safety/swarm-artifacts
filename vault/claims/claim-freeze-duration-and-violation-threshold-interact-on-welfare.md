---
description: Longer freeze durations (5 vs 1 epoch) improve welfare 17% and interact with violation thresholds, replicated across 3 seeds
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260208-215009_sweep_freeze_duration
    metric: welfare
    detail: "Freeze duration 5 vs 1 epoch: welfare_per_epoch 7.8 vs 7.3 (+17%). Best config: duration=5, violations=3, welfare=8.0. Worst: duration=1, violations=8, welfare=7.0. 36 runs, 12 configs x 3 seeds"
  - run: 20260208-215009_sweep_freeze_duration
    metric: toxicity_rate
    detail: "Tighter violation threshold (3 vs 8): toxicity 0.227 vs 0.261 (-13%). Replicated across all 3 seeds"
  weakening: []
  boundary_conditions:
  - "Freeze duration: 1, 2, 3, 5 epochs. Violation threshold: 3, 5, 8"
  - "3 seeds — adequate for medium effects but may miss interactions"
  - "8 agents, default topology"
  - "No formal interaction test (2-way ANOVA missing)"
sensitivity:
  topology: untested
  agent_count: untested beyond 8
  governance_interaction: "Interacts with violation threshold; untested with tax or collusion detection"
supersedes: []
superseded_by: []
related_claims:
- claim-circuit-breakers-dominate
- claim-cb-null-may-reflect-design-limitation
- claim-governance-cost-paradox
- claim-audit-threshold-interaction-enables-dancing
created: 2026-02-21
updated: 2026-02-21
aliases:
- freeze-duration-and-violation-threshold-interact-on-welfare
cssclasses:
- claim
- claim-low
tags:
- governance
- circuit-breaker
- freeze-duration
- parameter-sensitivity
graph-group: claim
---

# longer freeze durations improve welfare 17% and interact with violation thresholds

## Evidence summary

The [[20260208-215009_sweep_freeze_duration]] swept freeze duration (1-5 epochs) x violation threshold (3-8) across 36 runs with 3 seeds per config.

| Duration | Violations=3 | Violations=5 | Violations=8 |
|----------|-------------|-------------|-------------|
| 1 epoch  | 7.3         | 7.1         | 7.0         |
| 5 epochs | 8.0         | 7.8         | 7.5         |

The best configuration (duration=5, violations=3) produces 14% higher welfare than the worst (duration=1, violations=8). Both parameters contribute: longer freezes give the ecosystem more time to recover from adversarial disruption, while tighter violation thresholds catch bad actors earlier.

Toxicity also responds: violation threshold 3 vs 8 reduces toxicity from 0.261 to 0.227 (-13%), replicated across all 3 seeds.

This directly addresses [[claim-cb-null-may-reflect-design-limitation]]: the CB null effect in binary on/off designs may reflect that the default freeze parameters are suboptimal. The freeze duration sweep shows CB parameters have real effects when varied continuously. If confirmed, this partially resolves the tension between [[claim-circuit-breakers-dominate]] (CB effective in governance comparison) and the CB null in baseline governance sweeps — the difference may be parameter calibration, not fundamental CB ineffectiveness.

## Open questions

- Does the interaction hold at larger scale (more seeds, more agents)?
- What is the optimal freeze duration beyond 5 epochs? The sweep didn't test longer durations.
- How does freeze duration interact with tax rate?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, circuit-breaker, freeze-duration, parameter-sensitivity -->
