---
description: Single baseline run of rlm_recursive_collusion_seed7, final welfare=131.7
type: experiment
status: completed
run_id: 20260210-211753_rlm_recursive_collusion_seed7
experiment_type: single
created: '2026-02-10'
aliases:
- 20260210-211753_rlm_recursive_collusion_seed7
cssclasses:
- experiment
- experiment-single
tags:
- rlm
- collusion
- seed-7
graph-group: experiment
---

# single-run baseline with welfare=131.7 (rlm recursive collusion seed7)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 7
- **Epochs**: 30
- **Steps per epoch**: 15
- **Agents**: 12
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 131.683
- **Toxicity rate**: 0.322
- **Acceptance rate**: 0.985
- **Quality gap**: 0.011

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-211753_rlm_recursive_collusion_seed7/csv/rlm_recursive_collusion_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 7
```

---

Topics:
- [[_index]]

<!-- topics: rlm, collusion, seed-7 -->
