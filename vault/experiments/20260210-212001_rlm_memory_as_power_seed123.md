---
description: Single baseline run of rlm_memory_as_power_seed123, final welfare=80.5
type: experiment
status: completed
run_id: 20260210-212001_rlm_memory_as_power_seed123
experiment_type: single
created: '2026-02-10'
aliases:
- 20260210-212001_rlm_memory_as_power_seed123
cssclasses:
- experiment
- experiment-single
tags:
- rlm
- seed-123
graph-group: experiment
---

# single-run baseline with welfare=80.5 (rlm memory as power seed123)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 123
- **Epochs**: 40
- **Steps per epoch**: 15
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 80.498
- **Toxicity rate**: 0.341
- **Acceptance rate**: 0.970
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-212001_rlm_memory_as_power_seed123/csv/rlm_memory_as_power_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 123
```

---

Topics:
- [[_index]]

<!-- topics: rlm, seed-123 -->
