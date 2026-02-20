---
description: Single baseline run of rlm_memory_as_power_seed42, final welfare=91.3
type: experiment
status: completed
run_id: 20260210-225330_rlm_memory_as_power_seed42
experiment_type: single
created: '2026-02-10'
aliases:
- 20260210-225330_rlm_memory_as_power_seed42
cssclasses:
- experiment
- experiment-single
tags:
- rlm
- seed-42
graph-group: experiment
---

# single-run baseline with welfare=91.3 (rlm memory as power seed42)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 42
- **Epochs**: 40
- **Steps per epoch**: 15
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 91.284
- **Toxicity rate**: 0.321
- **Acceptance rate**: 1.000
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-225330_rlm_memory_as_power_seed42/csv/rlm_memory_as_power_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 42
```

---

Topics:
- [[_index]]

<!-- topics: rlm, seed-42 -->
