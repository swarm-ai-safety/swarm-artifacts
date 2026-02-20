---
description: Single baseline run of rlm_memory_as_power_seed1337, final welfare=88.3
type: experiment
status: completed
run_id: 20260210-212019_rlm_memory_as_power_seed1337
experiment_type: single
created: '2026-02-10'
aliases:
- 20260210-212019_rlm_memory_as_power_seed1337
cssclasses:
- experiment
- experiment-single
tags:
- rlm
- seed-1337
graph-group: experiment
---

# single-run baseline with welfare=88.3 (rlm memory as power seed1337)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 1337
- **Epochs**: 40
- **Steps per epoch**: 15
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 88.290
- **Toxicity rate**: 0.330
- **Acceptance rate**: 1.000
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-212019_rlm_memory_as_power_seed1337/csv/rlm_memory_as_power_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 1337
```

---

Topics:
- [[_index]]

<!-- topics: rlm, seed-1337 -->
