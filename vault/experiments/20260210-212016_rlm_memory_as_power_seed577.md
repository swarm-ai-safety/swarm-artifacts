---
description: Single baseline run of rlm_memory_as_power_seed577, final welfare=85.0
type: experiment
status: completed
run_id: 20260210-212016_rlm_memory_as_power_seed577
experiment_type: single
created: '2026-02-10'
aliases:
- 20260210-212016_rlm_memory_as_power_seed577
cssclasses:
- experiment
- experiment-single
tags:
- rlm
- seed-577
graph-group: experiment
---

# single-run baseline with welfare=85.0 (rlm memory as power seed577)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 577
- **Epochs**: 40
- **Steps per epoch**: 15
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 85.025
- **Toxicity rate**: 0.337
- **Acceptance rate**: 0.990
- **Quality gap**: 0.087

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-212016_rlm_memory_as_power_seed577/csv/rlm_memory_as_power_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 577
```

---

Topics:
- [[_index]]

<!-- topics: rlm, seed-577 -->
