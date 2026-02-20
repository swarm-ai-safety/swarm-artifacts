---
description: Single baseline run of rlm_memory_as_power_seed8080, final welfare=86.3
type: experiment
status: completed
run_id: 20260210-212022_rlm_memory_as_power_seed8080
experiment_type: single
created: '2026-02-10'
aliases:
- 20260210-212022_rlm_memory_as_power_seed8080
cssclasses:
- experiment
- experiment-single
tags:
- rlm
- seed-8080
graph-group: experiment
---

# single-run baseline with welfare=86.3 (rlm memory as power seed8080)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 8080
- **Epochs**: 40
- **Steps per epoch**: 15
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 86.280
- **Toxicity rate**: 0.338
- **Acceptance rate**: 0.990
- **Quality gap**: -0.091

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-212022_rlm_memory_as_power_seed8080/csv/rlm_memory_as_power_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 8080
```

---

Topics:
- [[_index]]

<!-- topics: rlm, seed-8080 -->
