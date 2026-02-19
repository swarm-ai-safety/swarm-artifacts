---
description: Single baseline run of rlm_memory_as_power_seed7, final welfare=91.7
type: experiment
status: completed
run_id: 20260210-211958_rlm_memory_as_power_seed7
experiment_type: single
created: '2026-02-10'
---

# single-run baseline with welfare=91.7 (rlm memory as power seed7)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 7
- **Epochs**: 40
- **Steps per epoch**: 15
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 91.712
- **Toxicity rate**: 0.328
- **Acceptance rate**: 1.000
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-211958_rlm_memory_as_power_seed7/csv/rlm_memory_as_power_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 7
```

---

Topics:
- [[_index]]

<!-- topics: rlm, seed-7 -->
