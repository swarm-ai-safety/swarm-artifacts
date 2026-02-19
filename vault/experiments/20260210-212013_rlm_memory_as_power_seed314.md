---
description: Single baseline run of rlm_memory_as_power_seed314, final welfare=85.2
type: experiment
status: completed
run_id: 20260210-212013_rlm_memory_as_power_seed314
experiment_type: single
created: '2026-02-10'
---

# single-run baseline with welfare=85.2 (rlm memory as power seed314)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 314
- **Epochs**: 40
- **Steps per epoch**: 15
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 85.165
- **Toxicity rate**: 0.342
- **Acceptance rate**: 1.000
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-212013_rlm_memory_as_power_seed314/csv/rlm_memory_as_power_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 314
```

---

Topics:
- [[_index]]

<!-- topics: rlm, seed-314 -->
