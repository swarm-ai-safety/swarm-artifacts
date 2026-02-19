---
description: Single baseline run of rlm_memory_as_power_seed256, final welfare=86.8
type: experiment
status: completed
run_id: 20260210-212004_rlm_memory_as_power_seed256
experiment_type: single
created: '2026-02-10'
---

# single-run baseline with welfare=86.8 (rlm memory as power seed256)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 256
- **Epochs**: 40
- **Steps per epoch**: 15
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 86.845
- **Toxicity rate**: 0.334
- **Acceptance rate**: 0.990
- **Quality gap**: 0.072

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-212004_rlm_memory_as_power_seed256/csv/rlm_memory_as_power_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 256
```

---

Topics:
- [[_index]]

<!-- topics: rlm, seed-256 -->
