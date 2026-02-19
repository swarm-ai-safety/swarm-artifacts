---
description: Single baseline run of rlm_recursive_collusion_seed999, final welfare=130.7
type: experiment
status: completed
run_id: 20260210-211803_rlm_recursive_collusion_seed999
experiment_type: single
created: '2026-02-10'
---

# single-run baseline with welfare=130.7 (rlm recursive collusion seed999)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 999
- **Epochs**: 30
- **Steps per epoch**: 15
- **Agents**: 12
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 130.720
- **Toxicity rate**: 0.330
- **Acceptance rate**: 1.000
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-211803_rlm_recursive_collusion_seed999/csv/rlm_recursive_collusion_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 999
```

---

Topics:
- [[_index]]

<!-- topics: rlm, collusion, seed-999 -->
