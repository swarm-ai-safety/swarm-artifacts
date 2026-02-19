---
description: Single baseline run of rlm_recursive_collusion_seed123, final welfare=129.7
type: experiment
status: completed
run_id: 20260210-211757_rlm_recursive_collusion_seed123
experiment_type: single
created: '2026-02-10'
---

# single-run baseline with welfare=129.7 (rlm recursive collusion seed123)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 123
- **Epochs**: 30
- **Steps per epoch**: 15
- **Agents**: 12
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 129.701
- **Toxicity rate**: 0.327
- **Acceptance rate**: 0.985
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-211757_rlm_recursive_collusion_seed123/csv/rlm_recursive_collusion_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 123
```

---

Topics:
- [[_index]]

<!-- topics: rlm, collusion, seed-123 -->
