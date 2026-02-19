---
description: Single baseline run of rlm_recursive_collusion_seed42, final welfare=125.4
type: experiment
status: completed
run_id: 20260210-211721_rlm_recursive_collusion_seed42
experiment_type: single
created: '2026-02-10'
---

# single-run baseline with welfare=125.4 (rlm recursive collusion seed42)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 42
- **Epochs**: 30
- **Steps per epoch**: 15
- **Agents**: 12
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 125.409
- **Toxicity rate**: 0.348
- **Acceptance rate**: 1.000
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-211721_rlm_recursive_collusion_seed42/csv/rlm_recursive_collusion_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 42
```

---

Topics:
- [[_index]]

<!-- topics: rlm, collusion, seed-42 -->
