---
description: Single baseline run of rlm_recursive_collusion_seed256, final welfare=123.7
type: experiment
status: completed
run_id: 20260210-211800_rlm_recursive_collusion_seed256
experiment_type: single
created: '2026-02-10'
aliases:
- 20260210-211800_rlm_recursive_collusion_seed256
cssclasses:
- experiment
- experiment-single
tags:
- rlm
- collusion
- seed-256
graph-group: experiment
---

# single-run baseline with welfare=123.7 (rlm recursive collusion seed256)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 256
- **Epochs**: 30
- **Steps per epoch**: 15
- **Agents**: 12
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 123.650
- **Toxicity rate**: 0.343
- **Acceptance rate**: 0.977
- **Quality gap**: 0.015

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260210-211800_rlm_recursive_collusion_seed256/csv/rlm_recursive_collusion_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 256
```

---

Topics:
- [[_index]]

<!-- topics: rlm, collusion, seed-256 -->
