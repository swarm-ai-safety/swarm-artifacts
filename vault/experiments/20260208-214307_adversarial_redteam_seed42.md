---
description: Single baseline run of adversarial_redteam_seed42, final welfare=0.0
type: experiment
status: completed
run_id: 20260208-214307_adversarial_redteam_seed42
experiment_type: single
created: '2026-02-08'
aliases:
- 20260208-214307_adversarial_redteam_seed42
cssclasses:
- experiment
- experiment-single
tags:
- redteam
- adversarial
- seed-42
graph-group: experiment
---

# single-run baseline with welfare=0.0 (adversarial redteam seed42)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 42
- **Epochs**: 30
- **Steps per epoch**: 15
- **Agents**: 8
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 0.000
- **Toxicity rate**: 0.000
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260208-214307_adversarial_redteam_seed42/csv/adversarial_redteam_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 42
```

---

Topics:
- [[_index]]

<!-- topics: redteam, adversarial, seed-42 -->
