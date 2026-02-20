---
description: Single baseline run of delegation_games_seed42, final welfare=11.1
type: experiment
status: completed
run_id: 20260213-143120_delegation_games_seed42
experiment_type: single
created: '2026-02-13'
aliases:
- 20260213-143120_delegation_games_seed42
cssclasses:
- experiment
- experiment-single
tags:
- delegation
- seed-42
graph-group: experiment
---

# single-run baseline with welfare=11.1 (delegation games seed42)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 42
- **Epochs**: 20
- **Steps per epoch**: 15
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 11.073
- **Toxicity rate**: 0.371
- **Acceptance rate**: 0.833
- **Quality gap**: 0.207

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260213-143120_delegation_games_seed42/csv/delegation_games_epochs.csv`

## Reproduction

```bash
python -m swarm run unknown --seed 42
```

---

Topics:
- [[_index]]

<!-- topics: delegation, seed-42 -->
