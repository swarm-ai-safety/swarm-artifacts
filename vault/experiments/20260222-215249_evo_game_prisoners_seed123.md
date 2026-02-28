---
description: Single baseline run of evo_game_prisoners_seed123, final welfare=24.1
type: experiment
status: completed
run_id: 20260222-215249_evo_game_prisoners_seed123
experiment_type: single
created: '2026-02-22'
---

# single-run baseline with welfare=24.1 (evo game prisoners seed123)

## Design

- **Type**: Single run
- **Scenario**: evo_game_prisoners
- **Seed**: 123
- **Epochs**: 10
- **Steps per epoch**: 5
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 24.149
- **Toxicity rate**: 0.257
- **Acceptance rate**: 0.929
- **Quality gap**: 0.092

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260222-215249_evo_game_prisoners_seed123/csv/evo_game_prisoners_epochs.csv`

## Reproduction

```bash
python -m swarm run evo_game_prisoners --seed 123
```

---

Topics:
- [[_index]]

<!-- topics: evo-game, prisoners-dilemma, seed-123, single -->
