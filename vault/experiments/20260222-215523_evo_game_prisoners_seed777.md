---
description: Single baseline run of evo_game_prisoners_seed777, final welfare=21.0
type: experiment
status: completed
run_id: 20260222-215523_evo_game_prisoners_seed777
experiment_type: single
created: '2026-02-22'
---

# single-run baseline with welfare=21.0 (evo game prisoners seed777)

## Design

- **Type**: Single run
- **Scenario**: evo_game_prisoners
- **Seed**: 777
- **Epochs**: 10
- **Steps per epoch**: 5
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 20.976
- **Toxicity rate**: 0.291
- **Acceptance rate**: 1.000
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260222-215523_evo_game_prisoners_seed777/csv/evo_game_prisoners_epochs.csv`

## Reproduction

```bash
python -m swarm run evo_game_prisoners --seed 777
```

---

Topics:
- [[_index]]

<!-- topics: evo-game, prisoners-dilemma, seed-777, single -->
