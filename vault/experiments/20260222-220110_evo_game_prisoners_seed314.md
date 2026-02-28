---
description: Single baseline run of evo_game_prisoners_seed314, final welfare=15.0
type: experiment
status: completed
run_id: 20260222-220110_evo_game_prisoners_seed314
experiment_type: single
created: '2026-02-22'
---

# single-run baseline with welfare=15.0 (evo game prisoners seed314)

## Design

- **Type**: Single run
- **Scenario**: evo_game_prisoners
- **Seed**: 314
- **Epochs**: 10
- **Steps per epoch**: 5
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 14.991
- **Toxicity rate**: 0.247
- **Acceptance rate**: 0.917
- **Quality gap**: 0.251

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260222-220110_evo_game_prisoners_seed314/csv/evo_game_prisoners_epochs.csv`

## Reproduction

```bash
python -m swarm run evo_game_prisoners --seed 314
```

---

Topics:
- [[_index]]

<!-- topics: evo-game, prisoners-dilemma, seed-314, single -->
