---
description: Single baseline run of evo_game_prisoners_seed42, final welfare=30.4
type: experiment
status: completed
run_id: 20260222-211635_evo_game_prisoners_seed42
experiment_type: single
created: '2026-02-22'
---

# single-run baseline with welfare=30.4 (evo game prisoners seed42)

## Design

- **Type**: Single run
- **Scenario**: evo_game_prisoners
- **Seed**: 42
- **Epochs**: 10
- **Steps per epoch**: 5
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 30.406
- **Toxicity rate**: 0.273
- **Acceptance rate**: 0.944
- **Quality gap**: 0.221

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260222-211635_evo_game_prisoners_seed42/csv/evo_game_prisoners_epochs.csv`

## Reproduction

```bash
python -m swarm run evo_game_prisoners --seed 42
```

---

Topics:
- [[_index]]

<!-- topics: evo-game, prisoners-dilemma, seed-42, single -->
