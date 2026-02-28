---
description: Single baseline run of evo_game_prisoners_seed999, final welfare=34.2
type: experiment
status: completed
run_id: 20260222-220608_evo_game_prisoners_seed999
experiment_type: single
created: '2026-02-22'
---

# single-run baseline with welfare=34.2 (evo game prisoners seed999)

## Design

- **Type**: Single run
- **Scenario**: evo_game_prisoners
- **Seed**: 999
- **Epochs**: 10
- **Steps per epoch**: 5
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 34.239
- **Toxicity rate**: 0.246
- **Acceptance rate**: 1.000
- **Quality gap**: 0.000

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260222-220608_evo_game_prisoners_seed999/csv/evo_game_prisoners_epochs.csv`

## Reproduction

```bash
python -m swarm run evo_game_prisoners --seed 999
```

---

Topics:
- [[_index]]

<!-- topics: evo-game, prisoners-dilemma, seed-999, single -->
