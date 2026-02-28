---
description: Single baseline run of evo_game_prisoners_seed42_20ep, final welfare=28.8
type: experiment
status: completed
run_id: 20260223-001025_evo_game_prisoners_seed42_20ep
experiment_type: single
created: '2026-02-23'
---

# single-run baseline with welfare=28.8 (evo game prisoners seed42 20ep)

## Design

- **Type**: Single run
- **Scenario**: evo_game_prisoners
- **Seed**: 42
- **Epochs**: 20
- **Steps per epoch**: 5
- **Agents**: 10
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 28.774
- **Toxicity rate**: 0.293
- **Acceptance rate**: 0.952
- **Quality gap**: -0.011

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260223-001025_evo_game_prisoners_seed42_20ep/csv/evo_game_prisoners_epochs.csv`

## Reproduction

```bash
python -m swarm run evo_game_prisoners --seed 42
```

---

Topics:
- [[_index]]

<!-- topics: evo-game, prisoners-dilemma, seed-42, extended-epochs, single -->
