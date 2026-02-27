---
description: 5-seed evolutionary prisoners dilemma shows weak toxicity reduction over 10 epochs (0.291→0.263) with non-monotonic extended dynamics
type: experiment
status: completed
run_id: 20260222-215017_evo_game_prisoners_seed42
experiment_type: study
created: '2026-02-27'
aliases:
- evo_game_prisoners
cssclasses:
- experiment
- experiment-study
tags:
- evolutionary-game
- prisoners-dilemma
- cooperation
- multi-seed
graph-group: experiment
---

# evolutionary prisoners dilemma shows weak selection for cooperation that does not eliminate toxicity even over 20 epochs

## Design

- **Hypothesis**: Evolutionary selection pressure in iterated prisoner's dilemma reduces toxicity and favors cooperative agent strategies
- **Type**: Multi-seed single study + extended-epoch replication
- **Seeds**: [42, 123, 314, 777, 999] (10 epochs each) + seed 42 extended to 20 epochs
- **Total runs**: 7 (5 base + 1 duplicate + 1 extended)
- **Config**: 10 agents, 5 steps per epoch, prisoner's dilemma scenario
- **Note**: runs 20260222-211635 and 20260222-215017 (both seed 42) produce identical results — duplicate runs

## Key results

### Toxicity declines weakly over 10 epochs

Mean toxicity across 5 seeds decreases from 0.291 (epoch 0) to 0.263 (epoch 9), a reduction of 9.6%. However, the trajectory is non-monotonic — toxicity peaks at epoch 1 (0.355) before declining, and the decline is modest relative to the variance across seeds.

| Epoch | Toxicity (mean ± SD) |
|-------|---------------------|
| 0 | 0.291 ± 0.021 |
| 1 | 0.355 ± 0.076 |
| 5 | 0.285 ± 0.029 |
| 9 | 0.263 ± 0.019 |

### Extended run shows non-monotonic dynamics

The 20-epoch run (seed 42) shows toxicity reaching a minimum at epoch 15 (0.252) then rising back to 0.293 at epoch 19. This suggests evolutionary dynamics may oscillate rather than converge, consistent with known cyclic dynamics in evolutionary game theory (rock-paper-scissors-like oscillations between strategies).

### Final-epoch aggregate statistics (N=5 seeds)

| Metric | Mean ± SD |
|--------|-----------|
| Toxicity | 0.263 ± 0.019 |
| Total welfare | 24.95 ± 7.61 |
| Avg quality (p) | 0.729 ± 0.018 |
| Gini coefficient | 0.091 ± 0.024 |
| Avg payoff | 0.949 ± 0.039 |

### Payoff inequality is low

Gini coefficients range from 0.069 to 0.124, indicating relatively egalitarian payoff distribution. Evolutionary selection does not produce winner-take-all dynamics in this prisoner's dilemma setting.

## Claims affected

- **New**: [[claim-evolutionary-selection-weakly-reduces-toxicity-in-prisoners-dilemma]] — 9.6% reduction over 10 epochs, non-monotonic, not sustained at 20 epochs

## Artifacts

- History: `runs/20260222-215017_evo_game_prisoners_seed42/history.json` (and 4 other seeds)
- CSV: `runs/20260222-215017_evo_game_prisoners_seed42/csv/evo_game_prisoners_epochs.csv`
- Extended: `runs/20260223-001025_evo_game_prisoners_seed42_20ep/history.json`
- Plots: `runs/20260222-215017_evo_game_prisoners_seed42/plots/`

## Reproduction

```bash
python -m swarm single evo_game_prisoners --seeds 42,123,314,777,999 --epochs 10 --steps-per-epoch 5
python -m swarm single evo_game_prisoners --seed 42 --epochs 20 --steps-per-epoch 5
```

---

Topics:
- [[_index]]

<!-- topics: evolutionary-game, prisoners-dilemma, cooperation, agent-behavior -->
