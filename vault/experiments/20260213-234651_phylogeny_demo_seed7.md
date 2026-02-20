---
description: Single baseline run of phylogeny_demo_seed7, final welfare=156.8
type: experiment
status: completed
run_id: 20260213-234651_phylogeny_demo_seed7
experiment_type: single
created: '2026-02-13'
aliases:
- 20260213-234651_phylogeny_demo_seed7
cssclasses:
- experiment
- experiment-single
tags:
- phylogeny
- seed-7
graph-group: experiment
---

# single-run baseline with welfare=156.8 (phylogeny demo seed7)

## Design

- **Type**: Single run
- **Scenario**: unknown
- **Seed**: 7
- **Epochs**: 20
- **Steps per epoch**: 20
- **Agents**: 50
- **SWARM version**: unknown @ `unknown`

## Key results

- **Welfare**: 156.805
- **Toxicity rate**: 0.327
- **Acceptance rate**: 0.924
- **Quality gap**: 0.153

## Claims affected

No claims with >=2 tag overlap found.

## Artifacts

- CSV: `runs/20260213-234651_phylogeny_demo_seed7/csv/phylogeny_demo_epochs.csv`
- Plot: `runs/20260213-234651_phylogeny_demo_seed7/plots/phylogeny.html`

## Reproduction

```bash
python -m swarm run unknown --seed 7
```

---

Topics:
- [[_index]]

<!-- topics: phylogeny, seed-7 -->
