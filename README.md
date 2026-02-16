# swarm-artifacts

Supplementary artifacts for [SWARM](https://github.com/swarm-ai-safety/swarm) — experiment runs, formal proofs, promotional site, research notes, and reference papers.

These files were moved out of the main repository to reduce clone size and keep the core codebase focused on the simulation framework.

## Contents

| Directory | Description |
|-----------|-------------|
| `runs/` | Experiment run outputs (CSVs, history JSON, plots). Reproducible from scenario YAML + seed. |
| `lean/` | Lean 4 formal verification proofs (SwarmProofs) |
| `promo/` | React/TypeScript promotional site (Revelator scenes, animations) |
| `research/` | Investigation notes, analysis, and external submissions |
| `papers/` | Reference papers (formerly `docs/papers/` in main repo) |

## Reproducing runs

Runs can be regenerated from the main repo:

```bash
python -m swarm run scenarios/baseline.yaml --seed 42 --epochs 10 --steps 10
```

The artifacts here are kept for reference and to support paper reproducibility.
