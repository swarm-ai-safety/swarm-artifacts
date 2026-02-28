---
description: Multi-condition study of mesa_governance_study (0 levels, None total
  runs)
type: experiment
status: completed
run_id: 20260224-220829_mesa_governance_study
experiment_type: study
created: '2026-02-24'
---

# mesa governance study study (None runs) finds 0 significant pairwise differences

## Design

- **Type**: Multi-condition study
- **Parameter**: `unknown`
- **Levels**: []
- **Seeds per config**: None
- **Total runs**: None
- **SWARM version**: unknown @ `unknown`

## Key results

### Descriptive statistics

No descriptive statistics available

### Pairwise comparisons

No pairwise tests available

## Claims affected

- [[claim-adaptive-acceptance-reduces-toxicity-monotonically-with-externality-internalization]] (medium) — adaptive-acceptance, externality-internalization, governance, mesa
- [[claim-adaptive-governance-trades-welfare-for-toxicity-at-constant-marginal-rate]] (medium) — governance, mesa
- [[claim-adaptive-learning-narrows-quality-gap-by-converting-selfish-agents]] (medium) — governance, mesa
- [[claim-game-structure-determines-optimal-governance-regime]] (medium) — governance, mesa
- [[claim-mesa-agent-objectives-are-invariant-to-governance-regime]] (medium) — governance, mesa
- [[claim-static-externality-tax-is-pure-deadweight-welfare-loss]] (medium) — governance, mesa

## Artifacts

- Summary: `runs/20260224-220829_mesa_governance_study/analysis/summary.json`
- Sweep CSV: `runs/20260224-220829_mesa_governance_study/sweep_results.csv`

## Reproduction

```bash
python -m swarm study mesa_bridge_governance --seeds None
```

---

Topics:
- [[_index]]

<!-- topics: mesa, governance, externality-internalization, adaptive-acceptance, toxicity-welfare-tradeoff, study, sweep -->
