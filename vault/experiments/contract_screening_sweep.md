---
description: 10-seed contract screening sweep confirms perfect separation (1.0) and ~0.32 toxicity rate with 213-232 mean welfare
type: experiment
status: completed
run_id: contract_screening_sweep
experiment_type: sweep
created: '2026-02-21'
aliases:
- contract_screening_sweep
cssclasses:
- experiment
- experiment-sweep
tags:
- contract-screening
- screening-equilibrium
- multi-seed
graph-group: experiment
---

# contract screening sweep across 10 seeds confirms perfect type separation with stable welfare and moderate toxicity

## Design

- **Hypothesis**: Contract screening type separation and welfare outcomes are robust across seeds
- **Type**: Parameter sweep (seed-only)
- **Seeds**: [43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
- **Total runs**: 10
- **Parent run**: [[contract_screening_seed42]]

## Key results

### Summary statistics across 10 seeds

| Metric | Mean | SD | Min | Max |
|--------|------|----|-----|-----|
| Welfare | 219.00 | 10.62 | 201.61 | 232.54 |
| Welfare per epoch | 10.95 | 0.53 | 10.08 | 11.63 |
| Toxicity rate | 0.321 | 0.006 | 0.313 | 0.332 |
| Total interactions | 253.2 | 9.5 | 239 | 267 |
| Accepted interactions | 243.2 | 10.1 | 224 | 256 |
| Separation quality | **1.0** | 0.0 | 1.0 | 1.0 |
| Infiltration rate | **0.0** | 0.0 | 0.0 | 0.0 |
| Quality gap | 0.016 | 0.012 | -0.014 | 0.031 |

### Perfect separation is robust

Separation quality = 1.0 across all 10 seeds, with zero infiltration. This confirms that the screening mechanism achieves perfect type separation deterministically, not by chance. This is a strong result because it holds across 10 independent random seeds controlling interaction order and payoff noise.

### Payoff hierarchy by agent type

| Agent Type | Mean Payoff | SD |
|------------|-------------|-----|
| Honest | 28.52 | 2.71 |
| Opportunistic | 22.62 | 2.12 |
| Deceptive | 4.27 | 0.95 |

Honest agents earn 6.7x more than deceptive agents (28.52 vs 4.27) across all seeds, confirming that the screening mechanism creates strong incentive alignment. The honest-opportunistic gap (28.52 vs 22.62, d=2.42) is also substantial.

### Pool-level welfare

| Pool | Mean Welfare | Seeds with Data |
|------|-------------|-----------------|
| truthful_auction | 1.186 | 10/10 |
| fair_division | 0.427 | 3/10 |
| default_market | 0.574 | 10/10 |

The truthful_auction pool consistently produces the highest per-interaction welfare. The fair_division pool only has measurable welfare in 3 of 10 seeds, suggesting opportunistic agents sometimes interact entirely across pool boundaries.

### Toxicity remains moderate

Toxicity rate averages 0.321 (SD=0.006), indicating that ~32% of interactions are classified as toxic. This baseline toxicity likely reflects cross-pool interactions where type-mismatched agents exploit information asymmetries.

## Claims affected

- Supports: [[claim-contract-screening-achieves-perfect-type-separation]] — 1.0 separation across 10 seeds
- Supports: [[claim-screening-equilibrium-generates-honest-payoff-premium]] — honest 6.7x deceptive, d=2.42 vs opportunistic

## Artifacts

- CSV: `runs/contract_screening_sweep/sweep_results.csv`
- Plots: `runs/contract_screening_sweep/plots/`

## Reproduction

```bash
python -m swarm sweep contract_screening --seeds 43-52
```

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: contract-screening, screening-equilibrium, multi-seed, mechanism-design -->
