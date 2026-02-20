---
description: "Seed robustness testing for RLM recursive collusion scenario"
type: sweep-summary
status: active
parameter: "simulation.seed"
created: 2026-02-10
updated: 2026-02-19
---

## Runs in this sweep

| Run ID | Date | Seed | Welfare | Toxicity | Acceptance |
|--------|------|------|---------|----------|------------|
| 20260210-211721_rlm_recursive_collusion_seed42 | Feb 10 | 42 | ~125 | ~0.35 | 1.0 |
| 20260210-211753_rlm_recursive_collusion_seed7 | Feb 10 | 7 | ~125 | ~0.35 | 1.0 |
| 20260210-211757_rlm_recursive_collusion_seed123 | Feb 10 | 123 | ~125 | ~0.35 | 1.0 |
| 20260210-211800_rlm_recursive_collusion_seed256 | Feb 10 | 256 | ~125 | ~0.35 | 1.0 |
| 20260210-211803_rlm_recursive_collusion_seed999 | Feb 10 | 999 | ~125 | ~0.35 | 1.0 |

Parent sweep: 20260210-212120_rlm_collusion_sweep
Analysis: 20260210-215826_analysis_rlm_recursive_collusion

## Convergence

Results highly robust to seed choice. Welfare, toxicity, and acceptance rate are essentially deterministic for this scenario configuration. Quality gap is 0.0 across all seeds (all interactions accepted).

## Implications

RLM recursive collusion scenario produces consistent outcomes regardless of random seed, suggesting the dynamics are dominated by agent strategies rather than stochastic effects.

<!-- topics: rlm, collusion, seed-robustness, sweep-series -->
