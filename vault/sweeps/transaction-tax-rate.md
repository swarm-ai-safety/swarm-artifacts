---
description: "All runs exploring transaction tax sensitivity across governance configs"
type: sweep-summary
status: active
parameter: "governance.transaction_tax_rate"
created: 2026-02-10
updated: 2026-02-19
---

## Runs in this sweep

| Run ID | Date | Seeds | Tax levels | CB states | Key finding |
|--------|------|-------|------------|-----------|-------------|
| 20260213-173805_baseline_governance | Feb 13 | 10 | 4 | 2 | d=0.95, sig |
| 20260213-202050_baseline_governance_v2 | Feb 13 | 50 | 7 | 2 | d=1.18, sig |
| 20260213-221500_collusion_tax_effect | Feb 13 | 10 | 4 | — | d=6.02 on RLM payoff |
| 20260212-015027_kernel_market_v4_code | Feb 12 | 5 | 4 | 2 | d=1.14-1.59, CB null |

## Convergence

The tax-welfare effect is robust across all runs and domains:
- Baseline governance: d=0.95 (v1, N=280) → d=1.18 (v2, N=700), narrowed CIs
- Kernel market: d=1.14-1.59, step-function at 5-10% boundary
- Collusion context: d=6.02 on RLM payoff (massive effect)

## Phase transition surface

Tax threshold for significant welfare loss: ~5% (below this, effect negligible).
Sharp phase transition between 5-10% where small increment causes disproportionate welfare collapse.
Circuit breakers partially compensate above 7.5% in baseline topology but show null effect in kernel markets.

<!-- topics: governance, transaction-tax, sweep-series -->
