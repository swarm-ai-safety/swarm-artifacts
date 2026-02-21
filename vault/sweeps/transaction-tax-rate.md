---
description: All runs exploring transaction tax sensitivity across governance configs
type: sweep-summary
status: active
parameter: governance.transaction_tax_rate
created: 2026-02-10
updated: 2026-02-21
aliases:
- governance.transaction_tax_rate
- transaction-tax-rate
cssclasses:
- sweep-summary
tags:
- governance
- transaction-tax
- sweep-series
graph-group: sweep
---

## Runs in this sweep

| Run ID | Date | Seeds | Tax levels | CB states | Key finding |
|--------|------|-------|------------|-----------|-------------|
| 20260213-173805_baseline_governance | Feb 13 | 10 | 4 | 2 | d=0.95, sig |
| 20260213-202050_baseline_governance_v2 | Feb 13 | 50 | 7 | 2 | d=1.18, sig |
| 20260213-221500_collusion_tax_effect | Feb 13 | 10 | 4 | — | d=6.02 on RLM payoff |
| 20260212-015027_kernel_market_v4_code | Feb 12 | 5 | 4 | 2 | d=1.14-1.59, CB null |
| 20260213-143751_delegation_games_study | Feb 13 | 10 | 4 | 2 | d=1.56, sig |
| 20260210-213833_collusion_governance | Feb 10 | 10 | 4 | 2 | d=1.33, sig |
| 20260213-204503_agent_lab_research_safety_study | Feb 13 | 10 | 4 | 2 | d=0.80, sig |
| 20260210-223119_kernel_market_v2 | Feb 10 | 10 | varies | 2 | d=1.19, sig |

## Convergence

The tax-welfare effect is robust across 8 independent sweeps and 5 domains:
- Baseline governance: d=0.95 (v1, N=280) → d=1.18 (v2, N=700), narrowed CIs
- Kernel market: d=1.14-1.59 (v4), d=1.19 (v2), step-function at 5-10% boundary
- Collusion context: d=6.02 on RLM payoff (massive effect), d=1.33 welfare
- Delegation games: d=1.56, only Bonferroni-surviving comparison in 8-test battery
- Agent lab: d=0.80, Holm-significant in 160-run 4x2x2 factorial (CB and CD null)

## Phase transition surface

Tax threshold for significant welfare loss: ~5% (below this, effect negligible).
Sharp phase transition between 5-10% where small increment causes disproportionate welfare collapse.
Circuit breakers partially compensate above 7.5% in baseline topology but show null effect in kernel markets.
Tax disproportionately affects RLM agents (d=6.02 vs d=2.87 for honest agents) — see [[claim-tax-disproportionately-punishes-rlm-agents]].
High tax also increases toxicity by 0.6pp (d=-0.86) — see [[claim-high-tax-increases-toxicity]].
Welfare distributions are non-normal at extreme tax rates (0% and 10%) — see [[claim-welfare-non-normality-at-extreme-tax]].

<!-- topics: governance, transaction-tax, sweep-series -->
