---
description: LLM-mutated evolutionary search reaches 80% of final fitness by iteration 5 regardless of budget (5, 20, or 50 iters)
type: claim
status: active
confidence: medium
domain: governance-calibration
evidence:
  supporting:
  - run: 20260227_222203_evolve_baseline
    metric: fitness_score
    detail: "5-iteration run: score 0.398 → 0.716 (+0.318). 91 evaluations. Final score 0.693 at final eval (10 ep x 10 steps). LLM mutator: claude-sonnet-4-20250514"
  - run: 20260227_222439_evolve_baseline
    metric: fitness_score
    detail: "20-iteration run: score 0.398 → 0.741 (+0.343). 361 evaluations. Final eval score 0.693. Marginal gain from iters 5-20 is only +0.025"
  - run: 20260228_093125_evolve_baseline
    metric: fitness_score
    detail: "50-iteration run: score 0.397 → 0.726 (+0.329). 901 evaluations. Final eval score 0.693. Plateau reached by iteration 5, no meaningful improvement in 45 additional iterations"
  weakening: []
  boundary_conditions:
  - "Single seed base (42) per run — no cross-seed replication of convergence speed"
  - "Baseline scenario only — convergence dynamics may differ for other scenarios"
  - "LLM mutator (Claude Sonnet 4) — convergence speed depends on mutator quality"
  - "3 parents per iteration — different parent counts may shift convergence"
  - "Final eval scores near-identical (0.693) despite different iteration counts, suggesting a fitness ceiling"
sensitivity:
  topology: untested
  agent_count: untested
  mutator_model: "claude-sonnet-4-20250514 only — different LLMs may produce different convergence dynamics"
supersedes: []
superseded_by: []
related_claims:
- claim-evolutionary-governance-optimization-favors-high-audit-high-penalty-regimes
- claim-evolutionary-selection-weakly-reduces-toxicity-in-prisoners-dilemma
- claim-tax-welfare-tradeoff
- claim-circuit-breakers-dominate
- claim-freeze-duration-and-violation-threshold-interact-on-welfare
created: 2026-02-28
updated: 2026-02-28
aliases:
- evo-convergence-speed
cssclasses:
- claim
- claim-medium
tags:
- evolutionary-optimization
- llm-mutator
- convergence
- governance-calibration
graph-group: claim
---

# LLM-guided evolutionary optimization converges to near-optimal governance within 5 iterations

## Evidence summary

Three independent evolutionary optimization runs on the baseline scenario — with 5, 20, and 50 iteration budgets — all converge to nearly identical final evaluation scores (~0.693) despite order-of-magnitude differences in compute budget:

| Run | Iterations | Evaluations | Final eval score | Toxicity | Welfare |
|-----|-----------|-------------|-----------------|----------|---------|
| [[20260227_222203_evolve_baseline]] | 5 | 91 | 0.6933 | 0.305 | 25.22 |
| [[20260227_222439_evolve_baseline]] | 20 | 361 | 0.6928 | 0.306 | 28.03 |
| [[20260228_093125_evolve_baseline]] | 50 | 901 | 0.6928 | 0.306 | 30.12 |

The 50-iteration population log shows that 80% of the fitness improvement (from 0.397 to 0.618) occurs in iteration 1 alone. By iteration 5, the best score reaches ~0.693, and the remaining 45 iterations provide only marginal improvement in population distribution (median score rises from 0.40 to 0.62) without improving the best organism.

This suggests the LLM mutator is effective at quickly identifying high-fitness governance parameter regions but struggles to escape local optima. The rapid convergence is consistent with the hypothesis that the governance fitness landscape has a single dominant basin of attraction under this fitness function.

## Cross-run parameter analysis

Despite converging to similar fitness scores, the three runs find **different optimal parameter sets**:

| Parameter | 5-iter | 20-iter | 50-iter |
|-----------|--------|---------|---------|
| audit_probability | 0.6 | 0.6 | **0.9** |
| audit_penalty_multiplier | 6.0 | 4.0 | **9.5** |
| stake_slash_rate | 0.4 | 0.5 | **0.8** |
| freeze_threshold_toxicity | 0.1 | 0.25 | **0.06** |
| transaction_tax_rate | 0.15 | 0.1 | **0.18** |
| w_rep | 7.0 | 3.0 | **8.5** |

The 50-iteration run's best organism is consistently more aggressive: higher audit probability (0.9 vs 0.6), higher penalty multiplier (9.5 vs 4-6), tighter freeze threshold (0.06 vs 0.1-0.25), and higher stake slashing (0.8 vs 0.4-0.5). Yet all three achieve nearly identical fitness scores, suggesting a flat ridge in the governance fitness landscape where multiple parameter combinations yield equivalent performance.

## Mechanism

The LLM mutator (Claude Sonnet 4) generates parameter mutations by reasoning about governance mechanisms. Its rapid convergence to high-fitness regions likely reflects that LLM-guided search exploits semantic understanding of parameter relationships (e.g., "higher audit probability pairs with higher penalty") rather than random exploration. The flat fitness ridge means multiple governance "philosophies" (lenient vs aggressive) can achieve equivalent aggregate scores with different tradeoff profiles.

## Open questions

- Does the flat fitness ridge persist across different fitness weight vectors?
- Would a different LLM mutator (e.g., GPT-4, Gemini) converge to the same region or find different optima?
- Is the welfare difference (25 vs 30) between 5-iter and 50-iter meaningful, or an artifact of evaluation noise?
- Can the search be improved by adding diversity pressure (e.g., novelty search) to escape the apparent local optimum?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: evolutionary-optimization, llm-mutator, convergence, governance-calibration, parameter-sensitivity -->
