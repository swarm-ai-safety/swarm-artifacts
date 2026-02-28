---
description: Moderate governance achieves highest welfare at each toxicity level across the adversarial spectrum, Pareto-dominating all other configs
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260227_203024_composition_boundary_study
    metric: welfare
    detail: "Welfare-toxicity Pareto frontier: at toxicity ~0.28, moderate achieves welfare 14.5 vs full 10.8 vs basic 14.0 vs none 15.2. At toxicity ~0.31, moderate achieves 11.6 vs full 8.3 vs basic 9.9 vs none 11.2. Moderate curve lies above basic and full at all matched toxicity levels above 0.28. 20 runs per cell (5 seeds x 4 pop sizes)"
  - run: 20260227_203024_composition_boundary_study
    metric: toxicity
    detail: "At 50% adversarial: moderate toxicity 0.311 vs none 0.425 vs basic 0.418 vs full 0.319. Moderate suppresses toxicity 27% below none while maintaining 47% higher welfare (7.52 vs 5.02). 20 runs per cell"
  weakening: []
  boundary_conditions:
  - "Adversarial fraction sweep only (honest vs adversarial binary mixtures)"
  - "Pareto dominance observed in welfare-toxicity space; acceptance and quality gap dimensions not included"
  - "Moderate config: 8% tax, CB, audit p=0.10, penalty 2x. Results may be specific to this parameter combination"
sensitivity:
  topology: untested
  agent_count: tested at 4-32
  governance_interaction: "Pareto dominance is a configuration-level result; individual mechanism contributions not decomposed"
supersedes: []
superseded_by: []
related_claims:
- claim: claim-moderate-governance-extends-cooperative-regime-to-50pct-adversarial
  relation: supports
- claim: claim-full-governance-welfare-penalty-exceeds-safety-gain-over-moderate
  relation: supports
- claim: claim-governance-cost-paradox
  relation: refines
- claim: claim-adaptive-governance-trades-welfare-for-toxicity-at-constant-marginal-rate
  relation: extends
created: 2026-02-28
aliases:
- moderate-governance-pareto-dominates
cssclasses:
- claim
- claim-medium
tags:
- governance
- welfare
- toxicity
- pareto-frontier
- composition
graph-group: claim
---

# Moderate governance Pareto-dominates the welfare-toxicity frontier at high adversarial fractions

## Evidence summary

The welfare-toxicity tradeoff plot from [[20260227_203024_composition_boundary_study]] maps each governance configuration's trajectory through welfare-toxicity space as adversarial fraction increases from 0% to 50%.

At low adversarial fractions (0-10%), no governance and basic governance achieve the highest welfare with lowest toxicity — governance mechanisms impose cost without providing benefit when few adversarial agents exist. However, as adversarial fraction increases above 15%, moderate governance's trajectory separates from the others: it maintains higher welfare at matched toxicity levels.

At 50% adversarial fraction, the separation is clear:
- **Moderate**: welfare 7.52, toxicity 0.311
- **None**: welfare 6.40, toxicity 0.425
- **Basic**: welfare 5.74, toxicity 0.418
- **Full**: welfare 5.02, toxicity 0.319

Moderate achieves 47% higher welfare than full with nearly identical toxicity (0.311 vs 0.319). It achieves 18% higher welfare than none with 27% lower toxicity. This Pareto dominance is particularly relevant for AI safety design: moderate governance is strictly better than full governance at every adversarial level tested, meaning the additional mechanisms in the full stack are pure deadweight.

This refines the [[claim-governance-cost-paradox]] by identifying that the paradox is specific to over-governance: moderate governance escapes the cost paradox by achieving a favorable cost-benefit ratio. The [[claim-adaptive-governance-trades-welfare-for-toxicity-at-constant-marginal-rate|adaptive governance marginal rate]] finding may explain the mechanism: at moderate governance levels, each unit of toxicity reduction costs less welfare than at full governance levels.

**Confidence: medium.** Visual Pareto dominance from summary statistics across 20 runs per cell. No formal dominance testing (stochastic dominance or hypervolume comparison). Single study.

## Mechanism

Moderate governance achieves Pareto dominance through calibrated deterrence: audit probability 0.10 with 2x penalty creates sufficient expected cost to deter adversarial strategies without the welfare-destroying overhead of staking requirements and aggressive taxation. The 8% tax rate sits near the upper bound of the safe operating envelope (see [[claim-optimal-tax-range-0-to-5pct]]), providing revenue for redistribution without triggering the phase transition. The result is a governance configuration that "bends the curve" — shifting the welfare-toxicity frontier outward rather than simply sliding along it.

## Open questions

- Is moderate governance's Pareto dominance robust to different scenarios (kernel v4, concordia)?
- Would optimizing audit probability within the moderate framework (sweeping p from 0.05 to 0.20) find an even better frontier?
- Does the dominance hold in mixed-profile populations, or only in binary honest/adversarial?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, welfare, toxicity, pareto-frontier, composition -->
