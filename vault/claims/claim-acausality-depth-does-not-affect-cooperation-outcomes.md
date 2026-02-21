---
description: Two independent LDT studies (N=30 each) find zero Bonferroni-significant effects of acausality depth 1-3 on welfare, toxicity, or payoffs
type: claim
status: active
confidence: medium
domain: agent-behavior
evidence:
  supporting:
  - run: 20260212-231859_ldt_acausality_study
    metric: welfare
    detail: "Depth 1: 125.07, Depth 2: 132.16, Depth 3: 127.72. Largest effect d=-0.865 (depth 1 vs 2), p=0.069. 0/15 tests Bonferroni-significant. N=10 seeds per depth, 7 agents, pre-registered"
  - run: 20260213-003757_ldt_large_population_study
    metric: welfare
    detail: "Depth 1: 366.38, Depth 2: 371.41, Depth 3: 387.68. Largest effect d=-1.17 (depth 1 vs 3), p=0.018. 3/15 nominally significant, 0/15 Bonferroni-significant. N=10 seeds per depth, large population scenario"
  weakening: []
  boundary_conditions:
  - "Both studies use 10 seeds per condition — adequately powered for large effects but may miss small effects"
  - "Acausality depth range limited to 1-3; deeper reasoning may behave differently"
  - "ldt_cooperation and large_population scenarios only; untested in adversarial or governance-heavy contexts"
sensitivity:
  topology: untested
  agent_count: tested at 7 (standard) and large population — consistent null
  governance_interaction: no governance mechanisms in LDT studies
supersedes: []
superseded_by: []
related_claims:
- claim-smarter-agents-earn-less
- claim-rlhf-persona-invariant
created: 2026-02-21
updated: 2026-02-21
aliases:
- acausality-depth-does-not-affect-cooperation-outcomes
cssclasses:
- claim
- claim-medium
tags:
- agent-behavior
- acausality
- ldt
- null-result
graph-group: claim
---

# Acausality depth (1-3) does not significantly affect cooperation outcomes in LDT scenarios

## Evidence summary

Two pre-registered LDT studies tested whether deeper acausal reasoning (modeling of counterparty reasoning chains) improves cooperation outcomes. Neither found Bonferroni-significant effects across any metric.

**Standard scale** ([[20260212-231859_ldt_acausality_study]], 7 agents, 30 runs): Depth 2 showed nominally higher welfare (132.16 vs 125.07 at depth 1, d=-0.865) and lower toxicity (0.326 vs 0.336, d=0.849), but neither survived correction (0/15 Bonferroni-significant). All pairwise comparisons across welfare, toxicity, quality gap, honest payoff, and adversarial payoff were non-significant.

**Large population** ([[20260213-003757_ldt_large_population_study]], 30 runs): Depth 3 showed nominally higher welfare (387.68 vs 366.38 at depth 1, d=-1.17, p=0.018) and honest payoff (24.57 vs 22.47, d=-1.25, p=0.013). Three tests reached nominal significance but zero survived Bonferroni correction (threshold p<0.003 for 15 tests).

The consistency of null results across two independent studies with different population sizes strengthens the conclusion. This aligns with [[claim-smarter-agents-earn-less]] — additional reasoning capacity does not translate into better outcomes, and may be irrelevant below some threshold. The null also parallels [[claim-rlhf-persona-invariant]], where architectural variation (RLHF training) similarly failed to affect behavioral outcomes.

## Mechanism (hypothesized)

In the LDT cooperation scenario, the strategic landscape may be simple enough that depth-1 reasoning already captures the relevant counterparty dynamics. Deeper reasoning chains (depth 2-3) provide no additional strategic advantage because the game structure doesn't reward multi-step reasoning about reasoning. Alternatively, the acausality implementation may not effectively differentiate depths at the behavioral level.

## Open questions

- Does acausality depth matter at depths >3?
- Would adversarial LDT scenarios (with higher strategic complexity) reveal depth effects?
- Is the null result specific to the LDT cooperation game structure, or general?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: agent-behavior, acausality, ldt, null-result -->
