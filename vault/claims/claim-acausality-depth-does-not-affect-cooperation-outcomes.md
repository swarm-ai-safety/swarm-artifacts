---
description: Seven LDT studies across 5 scenarios find zero Bonferroni-significant effects of acausality depth or decision theory on outcomes
type: claim
status: active
confidence: high
domain: agent-behavior
evidence:
  supporting:
  - run: 20260212-231859_ldt_acausality_study
    metric: welfare
    detail: "Depth 1: 125.07, Depth 2: 132.16, Depth 3: 127.72. Largest effect d=-0.865 (depth 1 vs 2), p=0.069. 0/15 tests Bonferroni-significant. N=10 seeds per depth, 7 agents, pre-registered"
  - run: 20260213-003757_ldt_large_population_study
    metric: welfare
    detail: "Depth 1: 366.38, Depth 2: 371.41, Depth 3: 387.68. Largest effect d=-1.17 (depth 1 vs 3), p=0.018. 3/15 nominally significant, 0/15 Bonferroni-significant. N=10 seeds per depth, large population scenario"
  - run: 20260213-013951_ldt_decision_theory_study
    metric: welfare
    detail: "TDT vs FDT vs UDT: 0/15 Bonferroni-significant, 0/15 nominally significant. Largest d=-0.865 (TDT vs FDT welfare). N=10 seeds per DT, 7 agents. Decision theory choice also irrelevant"
  - run: 20260213-101646_ldt_large_pop_dt_study
    metric: welfare
    detail: "TDT vs FDT vs UDT at large pop: 0/15 Bonferroni-sig, 3/15 nominal. UDT welfare nominally higher (387.68 vs TDT 366.38, d=-1.17, p=0.018). N=10 seeds per DT, 21 agents"
  - run: 20260213-003804_ldt_modeling_adversary_study
    metric: welfare
    detail: "Acausality depth 1-3 in modeling_adversary scenario: 0/15 Bonferroni-sig, 0/15 nominal. N=10 seeds per depth"
  - run: 20260213-003812_ldt_low_prior_study
    metric: welfare
    detail: "Acausality depth 1-3 in low_prior scenario: 0/15 Bonferroni-sig, 0/15 nominal. Largest d=-0.846 (depth 1 vs 2), p=0.075. N=10 seeds per depth"
  - run: 20260213-003819_ldt_short_horizon_study
    metric: welfare
    detail: "Acausality depth 1-3 in short_horizon scenario: 0/15 Bonferroni-sig, 0/15 nominal. Largest d=-0.755 (depth 1 vs 2 welfare), p=0.109. N=10 seeds per depth"
  weakening: []
  boundary_conditions:
  - "All studies use 10 seeds per condition — adequately powered for large effects but may miss small effects"
  - "Acausality depth range limited to 1-3; deeper reasoning may behave differently"
  - "7 LDT studies across 5 scenarios (cooperation, large_pop, modeling_adversary, low_prior, short_horizon) — broad scenario coverage"
  - "Decision theory variant (TDT/FDT/UDT) also shows no effect, generalizing beyond depth to reasoning framework"
sensitivity:
  topology: untested
  agent_count: tested at 7 (standard) and 21 (large population) — consistent null
  governance_interaction: no governance mechanisms in LDT studies
supersedes: []
superseded_by: []
related_claims:
- claim-smarter-agents-earn-less
- claim-rlhf-persona-invariant
- claim-agent-architecture-constrains-behavior-more-than-governance
created: 2026-02-21
updated: 2026-02-21
aliases:
- acausality-depth-does-not-affect-cooperation-outcomes
cssclasses:
- claim
- claim-high
tags:
- agent-behavior
- acausality
- ldt
- null-result
graph-group: claim
---

# Neither acausality depth nor decision theory variant significantly affects cooperation outcomes in LDT scenarios

## Evidence summary

Seven pre-registered LDT studies across 5 scenarios tested whether deeper acausal reasoning (depth 1-3) or decision theory variant (TDT/FDT/UDT) improves cooperation outcomes. None found Bonferroni-significant effects on any metric. Combined: 0/105 tests Bonferroni-significant, 6/105 nominally significant (consistent with chance at alpha=0.05).

**Acausality depth** (5 studies): Tested across cooperation ([[20260212-231859_ldt_acausality_study]]), large_population ([[20260213-003757_ldt_large_population_study]]), modeling_adversary ([[20260213-003804_ldt_modeling_adversary_study]]), low_prior ([[20260213-003812_ldt_low_prior_study]]), and short_horizon ([[20260213-003819_ldt_short_horizon_study]]). Largest effects are medium-sized (d~0.85-1.17) but none survive correction. The null is consistent across all 5 scenarios.

**Decision theory** (2 studies): TDT vs FDT vs UDT tested at standard ([[20260213-013951_ldt_decision_theory_study]]) and large population ([[20260213-101646_ldt_large_pop_dt_study]]) scales. 0/30 Bonferroni-significant. UDT shows nominal welfare advantage at large scale (d=-1.17, p=0.018) but this does not survive correction.

The breadth and consistency of nulls across 7 studies, 5 scenarios, and 210 total runs makes this one of the most robustly established null findings in the vault. This aligns with [[claim-smarter-agents-earn-less]] — additional reasoning capacity does not translate into better outcomes. The null also parallels [[claim-rlhf-persona-invariant]], where architectural variation similarly failed to affect behavioral outcomes.

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
