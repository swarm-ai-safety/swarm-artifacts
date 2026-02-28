---
description: LDT agents earn 3x honest, 2.3x opportunistic, 9.3x adversarial payoff in heterogeneous population with all Bonferroni corrections surviving
type: claim
status: active
confidence: high
domain: agent-behavior
evidence:
  supporting:
  - run: 20260211-004234_analysis_ldt_cooperation
    metric: payoff
    detail: "LDT mean=31.36 vs honest=10.28 (d=6.54, p<1e-11), opportunistic=13.36 (d=4.21, p<1e-8), adversarial=3.38 (d=10.24, p<1e-14). All Bonferroni-sig. 10 seeds, 7 agents (3 LDT, 2 honest, 1 opp, 1 adv). ANOVA F=132.68, p<1e-19"
  weakening: []
  boundary_conditions:
  - "7-agent population with LDT majority (43%) — LDT advantage may depend on critical mass"
  - "No governance mechanisms — pure agent interaction dynamics"
  - "LDT config: cooperation_prior=0.65, similarity_threshold=0.7, welfare_weight=0.3, updateless_commitment=0.8"
  - "Honest vs opportunistic NOT significant (d=-0.82, p=0.082) — non-LDT types are statistically equivalent"
  - "Gini=0.4243 — highest inequality among all RLM/LDT experiments, driven by LDT dominance"
  - "10 seeds with fixed a priori selection"
sensitivity:
  topology: untested
  agent_count: 7 agents only
  ldt_fraction: 43% (3/7) — below or above may differ
  governance_interaction: untested — governance may reduce LDT advantage
supersedes: []
superseded_by: []
related_claims:
- claim-ldt-agents-provide-welfare-stability-at-intermediate-composition
- claim-acausality-depth-does-not-affect-cooperation-outcomes
- claim-smarter-agents-earn-less
- claim-agent-architecture-constrains-behavior-more-than-governance
created: 2026-02-27
updated: 2026-02-27
aliases:
- ldt-dominance-mixed-population
cssclasses:
- claim
- claim-high
tags:
- agent-behavior
- ldt
- cooperation
- decision-theory
graph-group: claim
---

# LDT agents dominate all agent types in heterogeneous populations through logical cooperation

## Evidence summary

The [[20260211-004234_analysis_ldt_cooperation]] analysis (10 seeds, 7 agents per seed) tests LDT agents against a heterogeneous population with honest, opportunistic, and adversarial agents:

| Agent Type | Mean Payoff | Std | n |
|-----------|------------|-----|---|
| LDT (3 agents) | 31.36 | 3.84 | 3 |
| Opportunistic (1 agent) | 13.36 | 4.68 | 1 |
| Honest (2 agents) | 10.28 | 2.47 | 2 |
| Adversarial (1 agent) | 3.38 | 0.46 | 1 |

All pairwise comparisons involving LDT survive Bonferroni correction (7/8 tests significant, only honest-vs-opportunistic fails at p=0.082).

## Mechanism

LDT agents cooperate through logical correlation — they reason about what similar algorithms would do and coordinate without explicit communication. This produces:

1. **3.1x payoff premium** over honest agents (d=6.54)
2. **2.3x payoff premium** over opportunistic agents (d=4.21)
3. **9.3x payoff premium** over adversarial agents (d=10.24)

## Relationship to composition studies

This complements [[claim-ldt-agents-provide-welfare-stability-at-intermediate-composition]], which shows LDT welfare benefits scale with 40-70% composition. The current finding establishes LDT dominance even at 43% composition (3/7 agents), consistent with the intermediate composition sweet spot.

## Non-LDT type equivalence

Honest and opportunistic agents are NOT statistically distinguishable (p=0.082). The payoff hierarchy is: LDT >> {honest, opportunistic} >> adversarial. This suggests LDT cooperation creates a qualitatively different behavioral regime, not just a marginal improvement.

## Inequality concern

Gini coefficient of 0.4243 is the highest across all agent architecture experiments, driven entirely by LDT dominance. LDT cooperation is efficient but deeply inequitable.

---

Topics:
- [[_index]]
- [[agent-behavior-dashboard]]

<!-- topics: agent-behavior, ldt, cooperation, decision-theory -->
