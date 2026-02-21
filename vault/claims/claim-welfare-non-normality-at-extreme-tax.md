---
description: Welfare distributions are non-normal at 0% and 10% tax (Shapiro-Wilk p<0.01), suggesting regime bifurcation
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: welfare
    detail: "Shapiro-Wilk: tax=0% W=0.92 p=0.01; tax=10% W=0.87 p=0.0003; tax=5% W=0.97 p=0.35 (normal). Non-normality at extremes suggests bimodal distributions"
  weakening: []
  boundary_conditions:
  - N=40 per tax level (pooled across penalty levels)
  - Non-normality does not prove bimodality; could be skew or outliers
  - Parametric tests (t-tests, Cohen's d) assume normality; violations may affect other claims
sensitivity:
  topology: untested
  agent_count: untested
  governance_interaction: non-normality most severe at highest tax, where governance stress is maximal
supersedes: []
superseded_by: []
related_claims:
- claim-tax-phase-transition
- claim-tax-welfare-tradeoff
created: 2026-02-20
updated: 2026-02-20
aliases:
- welfare-non-normality-at-extreme-tax
cssclasses:
- claim
- claim-low
tags:
- governance
- transaction-tax
- methodology
- distributional
- open-question
graph-group: claim
---

# welfare distributions are non-normal at extreme tax rates suggesting ecosystem regime bifurcation

## Evidence summary

In the [[20260213-221500_collusion_tax_effect]] sweep, Shapiro-Wilk normality tests on welfare distributions by tax level reveal:

| Tax rate | W statistic | p-value | Normal? |
|----------|-------------|---------|---------|
| 0% | 0.92 | 0.01 | No |
| 2% | 0.94 | 0.03 | No |
| 5% | 0.97 | 0.35 | Yes |
| 10% | 0.87 | 0.0003 | No |

The most extreme non-normality occurs at 10% tax (W=0.87), suggesting the welfare distribution may be bimodal or heavy-tailed. This pattern is consistent with ecosystem bifurcation — some simulation runs collapse into a low-cooperation regime while others maintain moderate cooperation, producing a mixture distribution rather than a single normal.

This has methodological implications: the parametric tests used throughout the collusion_tax_effect analysis assume normality. The [[claim-tax-phase-transition]] findings may understate the true complexity of the welfare response to taxation.

## Open questions

- Plot kernel density estimates for each tax level to visually assess bimodality
- Run non-parametric alternatives (Mann-Whitney U) and compare with parametric results
- Does the non-normality correlate with specific penalty levels (interaction effect)?
- If bifurcation is real, can initial conditions predict which regime a run enters?

---

Topics:
- [[_index]]

<!-- topics: governance, transaction-tax, methodology, distributional, open-question -->
