---
description: Welfare non-normality at N=40 does not replicate at N=100 (all Shapiro-Wilk p>0.05 Bonferroni-corrected) — likely underpowering artifact
type: claim
status: weakened
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: welfare
    detail: "At N=40 (pooled across penalties): Shapiro-Wilk tax=0% W=0.92 p=0.01; tax=10% W=0.87 p=0.0003; tax=5% W=0.97 p=0.35"
  weakening:
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: "At N=100 per tax level (v2 sweep, 7 tax levels x 50 seeds): Shapiro-Wilk with Bonferroni correction (alpha=0.05/7=0.0071) — ALL 7 groups pass normality. Non-normality at N=40 was likely underpowering artifact"
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
- claim-tax-disproportionately-punishes-rlm-agents
- claim-tax-penalty-interaction-on-toxicity-uncharacterized
- claim-collusion-penalty-destabilizes
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

# welfare non-normality at extreme tax does not replicate at higher sample sizes

## Evidence summary

In the [[20260213-221500_collusion_tax_effect]] sweep at N=40 per tax level (pooled across penalties), Shapiro-Wilk tests suggested non-normality at 0% and 10% tax:

| Tax rate | W statistic | p-value | Normal? |
|----------|-------------|---------|---------|
| 0% | 0.92 | 0.01 | No |
| 2% | 0.94 | 0.03 | No |
| 5% | 0.97 | 0.35 | Yes |
| 10% | 0.87 | 0.0003 | No |

**However**, formal replication at N=100 per tax level in the [[20260213-202050_baseline_governance_v2]] sweep (700 runs, 7 tax levels x 2 CB x 50 seeds) with Bonferroni correction (alpha=0.05/7=0.0071) shows **all 7 tax levels pass normality**. The non-normality finding at N=40 was likely an underpowering artifact — Shapiro-Wilk is known to be sensitive to small sample sizes while simultaneously lacking power to detect true non-normality at N=40.

This **weakens** the original claim and its methodological implications. The parametric tests (Cohen's d, t-tests) used in [[claim-tax-welfare-tradeoff]] and [[claim-tax-phase-transition]] are not invalidated by normality violations, as the underlying distributions appear normal at adequate sample sizes. The bifurcation hypothesis remains interesting but lacks statistical support.

## Open questions

- Plot kernel density estimates for each tax level to visually assess bimodality
- Run non-parametric alternatives (Mann-Whitney U) and compare with parametric results
- Does the non-normality correlate with specific penalty levels (interaction effect)? This connects to [[claim-tax-penalty-interaction-on-toxicity-uncharacterized]] — the extreme cell (tax=10%, penalty=2.0x) may show the strongest non-normality
- If bifurcation is real, can initial conditions predict which regime a run enters?
- The non-normality at 0% tax is unexpected — [[claim-collusion-penalty-destabilizes]] may explain this if penalty variation alone creates bimodal welfare distributions even without tax

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[transaction-tax-rate]]

<!-- topics: governance, transaction-tax, methodology, distributional, open-question -->
