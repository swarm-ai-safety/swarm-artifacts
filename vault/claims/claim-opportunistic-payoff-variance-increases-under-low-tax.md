---
description: Opportunistic payoff variance pattern at N=20 does not replicate — Levene's test at N=100 is null (F=1.01, p=0.42)
type: claim
status: weakened
confidence: low
domain: agent-behavior
evidence:
  supporting:
  - run: 20260213-173805_baseline_governance
    metric: opportunistic_payoff
    detail: "SD by tax rate: 0%=4.49, 5%=5.46, 10%=3.94, 15%=2.53. SD ratio 5%/15% = 2.16x. No formal Levene's test, N=20 per cell"
  weakening:
  - run: 20260213-202050_baseline_governance_v2
    metric: opportunistic_payoff
    detail: "Formal Levene's test across 7 tax levels (N=100 per level): F=1.01, p=0.42 — NULL. No significant variance heterogeneity detected at adequate sample size"
  boundary_conditions:
  - 5 agents, small-world topology, 10 seeds per cell
  - No formal heteroscedasticity test in the data
  - N=20 per cell is underpowered for variance estimation
  - Not replicated in v2 sweep (different agent count, seed count)
sensitivity:
  topology: untested beyond small-world
  agent_count: 5 agents; variance pattern may differ with more agents
  governance_interaction: CB has no effect on opportunistic payoff variance
supersedes: []
superseded_by: []
related_claims:
- claim-tax-hurts-honest-more-than-opportunistic
- claim-tax-welfare-tradeoff
- claim-welfare-non-normality-at-extreme-tax
- claim-tax-phase-transition
- claim-optimal-tax-range-0-to-5pct
- claim-welfare-plateaus-above-12pct-tax
- claim-deceptive-payoff-weakly-declines-with-tax
- claim-tax-dominates-cb-kernel
- claim-governance-cost-paradox
- claim-high-tax-increases-toxicity
- claim-tax-and-penalty-effects-are-orthogonal
created: 2026-02-20
updated: 2026-02-20
aliases:
- opportunistic-payoff-variance-increases-under-low-tax
cssclasses:
- claim
- claim-low
tags:
- agent-behavior
- transaction-tax
- variance
- open-question
graph-group: claim
---

# opportunistic agent payoff variance pattern does not replicate at adequate sample size

## Evidence summary

In the [[20260213-173805_baseline_governance]] sweep (80 runs, 5 agents, 10 seeds), opportunistic agent payoff appeared to show higher variance at low tax rates:

| Tax rate | Mean | SD | N |
|----------|------|----|---|
| 0% | 11.95 | 4.49 | 20 |
| 5% | 12.61 | 5.46 | 20 |
| 10% | 11.41 | 3.94 | 20 |
| 15% | 9.88 | 2.53 | 20 |

The SD at 0-5% tax (4.49-5.46) appeared roughly 2x the SD at 15% tax (2.53). **However**, formal Levene's test on the [[20260213-202050_baseline_governance_v2]] sweep (N=100 per tax level, 7 levels) yields F=1.01, p=0.42 — **no significant variance heterogeneity**. The apparent doubling at N=20 was likely a small-sample artifact.

The original interpretation suggested that taxation constrains the strategy space available to opportunistic agents: at low tax, opportunistic agents can exploit variable conditions for high-variance returns; at high tax, the narrow margin after tax squeezes all agents into a similar low-payoff band. The peak variance at 5% aligns with the onset of the [[claim-tax-phase-transition]] — the 5-10% transition band is precisely where the strategy space compresses most sharply. The [[claim-tax-and-penalty-effects-are-orthogonal]] finding confirms this variance compression is a pure tax effect, not a penalty interaction.

This connects to [[claim-welfare-non-normality-at-extreme-tax]] — the non-normal welfare distributions at extreme tax rates may partly reflect this agent-type-specific variance heteroscedasticity. The high-variance regime (0-5% tax) coincides exactly with the safe operating range identified by [[claim-optimal-tax-range-0-to-5pct]], meaning the welfare-safe range permits the widest opportunistic strategy space. At the other extreme, the variance compression at 15% (SD=2.53) is consistent with the collapsed regime identified by [[claim-welfare-plateaus-above-12pct-tax]], where all agents converge to a depleted floor.

## Mechanism (hypothesized)

Opportunistic agents select strategies based on expected returns. In low-tax environments, the return landscape has more peaks and valleys — some opportunistic strategies succeed spectacularly while others fail. High taxation flattens the return landscape by extracting a larger share of gross returns, compressing the range of net outcomes. This is analogous to how progressive taxation reduces income inequality in real economies. The [[claim-tax-dominates-cb-kernel]] finding that tax explains 32.4% of welfare variance while CB has null effect reinforces the interpretation: the variance compression mechanism is specifically tax-driven, not a byproduct of circuit breaker activation.

Completing the agent-type variance picture: [[claim-tax-hurts-honest-more-than-opportunistic]] shows honest agents bear the largest absolute mean loss, while this claim shows opportunistic agents bear the largest variance compression. [[claim-deceptive-payoff-weakly-declines-with-tax]] shows deceptive agents have low baseline payoff and presumably compressed variance at all tax rates. Together, these establish that flat-rate taxation affects not just the mean but the entire distribution shape differently for each agent type. The [[claim-high-tax-increases-toxicity]] finding suggests that the variance compression may force opportunistic agents into toxic strategies when the high-variance exploitative strategies become unprofitable. This exemplifies the [[claim-governance-cost-paradox]]: high tax compresses opportunistic variance (a distributional effect) while simultaneously destroying aggregate welfare and increasing toxicity.

## Boundary conditions

- N=20 per cell is underpowered for reliable variance estimation
- No formal Levene's test or Brown-Forsythe test applied
- 5-agent population (different from the 8-agent v2 sweep); effect may be agent-count-dependent
- Not yet replicated; the v2 sweep (N=200 per tax level) could provide a decisive test

## Open questions

- Run Levene's test on the v2 sweep data to formally test heteroscedasticity
- Does the variance compression apply to honest agents too, or is it specific to opportunistic agents?
- Is the variance pattern monotonic with tax rate, or does the peak variance at 5% suggest a non-linear mechanism?
- Does variance compression explain why pairwise t-tests involving 5% tax show lower significance than expected given the mean differences?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[transaction-tax-rate]]

<!-- topics: agent-behavior, transaction-tax, variance, open-question -->
