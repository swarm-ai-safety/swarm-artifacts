---
description: Transaction tax reduces RLM agent payoff 2x more severely than honest agent payoff in effect-size terms
type: claim
status: active
confidence: high
domain: governance
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: rlm_payoff
    detail: "10% vs 0% tax: RLM payoff drops 220.8→194.5, d=6.02, p<1e-30, N=80, Bonferroni-corrected"
  - run: 20260213-221500_collusion_tax_effect
    metric: honest_payoff
    detail: "10% vs 0% tax: honest payoff drops 601.3→545.3, d=2.87, p<1e-20, N=80, Bonferroni-corrected"
  weakening: []
  boundary_conditions:
  - 12 agents with heterogeneous reasoning depths (1/3/5)
  - Default topology, tax range 0-10%, 10 seeds per cell
  - Collusion detection and penalty active simultaneously
sensitivity:
  topology: untested beyond default
  agent_count: 12 agents; ratio may shift with different population compositions
  governance_interaction: collusion penalty active but orthogonal to tax effect on payoffs
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-tax-phase-transition
- claim-smarter-agents-earn-less
- claim-collusion-penalty-destabilizes
- claim-staking-backfires
- claim-governance-cost-paradox
- claim-welfare-non-normality-at-extreme-tax
- claim-tax-and-penalty-effects-are-orthogonal
- claim-agent-architecture-constrains-behavior-more-than-governance
created: 2026-02-20
updated: 2026-02-21
aliases:
- tax-disproportionately-punishes-rlm-agents
cssclasses:
- claim
- claim-high
tags:
- governance
- transaction-tax
- agent-behavior
- rlm
graph-group: claim
---

# transaction tax reduces RLM agent payoff twice as severely as honest agent payoff

## Evidence summary

In the [[20260213-221500_collusion_tax_effect]] sweep (160 runs, 4 tax rates x 4 collusion penalty levels x 10 seeds), transaction tax at 10% vs 0% produces a dramatically larger effect on RLM agents (d=6.02) than on honest agents (d=2.87). The absolute payoff gap is already enormous at baseline — honest agents earn 601.3 vs RLM agents' 220.8 at 0% tax — and taxation widens it further because the proportional reduction hits RLM agents harder.

This finding extends [[claim-smarter-agents-earn-less]] by showing that deeper-reasoning agents are not only penalized at baseline but also more vulnerable to governance taxation. It adds a distributional dimension to [[claim-tax-welfare-tradeoff]]: the aggregate welfare decline is unevenly borne across agent types, with RLM agents absorbing a disproportionate share. Together with [[claim-staking-backfires]], this establishes a pattern where punitive governance mechanisms systematically disadvantage specific agent populations rather than applying uniform pressure.

## Mechanism

RLM agents engage in more complex multi-step transactions that incur tax at each step. Their lower baseline payoff means the same absolute tax bite represents a larger fraction of earnings. Additionally, RLM agents' collusive strategies require more transactions to coordinate, amplifying tax exposure relative to honest agents who transact more simply.

## Boundary conditions

- Tested with 12 agents (mixed honest/RLM), default topology
- Tax range 0–10% with collusion penalty multiplier varying 0.5–2.0x
- The disproportionate effect may reverse if tax redistribution favors low-earning agents
- Agent composition (ratio of honest to RLM) may modulate the differential

## Open questions

- Does the 2x differential persist under redistribution mechanisms?
- At what agent composition ratio does the differential disappear?
- Is the mechanism transactional volume or per-transaction value?
- How does this interact with [[claim-staking-backfires]] — do both mechanisms compound against the same agent type?
- The non-normal welfare distributions at extreme tax rates ([[claim-welfare-non-normality-at-extreme-tax]]) may reflect heterogeneous agent-type responses to taxation — does the bifurcation correspond to RLM vs honest agent outcomes?
- This contributes to [[claim-governance-cost-paradox]] by showing governance costs are not uniformly distributed

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[transaction-tax-rate]]

<!-- topics: governance, transaction-tax, agent-behavior, rlm -->
