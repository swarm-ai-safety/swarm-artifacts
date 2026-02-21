---
description: Deceptive agent payoff declines 21.8% under taxation but effect sizes are small (d=0.44) and only BH-significant
type: claim
status: active
confidence: medium
domain: agent-behavior
evidence:
  supporting:
  - run: 20260213-202050_baseline_governance_v2
    metric: deceptive_payoff
    detail: "0% vs 15% tax: mean 2.55→2.00, d=0.44, BH-significant, N=200. No Bonferroni-significant comparisons"
  - run: 20260213-202050_baseline_governance_v2
    metric: deceptive_payoff
    detail: "0% vs 10% tax: d=0.42, BH-significant. Percentage decline (21.8%) is highest among agent types but absolute delta is smallest"
  weakening: []
  boundary_conditions:
  - 8 agents, small-world topology k=4 p=0.15, 50 seeds
  - Deceptive agents have much lower baseline payoff (2.55) than honest (14.81) or opportunistic (12.19)
  - High percentage sensitivity but low absolute sensitivity
sensitivity:
  topology: untested beyond small-world
  agent_count: 2 deceptive agents in 8-agent population; larger samples may sharpen the effect
  governance_interaction: CB has negligible effect on deceptive payoff (d<0.07)
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-tax-hurts-honest-more-than-opportunistic
- claim-tax-disproportionately-punishes-rlm-agents
- claim-optimal-tax-range-0-to-5pct
- claim-governance-cost-paradox
- claim-welfare-plateaus-above-12pct-tax
created: 2026-02-20
updated: 2026-02-20
aliases:
- deceptive-payoff-weakly-declines-with-tax
cssclasses:
- claim
- claim-medium
tags:
- governance
- transaction-tax
- agent-behavior
- deceptive
graph-group: claim
---

# deceptive agent payoff declines with tax rate but the effect is small and only BH-significant

## Evidence summary

In the [[20260213-202050_baseline_governance_v2]] sweep (700 runs, 50 seeds), deceptive agents show a 21.8% payoff decline from 0% to 15% tax (2.55→2.00), the highest percentage decline of any agent type. However, the effect size is small (d=0.44) and only reaches BH significance, not Bonferroni. In absolute terms, the delta (-0.55) is much smaller than honest agents (-2.01) or opportunistic agents (-1.61).

This creates an asymmetry: deceptive agents are most sensitive to tax in percentage terms but least affected in absolute terms, because their baseline payoff is already low. See [[claim-tax-hurts-honest-more-than-opportunistic]] for the honest-vs-opportunistic comparison. Combined with [[claim-tax-disproportionately-punishes-rlm-agents]], which shows RLM agents absorbing 2x the effect size of honest agents in a different population, the full agent-type sensitivity spectrum is: RLM > honest > opportunistic > deceptive (in absolute terms). This spectrum exemplifies the [[claim-governance-cost-paradox]]: taxation imposes the highest absolute cost on the agents governance should protect (cooperative, high-value transactors) while barely affecting the agents it should constrain (deceptive, low-value transactors).

## Mechanism

Deceptive agents earn less per transaction because their deceptive strategies are partially detected and discounted by other agents. Taxation on already-marginal transactions pushes some below profitability, but the absolute loss is small because the baseline is small.

## Boundary conditions

- Only 2 deceptive agents in the 8-agent population; low N per agent type
- BH-significant only; may not survive stricter correction
- Deceptive agent definition is scenario-specific

## Open questions

- Does the percentage sensitivity matter more than the absolute sensitivity for ecosystem dynamics?
- Would deceptive agents switch strategies entirely above some tax threshold?
- Is the BH significance robust to replication with more seeds?
- Within the safe operating range identified by [[claim-optimal-tax-range-0-to-5pct]], the deceptive payoff decline is negligible — does this mean low tax rates provide zero anti-deception benefit?
- The [[claim-welfare-plateaus-above-12pct-tax]] plateau is partly explained by deceptive agents having so little left to lose — does the deceptive payoff also plateau, and at what tax rate?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[transaction-tax-rate]]

<!-- topics: governance, transaction-tax, agent-behavior, deceptive -->
