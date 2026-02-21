---
description: Transaction tax reduces honest agent payoff (d=0.80) more than opportunistic agent payoff (d=0.43) in absolute terms
type: claim
status: active
confidence: high
domain: governance
evidence:
  supporting:
  - run: 20260213-202050_baseline_governance_v2
    metric: honest_payoff
    detail: "0% vs 15% tax: honest payoff 14.81→12.79, delta=-2.01, d=0.80, p<1e-14, N=200, Bonferroni-corrected"
  - run: 20260213-202050_baseline_governance_v2
    metric: opportunistic_payoff
    detail: "0% vs 15% tax: opportunistic payoff 12.19→10.58, delta=-1.61, d=0.43, BH-significant only"
  weakening: []
  boundary_conditions:
  - 8 agents (4 honest, 2 adversarial, 2 adaptive), small-world topology k=4 p=0.15
  - Tax range 0-15%, 50 seeds per condition
  - Adversarial agent payoff is 0.0 across all conditions (no variation to compare)
sensitivity:
  topology: small-world k=4 p=0.15; differential may shift under different connectivity
  agent_count: 8 agents; ratio may change with population size
  governance_interaction: CB on/off has negligible main effect (d=0.008) but interacts with tax on honest_payoff
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-tax-disproportionately-punishes-rlm-agents
- claim-staking-backfires
- claim-governance-cost-paradox
- claim-deceptive-payoff-weakly-declines-with-tax
- claim-optimal-tax-range-0-to-5pct
- claim-welfare-plateaus-above-12pct-tax
- claim-high-tax-increases-toxicity
- claim-tax-phase-transition
created: 2026-02-20
updated: 2026-02-20
aliases:
- tax-hurts-honest-more-than-opportunistic
cssclasses:
- claim
- claim-high
tags:
- governance
- transaction-tax
- agent-behavior
graph-group: claim
---

# transaction tax reduces honest agent payoff more than opportunistic agent payoff in absolute terms

## Evidence summary

In the [[20260213-202050_baseline_governance_v2]] sweep (700 runs, 8 agents, 50 seeds, 7 tax levels), honest agents lose more from taxation than opportunistic agents in both absolute terms (delta=-2.01 vs -1.61) and effect size (d=0.80 Bonferroni-sig vs d=0.43 BH-sig only).

This extends [[claim-tax-disproportionately-punishes-rlm-agents]] to a different agent taxonomy: in the collusion study, RLM agents are hit 2x harder than honest agents; in this baseline study, honest agents are hit harder than opportunistic agents. The common pattern is that agents who transact more frequently or more honestly bear greater tax burden — connecting to [[claim-staking-backfires]] where honest agents are also disproportionately penalized by staking requirements.

## Mechanism

Honest agents transact at higher volumes and values because they engage in cooperative exchanges. Higher transaction volume means more tax events per round. Opportunistic agents selectively transact when advantageous, reducing their tax exposure. Adversarial agents earn 0.0 payoff regardless of tax rate (they are detected and excluded).

Completing the agent-type picture: [[claim-deceptive-payoff-weakly-declines-with-tax]] shows deceptive agents lose the least in absolute terms (delta=-0.55, d=0.44) because their baseline payoff is already marginal. Meanwhile, [[claim-tax-disproportionately-punishes-rlm-agents]] confirms the same honest-agent vulnerability in a different population composition with RLM agents bearing 2x the effect size. Together, these three claims establish a general pattern: agents who transact cooperatively and frequently are systematically penalized by flat-rate taxation.

## Boundary conditions

- 8-agent population with fixed composition (4 honest, 2 adversarial, 2 adaptive)
- Small-world topology — honest agents may be less disadvantaged in sparser topologies where transaction opportunities are limited for all agents
- Tax range 0-15% captures the full phase transition
- The differential is policy-relevant primarily above 5%; within the safe operating range identified by [[claim-optimal-tax-range-0-to-5pct]], honest agents absorb the tax with negligible welfare impact. Above 12.5%, [[claim-welfare-plateaus-above-12pct-tax]] suggests all agents converge to a depleted floor where the differential becomes moot.

## Open questions

- Is the honest-vs-opportunistic differential consistent with the honest-vs-RLM differential in [[claim-tax-disproportionately-punishes-rlm-agents]], or do different agent taxonomies produce different rankings?
- Does tax redistribution preferentially benefit honest agents, offsetting the differential?
- At what tax rate does the differential become negligible (convergence to shared poverty)? The [[claim-welfare-plateaus-above-12pct-tax]] plateau suggests ~12.5% is the answer.
- [[claim-high-tax-increases-toxicity]] shows tax increases toxicity — do honest agents bear the brunt of this too, compounding the distributional injustice?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[transaction-tax-rate]]

<!-- topics: governance, transaction-tax, agent-behavior -->
