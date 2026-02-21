---
description: Welfare decline flattens above 12.5% tax rate with negligible marginal change (d=0.028 at 12.5-15%)
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: "12.5% vs 15% tax: d=0.028, p=0.84, N=200. 10% vs 12.5%: d=0.47, BH-sig. Welfare essentially flat above 12.5%"
  weakening: []
  boundary_conditions:
  - 8 agents, small-world topology k=4 p=0.15, 50 seeds
  - Tax range 0-15%; behavior above 15% unknown
  - Circuit breaker on/off has negligible effect on the plateau
sensitivity:
  topology: untested beyond small-world; plateau point may shift with connectivity
  agent_count: 8 agents; plateau may occur at different tax rate with more agents
  governance_interaction: CB does not affect the plateau threshold
supersedes: []
superseded_by: []
related_claims:
- claim-tax-phase-transition
- claim-tax-welfare-tradeoff
- claim-optimal-tax-range-0-to-5pct
- claim-tax-hurts-honest-more-than-opportunistic
- claim-deceptive-payoff-weakly-declines-with-tax
- claim-welfare-non-normality-at-extreme-tax
- claim-high-tax-increases-toxicity
- claim-tax-cb-interact-on-quality-gap
created: 2026-02-20
updated: 2026-02-20
aliases:
- welfare-plateaus-above-12pct-tax
cssclasses:
- claim
- claim-medium
tags:
- governance
- transaction-tax
- welfare
- phase-transition
graph-group: claim
---

# welfare decline plateaus above 12.5% transaction tax with negligible marginal change

## Evidence summary

In the [[20260213-202050_baseline_governance_v2]] sweep (700 runs, 50 seeds, 7 tax levels), the welfare response to tax rate follows an S-curve: flat below 5%, steep decline 5-10%, then flattening above 12.5%. The 12.5% vs 15% comparison shows d=0.028 (p=0.84) — effectively zero marginal decline.

This refines [[claim-tax-phase-transition]] by identifying the upper bound of the transition region. The S-curve has three regimes: safe (0-5%), transition (5-12.5%), and collapsed (>12.5%). In the collapsed regime, the ecosystem has already contracted to a minimum viable state, and additional taxation extracts negligibly from an already-depleted system.

## Mechanism

Above the phase transition, most marginal interactions have already become unprofitable. Remaining transactions are either essential (high-value, tax-resistant) or between agents with no alternative partners. Additional tax beyond 12.5% cannot further reduce participation because participation is already near its floor.

The plateau's existence is grounded by the agent-type decomposition: [[claim-tax-hurts-honest-more-than-opportunistic]] shows honest agents bear the largest absolute loss from taxation, and by 12.5% their transaction volume has been maximally compressed. [[claim-deceptive-payoff-weakly-declines-with-tax]] confirms that deceptive agents contribute negligibly to the plateau since their baseline payoff is already marginal (2.55) — they have little left to lose at any tax rate.

## Boundary conditions

- Only tested up to 15% tax; behavior at 20%+ is unknown — the plateau may eventually break into full ecosystem collapse
- Small-world topology with k=4 provides moderate alternatives; sparser graphs may hit the plateau earlier
- 8-agent population; larger populations may sustain more marginal interactions, shifting the plateau

## Open questions

- Does the plateau hold at 20%, 25%, or higher tax rates, or does a second transition occur?
- Is the plateau tax rate topology-dependent?
- Does the collusion_tax_effect run (which only tested 0-10%) show early signs of flattening at 10%?
- [[claim-welfare-non-normality-at-extreme-tax]] shows non-normal welfare distributions at 10% tax — does the plateau regime (>12.5%) exhibit even more severe non-normality, or does the distributional shape stabilize once the ecosystem collapses?
- Does the [[claim-tax-cb-interact-on-quality-gap]] interaction change character in the plateau regime? If CB modulates quality gap differently when the ecosystem is already depleted, this could affect recovery strategies.
- [[claim-high-tax-increases-toxicity]] reports a toxicity increase with tax — does toxicity also plateau above 12.5%, or does it continue rising even as welfare flattens?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[transaction-tax-rate]]

<!-- topics: governance, transaction-tax, welfare, phase-transition -->
