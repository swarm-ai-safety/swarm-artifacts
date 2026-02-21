---
description: Welfare is statistically flat below 5% tax (d=0.34 at 2.5-5%, not significant), defining the safe operating range
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: "0% vs 2.5% tax: d=0.01, N=200. 2.5% vs 5%: d=0.34, not BH-sig. Welfare essentially flat across 0-5% range"
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: "5% vs 7.5%: d=0.87, Bonferroni-sig. Phase transition begins above 5%. Peak welfare at 2.5% (59.1)"
  weakening: []
  boundary_conditions:
  - 8 agents, small-world topology k=4 p=0.15, 50 seeds
  - No redistribution modeled; optimal range may shift if tax revenue is returned
  - Does not account for governance revenue benefits (only welfare cost)
sensitivity:
  topology: untested beyond small-world; the 5% threshold may shift with connectivity
  agent_count: 8 agents; larger populations may tolerate higher tax before welfare impact
  governance_interaction: CB has negligible effect on the optimal range
supersedes: []
superseded_by: []
related_claims:
- claim-tax-phase-transition
- claim-tax-welfare-tradeoff
- claim-welfare-plateaus-above-12pct-tax
created: 2026-02-20
updated: 2026-02-20
aliases:
- optimal-tax-range-0-to-5pct
cssclasses:
- claim
- claim-medium
tags:
- governance
- transaction-tax
- welfare
- optimization
graph-group: claim
---

# optimal transaction tax rate for welfare lies in the 0-5% range

## Evidence summary

In the [[20260213-202050_baseline_governance_v2]] sweep (700 runs, 50 seeds), welfare is statistically indistinguishable across the 0-5% tax range: 0% vs 2.5% shows d=0.01 (negligible) and 2.5% vs 5% shows d=0.34 (not BH-significant). Peak welfare occurs at 2.5% (mean=59.1). Above 5%, welfare drops sharply — the phase transition identified in [[claim-tax-phase-transition]] begins.

This identifies the **safe operating range**: governance designers can set tax rates up to 5% to generate revenue without measurable welfare cost. Combined with [[claim-welfare-plateaus-above-12pct-tax]], the full welfare curve is: flat (0-5%), steep decline (5-12.5%), flat again (>12.5%).

## Mechanism

Below 5%, the tax extraction is small enough that all agents can absorb it without changing strategies. Transaction volumes remain stable (95-96% acceptance across all conditions), and no agents are pushed below profitability thresholds. The 5% threshold likely corresponds to the point where marginal transactions become unprofitable.

## Boundary conditions

- Welfare-optimal does not mean governance-optimal: some tax may be needed to fund monitoring
- The flat response below 5% does not address toxicity effects ([[claim-high-tax-increases-toxicity]])
- No redistribution modeled; the optimal range considers only gross welfare

## Open questions

- What is the tax revenue generated at 5% vs the welfare cost? Is there a revenue-welfare frontier?
- Does the 5% threshold hold in the collusion_tax_effect context (12 agents, collusion active)?
- Can the safe range be extended by combining low tax with redistribution?
- How does this interact with the toxicity finding — is there a tax rate that is welfare-neutral but toxicity-increasing?

---

Topics:
- [[_index]]

<!-- topics: governance, transaction-tax, welfare, optimization -->
