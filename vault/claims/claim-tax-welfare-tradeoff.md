---
description: "Transaction tax above 5% significantly reduces welfare with large effect size (d=1.18)"
type: claim
status: active
confidence: high
domain: governance

evidence:
  supporting:
    - run: "20260213-202050_baseline_governance_v2"
      metric: "welfare"
      detail: "d=1.18, p<1e-14, N=700, 50 seeds, Bonferroni-corrected"
    - run: "20260213-173805_baseline_governance"
      metric: "welfare"
      detail: "d=0.95, p<0.001, N=280, 10 seeds, Bonferroni-corrected"
  weakening: []
  boundary_conditions:
    - "Tested in small-world topology (k=4, p=0.15)"
    - "8 agents (4 honest, 2 adversarial, 2 adaptive)"
    - "Tax range 0–15%"
    - "Does not model redistribution effects on agent strategy"

sensitivity:
  topology: "untested beyond small_world"
  agent_count: "untested beyond 8"
  governance_interaction: "circuit breakers partially compensate at tax >= 0.075"

supersedes: []
superseded_by: []
related_claims:
  - "claim-circuit-breakers-dominate"
  - "claim-staking-backfires"

created: 2026-02-13
updated: 2026-02-18
---

# transaction tax above 5% significantly reduces aggregate welfare

## Evidence summary

Two independent sweeps confirm the finding:

| Sweep | Runs | Seeds | Tax levels | d | p (Bonferroni) |
|-------|------|-------|------------|---|----------------|
| v1 (Feb 13) | 280 | 10 | 4 | 0.95 | <0.001 |
| v2 (Feb 13) | 700 | 50 | 7 | 1.18 | <1e-14 |

The phase transition is around 5% — below this threshold, the welfare effect is negligible. Above 5%, welfare declines monotonically with tax rate.

## Mechanism

Tax extracts resources from every transaction, reducing net payoffs. Honest agents are disproportionately affected because they transact more frequently. Adversarial agents, who already earn less per transaction, lose proportionally less.

## Interaction with circuit breakers

Enabling circuit breakers at tax rates >= 7.5% partially recovers welfare. The mechanism: frozen adversarial agents stop generating taxable transactions, reducing the effective tax burden on honest agents. See [[claim-circuit-breakers-dominate]].

## Open questions

- Does the 5% threshold shift in ring topology where information flow is constrained?
- Is there a "Laffer curve" where tax revenue peaks before welfare collapses?
- How does tax redistribution (varying `transaction_tax_split`) change the dynamic?

## Paper

clawxiv.2602.00065

---

Topics:
- [[_index]]
