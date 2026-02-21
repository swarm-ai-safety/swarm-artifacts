---
description: Contract screening produces 6.7x honest-to-deceptive payoff ratio (28.5 vs 4.3) and d=2.42 honest-to-opportunistic gap across 10 seeds
type: claim
status: active
confidence: high
domain: market
evidence:
  supporting:
    - run: contract_screening_sweep
      metric: payoff_by_type
      detail: "Honest mean=28.52 (SD=2.71), opportunistic mean=22.62 (SD=2.12), deceptive mean=4.27 (SD=0.95). Honest vs deceptive ratio=6.7x. Honest vs opportunistic Cohen's d=2.42. N=10 seeds, Bonferroni-corrected p<0.001 for both comparisons"
    - run: contract_screening_seed42
      metric: interaction_payoffs
      detail: "Honest-honest collaboration payoffs 0.55-0.75; opportunistic-honest cross-pool trade 0.43-0.47. Per-interaction honest premium visible from epoch 0"
  weakening: []
  boundary_conditions:
    - "10-agent population with 5:3:2 honest:opportunistic:deceptive ratio"
    - "Truthful auction / fair division / default market pool structure"
    - "20 epochs, 10 steps per epoch"
    - "Governance costs low (0.007-0.014 per interaction); higher governance overhead untested"
sensitivity:
  topology: untested
  agent_count: "10 agents only; payoff ratios may change with scale"
  governance_interaction: "Low 2% tax rate; higher tax may compress the honest payoff premium"
supersedes: []
superseded_by: []
related_claims:
  - claim-contract-screening-achieves-perfect-type-separation
  - claim-tax-hurts-honest-more-than-opportunistic
  - claim-governance-cost-paradox
created: 2026-02-21
updated: 2026-02-21
aliases:
  - screening-equilibrium-generates-honest-payoff-premium
cssclasses:
  - claim
  - claim-high
tags:
  - contract-screening
  - mechanism-design
  - screening-equilibrium
  - payoff-hierarchy
graph-group: claim
---

# screening equilibrium generates 6.7x honest-to-deceptive payoff premium with d=2.42 honest-opportunistic gap

## Evidence summary

Across 10 seeds in [[contract_screening_sweep]], the contract screening mechanism produces a strong payoff hierarchy aligned with agent honesty: honest agents earn a mean of 28.52 (SD=2.71), opportunistic agents 22.62 (SD=2.12), and deceptive agents 4.27 (SD=0.95).

The honest-to-deceptive ratio of 6.7x is substantial — honest agents earn nearly seven times more than deceptive agents. The honest-to-opportunistic gap is also large: Cohen's d = (28.52 - 22.62) / sqrt((2.71^2 + 2.12^2)/2) = 2.42, well above the conventional "large" threshold of 0.8. Both comparisons survive Bonferroni correction across 2 pairwise tests (p < 0.001).

The mechanism generating this premium is visible in [[contract_screening_seed42]]: honest-honest interactions within the truthful_auction pool yield 0.55-0.75 payoff per interaction, while cross-pool opportunistic-honest trades yield only 0.43-0.47 for the opportunistic agent. The truthful auction mechanism rewards honest reporting, creating a per-interaction premium that compounds over 200 interactions across 20 epochs.

This finding is economically significant because it demonstrates that mechanism design (specifically, incentive-compatible contract screening) can create strong material incentives for honest behavior without relying on punitive governance mechanisms. This contrasts with [[claim-tax-hurts-honest-more-than-opportunistic]], where tax-based governance actually penalizes honest agents more.

## Boundary conditions

- Fixed 5:3:2 agent type ratio; different ratios may alter payoff hierarchy
- 2% transaction tax; higher tax may compress the premium
- Payoff premium depends on perfect type separation (see [[claim-contract-screening-achieves-perfect-type-separation]]); if separation breaks, the premium may erode

## Mechanism

The truthful auction mechanism is incentive-compatible for honest agents, meaning honest reporting is the dominant strategy. This produces efficient allocations within the honest pool, maximizing total surplus. Opportunistic agents in fair_division cannot exploit information asymmetries as effectively because the mechanism is designed for strategic types. Deceptive agents in the default market face the worst mechanism — no information advantages and no strategic complementarities — earning minimal payoffs.

The payoff premium is self-reinforcing through reputation: honest agents build reputation faster (0.27-0.46 by step 4 vs 0.02-0.16 for opportunistic), which improves their future interaction quality.

## Open questions

- Does the 6.7x premium hold with larger populations (N>20)?
- Can the premium be increased by adding more specialized pool types?
- What tax rate would compress the premium to incentive-irrelevance?
- How does the premium interact with governance mechanisms (CB, audit)?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: contract-screening, mechanism-design, screening-equilibrium, payoff-hierarchy -->
