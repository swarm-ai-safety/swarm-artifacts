---
description: Transaction tax at 10% increases toxicity rate by 0.6pp (d=-0.86, Bonferroni-sig), a small but consistent effect
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: toxicity_rate
    detail: "10% vs 0% tax: toxicity 0.3403 vs 0.3346, d=-0.86, p=0.0004, N=80, Bonferroni-corrected"
  - run: 20260213-221500_collusion_tax_effect
    metric: toxicity_rate
    detail: "5% vs 10% tax: d=-0.57, BH-significant; 0% vs 5%: d=-0.69, BH-significant"
  weakening: []
  boundary_conditions:
  - 12 agents, default topology, tax range 0-10%, 10 seeds
  - Collusion penalty active (0.5-2.0x) but orthogonal to tax-toxicity relationship
  - Absolute effect is small (~0.6 percentage points)
sensitivity:
  topology: untested beyond default
  agent_count: 12 agents; toxicity response may differ in larger populations
  governance_interaction: collusion penalty independently affects toxicity; combined effect may be super-additive
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-collusion-penalty-destabilizes
- claim-tax-phase-transition
created: 2026-02-20
updated: 2026-02-20
aliases:
- high-tax-increases-toxicity
cssclasses:
- claim
- claim-medium
tags:
- governance
- transaction-tax
- toxicity
graph-group: claim
---

# high transaction tax increases ecosystem toxicity rate

## Evidence summary

In the [[20260213-221500_collusion_tax_effect]] sweep (160 runs), transaction tax at 10% vs 0% increases mean toxicity from 0.3346 to 0.3403 (d=-0.86, p=0.0004, Bonferroni-corrected, N=80). The effect is consistent across intermediate comparisons: 0% vs 5% (d=-0.69, BH-sig) and 5% vs 10% (d=-0.57, BH-sig), indicating a monotonic toxicity increase with tax rate.

This creates a governance dilemma: transaction tax reduces welfare ([[claim-tax-welfare-tradeoff]]) AND increases toxicity, meaning it fails on both economic and safety dimensions at high rates.

## Mechanism

Resource scarcity induced by high taxation may force agents into more competitive, lower-quality interactions. When legitimate transaction returns decline, agents shift toward strategies that extract short-term value at the cost of ecosystem quality. This parallels how [[claim-collusion-penalty-destabilizes]] shows punitive governance measures backfiring on toxicity.

## Boundary conditions

- The absolute toxicity increase is small (~0.6pp), though statistically robust
- Only tested with collusion-enabled agent population; pure honest-agent ecosystems may respond differently
- No redistribution modeled — returning tax revenue might offset the scarcity mechanism

## Open questions

- Is the tax-toxicity relationship linear or does it exhibit a phase transition like welfare?
- Does the toxicity increase come from specific agent types (RLM) or is it ecosystem-wide?
- Is there a tax × penalty interaction that produces super-additive toxicity at high levels of both?

---

Topics:
- [[_index]]

<!-- topics: governance, transaction-tax, toxicity -->
