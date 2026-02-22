---
description: Contract screening achieves separation_quality=1.0 and infiltration_rate=0.0 across 11 seeds (42-52) with honest/opportunistic/deceptive pools
type: claim
status: active
confidence: high
domain: market
evidence:
  supporting:
    - run: contract_screening_seed42
      metric: pool_composition
      detail: "Perfect separation at epoch 0: 5 honest→truthful_auction, 3 opportunistic→fair_division, 2 deceptive→default_market. N=1"
    - run: contract_screening_sweep
      metric: separation_quality
      detail: "separation_quality=1.0, infiltration_rate=0.0 across all 10 seeds (43-52). Zero variance. Bonferroni-corrected across 10 comparisons: every seed is individually perfect"
    - run: research-mechanism-design-screening-2026-02-22
      source_type: research
      detail: "Rothschild-Stiglitz (1976) screening equilibrium theory predicts perfect type separation with discrete type spaces, consistent with SWARM's honest/deceptive/opportunistic classification. R-S also predicts fragility when types are close — adaptive adversaries who learn to mimic honest behavior may degrade separation. The 6.7x payoff premium is consistent with classical information rent theory"
  weakening: []
  boundary_conditions:
    - "10-agent population (5 honest, 3 opportunistic, 2 deceptive); scaling untested"
    - "Three pool types: truthful_auction, fair_division, default_market"
    - "Contract screening scenario only; generalizability to other scenarios untested"
    - "Agent type ratios fixed at 5:3:2; different ratios untested"
sensitivity:
  topology: untested
  agent_count: "10 agents only; larger populations may break separation"
  governance_interaction: "Screening operates independently of CB/audit/tax governance; mechanism orthogonal to standard governance stack"
supersedes: []
superseded_by: []
related_claims:
  - claim-screening-equilibrium-generates-honest-payoff-premium
  - claim-agent-architecture-constrains-behavior-more-than-governance
  - claim-prompt-level-governance-fails-in-multi-agent-systems
  - claim-leniency-whistleblowing-is-untested-governance-lever
  - claim-quadratic-staking-may-solve-sybil-cost-inversion
created: 2026-02-21
updated: 2026-02-22
aliases:
  - contract-screening-achieves-perfect-type-separation
cssclasses:
  - claim
  - claim-high
tags:
  - contract-screening
  - mechanism-design
  - screening-equilibrium
  - market
graph-group: claim
---

# contract screening achieves perfect type separation across 11 seeds with zero infiltration

## Evidence summary

The contract screening mechanism achieves perfect agent type separation in all 11 tested seeds, a result strong enough for high confidence.

In [[contract_screening_seed42]], the event log shows agents self-selecting at epoch 0: all 5 honest agents enter the truthful_auction pool, all 3 opportunistic agents enter fair_division, and both deceptive agents enter default_market. This separation persists through all 20 epochs with no type mixing.

In [[contract_screening_sweep]] (seeds 43-52), separation_quality=1.0 and infiltration_rate=0.0 in every one of 10 seeds. The zero variance across seeds means this is deterministic, not stochastic — the screening mechanism always correctly sorts agents by type. Bonferroni correction across 10 seeds is trivially satisfied because each seed individually shows perfect separation.

This is a mechanistic result, not a statistical one. The screening contracts are designed so that truthful_auction is incentive-compatible only for honest types, fair_division only for opportunistic types, and default_market is the residual pool. Because agent types are fixed (not learned), the revelation principle guarantees separation in equilibrium.

## Boundary conditions

- Population fixed at 10 agents with 5:3:2 type ratio
- Three pool types mapped to three agent types — may not generalize to finer-grained type spaces
- Agent types are exogenous and fixed; adaptive agents that change type over time are untested
- 20-epoch horizon; longer horizons with type-switching are untested

## Mechanism

Contract screening is a revelation mechanism from mechanism design theory. Each pool offers different terms (truthful auction vs fair division vs default market) that are differentially attractive to different agent types. Honest agents prefer truthful auctions because honest reporting is dominant strategy there. Opportunistic agents prefer fair division because it rewards strategic bargaining. Deceptive agents end up in the default market because neither specialized pool is incentive-compatible for deceptive behavior.

The separation is self-enforcing because each type earns strictly higher payoff in its assigned pool than in any other pool — this is the incentive compatibility constraint that drives self-selection.

## Update history

**2026-02-22** — research enrichment:
- Added Rothschild-Stiglitz (1976) theoretical grounding: screening equilibrium theory predicts perfect separation with discrete type spaces, consistent with SWARM's results. R-S also predicts fragility when types are close, suggesting adaptive adversaries could degrade separation. The 6.7x payoff premium aligns with classical information rent theory.
- Confidence unchanged — external literature, not new SWARM evidence.

## Open questions

- Does perfect separation break with larger populations (N>20)?
- Can adaptive agents learn to mimic honest types and infiltrate the truthful auction pool?
- What happens when agent type ratios shift (e.g., 2 honest, 5 deceptive)?
- Is the screening mechanism robust to collusion between types across pools?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: contract-screening, mechanism-design, screening-equilibrium, market -->
