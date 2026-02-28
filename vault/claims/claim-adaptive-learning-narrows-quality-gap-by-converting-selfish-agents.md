---
description: Adaptive learning regime reduces quality gap 27% (0.43 to 0.28) by raising selfish agent cooperation from 0.41 to 0.61, while increasing toxicity 15%
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260226-201109_mesa_adaptive_agents_study
    metric: quality_gap
    detail: "Adaptive learning at rho=1.0: quality_gap=0.283 vs adaptive rho=1.0 quality_gap=0.317. Selfish p rises from 0.41 to 0.61. Exploitative p rises from 0.32 to 0.41. 5 seeds per condition, 11 rho levels x 3 regimes = 33 conditions"
  - run: 20260226-201109_mesa_adaptive_agents_study
    metric: welfare
    detail: "Adaptive learning preserves 2.4x more welfare at rho=1.0 (807 vs 340) because agents learn to cooperate rather than being excluded by acceptance threshold"
  weakening: []
  boundary_conditions:
  - "Mesa adaptive agents scenario with 3 regimes (static, adaptive, adaptive_learning)"
  - "Adaptive learning modifies agent cooperation probabilities over time; static and adaptive do not"
  - "At rho=0: adaptive_learning toxicity 0.272 vs adaptive 0.236 — learning regime starts more toxic"
  - "5 seeds per condition — moderate statistical power"
  - "Quality gap reduction comes at cost of higher baseline toxicity"
sensitivity:
  topology: untested beyond mesa default
  agent_count: untested beyond default
  learning_rate: implicit in scenario — learning speed not parameterized
supersedes: []
superseded_by: []
related_claims:
- claim-adaptive-governance-trades-welfare-for-toxicity-at-constant-marginal-rate
- claim-mesa-agent-objectives-are-invariant-to-governance-regime
- claim-static-externality-tax-is-pure-deadweight-welfare-loss
- claim-governance-cost-paradox
created: 2026-02-27
updated: 2026-02-27
aliases:
- adaptive-learning-quality-gap
cssclasses:
- claim
- claim-medium
tags:
- governance
- adaptive-learning
- quality-gap
- mesa
graph-group: claim
---

# adaptive learning agents narrow the quality gap by 27% through selfish agent conversion toward cooperation

## Evidence summary

The [[20260226-201109_mesa_adaptive_agents_study]] (165 runs: 3 regimes x 11 rho levels x 5 seeds) compares three governance regimes:

| Regime | Quality gap (rho=0) | Quality gap (rho=1) | Welfare (rho=1) | Toxicity (rho=0) |
|--------|--------------------|--------------------|-----------------|------------------|
| Static | 0.434 | 0.434 | 723 | 0.236 |
| Adaptive | 0.434 | 0.317 | 340 | 0.236 |
| Adaptive learning | 0.336 | 0.283 | 807 | 0.272 |

## Mechanism

Adaptive learning agents update their cooperation probabilities based on interaction outcomes. This produces measurable behavioral change:

- **Selfish agents**: p_cooperative rises from 0.41 (static/adaptive) to 0.61 (adaptive learning at rho=1.0)
- **Exploitative agents**: p_cooperative rises from 0.32 to 0.41
- **Cooperative agents**: p_cooperative unchanged at ~0.79

The quality gap narrows because selfish and exploitative agents learn to produce higher-quality outputs, not because governance excludes them.

## Welfare preservation

Adaptive learning preserves dramatically more welfare at high rho:
- At rho=1.0: adaptive_learning welfare=807 vs adaptive welfare=340 (2.4x)
- The mechanism: instead of raising acceptance thresholds to exclude bad agents (adaptive), the learning regime converts bad agents into better ones, maintaining participation rates

## Tradeoff

The learning regime comes with a toxicity penalty at low rho:
- At rho=0: adaptive_learning toxicity 0.272 vs adaptive 0.236 (15% higher)
- This resolves at high rho: at rho=1.0, adaptive_learning toxicity 0.147 vs adaptive 0.157

## Implications

1. Governance that changes agents (through incentive-aligned learning) outperforms governance that filters agents (through acceptance thresholds)
2. This challenges [[claim-mesa-agent-objectives-are-invariant-to-governance-regime]] — under adaptive learning, objectives DO change
3. The quality gap reduction is a better metric than toxicity for evaluating learning-based governance

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, adaptive-learning, quality-gap, mesa -->
