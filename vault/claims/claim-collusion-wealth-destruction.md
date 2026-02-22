---
description: Collusive agents accumulate 137x less wealth than honest agents under behavioral monitoring
type: claim
status: active
confidence: medium
domain: collusion
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: final_wealth
    detail: Collusive 3.4±1.2 vs honest 467.3±186.9, d=3.51, p<0.001, N=10 seeds, Bonferroni-corrected
  - run: 20260221-081953_redteam_contract_screening_with_collusion
    metric: collusion_ring_damage
    detail: "Contract screening scenario: CD reduces collusion ring damage 85.73→21.43 (75% reduction), evasion 0.40→0.10. Cross-scenario corroboration of monitoring-as-disincentive mechanism. N=1 seed"
  weakening: []
  boundary_conditions:
  - GTB 15x15 gridworld, 14 agents, heuristic tax planner
  - Similarity threshold 0.70 for collusion detection
  - Contract screening scenario replicates direction via correlation-based CD (threshold 0.8), different detection mechanism
sensitivity:
  topology: 15x15 gridworld with spatial proximity; results may differ in non-spatial interaction graphs
  agent_count: 14 agents; collusion detection difficulty scales with agent count
  detection_mechanism: GTB uses behavioral similarity (0.70 threshold); contract screening uses correlation-based CD (0.80 threshold). Both create large disincentives but through different detection channels
supersedes: []
superseded_by: []
related_claims:
- claim-collusion-penalty-destabilizes
- claim-collusion-penalty-has-no-economic-effect
- claim-collusion-detection-is-binding-constraint-on-robustness
- claim-coordination-attacks-dominate-redteam-damage
- claim-steganographic-collusion-unaddressed-by-swarm-detection
- claim-leniency-whistleblowing-is-untested-governance-lever
- claim-collusion-detection-reduces-ring-damage-75pct
created: 2026-02-19
updated: 2026-02-21
aliases:
- collusion-wealth-destruction
- collusive-agents-accumulate-137x-less-wealth
cssclasses:
- claim
- claim-medium
tags:
- collusion
- agent-behavior
- wealth
- monitoring
graph-group: claim
---

# collusive agents accumulate 137x less wealth than honest agents under behavioral monitoring

Under behavioral monitoring with a similarity threshold of 0.70, collusive agents accumulate 137x less wealth than honest agents (3.4 +/- 1.2 vs 467.3 +/- 186.9, d = 3.51, p < 0.001).

**Evidence summary.** In the AI Economist GTB study (10 seeds, 14 agents on a 15x15 gridworld with heuristic tax planner), agents flagged as collusive by the behavioral similarity detector were penalized through the tax mechanism. The wealth gap between collusive and honest agents was massive (d = 3.51) and robust across all 10 seeds after Bonferroni correction. This suggests that even imperfect behavioral monitoring can create overwhelming economic disincentives for collusion.

**Boundary conditions.** The result depends on the 0.70 similarity threshold for collusion detection. At lower thresholds, false positives would penalize honest agents; at higher thresholds, sophisticated collusion strategies might evade detection. The heuristic tax planner may not represent optimal tax policy. The 15x15 gridworld imposes spatial constraints that may make collusion more detectable than in abstract interaction graphs.

**Open questions.**
- What is the optimal similarity threshold that maximizes the wealth gap while minimizing false positives?
- Can collusive agents learn to diversify behavior to stay below the detection threshold?
- Does the wealth destruction effect hold under learned (rather than heuristic) tax policies?
- How does the 137x ratio change with the number of colluding agents?

## Update history

**2026-02-21** — backward-pass update:
- Added supporting evidence from [[20260221-081953_redteam_contract_screening_with_collusion]]: correlation-based collusion detection in the contract screening scenario achieves 75% damage reduction (85.73 to 21.43) against collusion rings, corroborating the core finding that behavioral monitoring creates strong economic disincentives for collusion. Different detection mechanism (correlation threshold 0.8 vs. behavioral similarity 0.70) reaching the same qualitative conclusion strengthens cross-scenario generalizability.
- Added [[claim-collusion-detection-reduces-ring-damage-75pct]] to related claims.
- Added boundary condition noting the contract screening scenario replicates direction through a different detection channel.
- Added detection_mechanism to sensitivity fields.
- Confidence remains **medium**: the GTB result is Bonferroni-significant with 10 seeds (primary evidence), and the contract screening result provides scenario-level replication but is single-seed (N=1). Upgrading to high would require multi-seed replication in a second scenario.

---

Topics:
- [[_index]]

<!-- topics: collusion, agent-behavior, wealth, monitoring -->
