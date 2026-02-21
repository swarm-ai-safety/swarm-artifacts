---
description: Collusive agents accumulate 137x less wealth than honest agents under behavioral monitoring
type: claim
status: active
confidence: high
domain: collusion
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: final_wealth
    detail: Collusive 3.4±1.2 vs honest 467.3±186.9, d=3.51, p<0.001, N=10 seeds, Bonferroni-corrected
  weakening: []
  boundary_conditions:
  - GTB 15x15 gridworld, 14 agents, heuristic tax planner
  - Similarity threshold 0.70 for collusion detection
sensitivity:
  topology: 15x15 gridworld with spatial proximity; results may differ in non-spatial interaction graphs
  agent_count: 14 agents; collusion detection difficulty scales with agent count
supersedes: []
superseded_by: []
related_claims:
- claim-collusion-penalty-destabilizes
- claim-collusion-penalty-has-no-economic-effect
created: 2026-02-19
updated: 2026-02-19
aliases:
- collusion-wealth-destruction
- collusive-agents-accumulate-137x-less-wealth
cssclasses:
- claim
- claim-high
tags:
- collusion
- agent-behavior
- wealth
- monitoring
graph-group: claim
---

## Collusion Wealth Destruction

Under behavioral monitoring with a similarity threshold of 0.70, collusive agents accumulate 137x less wealth than honest agents (3.4 +/- 1.2 vs 467.3 +/- 186.9, d = 3.51, p < 0.001).

**Evidence summary.** In the AI Economist GTB study (10 seeds, 14 agents on a 15x15 gridworld with heuristic tax planner), agents flagged as collusive by the behavioral similarity detector were penalized through the tax mechanism. The wealth gap between collusive and honest agents was massive (d = 3.51) and robust across all 10 seeds after Bonferroni correction. This suggests that even imperfect behavioral monitoring can create overwhelming economic disincentives for collusion.

**Boundary conditions.** The result depends on the 0.70 similarity threshold for collusion detection. At lower thresholds, false positives would penalize honest agents; at higher thresholds, sophisticated collusion strategies might evade detection. The heuristic tax planner may not represent optimal tax policy. The 15x15 gridworld imposes spatial constraints that may make collusion more detectable than in abstract interaction graphs.

**Open questions.**
- What is the optimal similarity threshold that maximizes the wealth gap while minimizing false positives?
- Can collusive agents learn to diversify behavior to stay below the detection threshold?
- Does the wealth destruction effect hold under learned (rather than heuristic) tax policies?
- How does the 137x ratio change with the number of colluding agents?

<!-- topics: collusion, agent-behavior, wealth, monitoring -->
