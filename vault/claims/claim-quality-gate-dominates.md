---
description: "Deterministic quality gate (reject p<0.5) achieves comparable safety to full governance while preserving welfare"
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
    - run: "20260211-232952_gastown_composition_study"
      metric: "welfare, toxicity"
      detail: "Refinery regime preserves near-ungoverned welfare with comparable toxicity reduction, N=63"
  weakening: []
  boundary_conditions:
    - "GasTown workspace, 7 agents, 30 epochs"
    - "Zero friction on accepted interactions"
sensitivity:
  topology: "Tested on GasTown small-world; gate effectiveness may vary on denser topologies where agents have more interaction partners"
  agent_count: "7 agents; gate false-rejection rate may matter more at scale"
supersedes: []
superseded_by: []
related_claims:
  - claim-governance-cost-paradox
  - claim-circuit-breakers-dominate
created: 2026-02-19
updated: 2026-02-19
---

## Quality Gate Dominates Full Governance

A simple deterministic quality gate — rejecting all interactions with p < 0.5 — achieves toxicity reduction comparable to the full governance stack while preserving near-ungoverned welfare levels.

**Evidence summary.** In the GasTown governance cost study (N=63 runs, 7 agents, 30 epochs), the "Refinery" regime (quality gate only, no tax, no circuit breakers, no collusion penalties) preserved welfare at levels close to the ungoverned baseline. Toxicity reduction was comparable to the fully governed regime, indicating that the additional governance mechanisms contribute marginal safety benefit at disproportionate welfare cost.

**Boundary conditions.** The result assumes zero friction on accepted interactions — that is, once an interaction passes the p >= 0.5 gate, it incurs no additional governance overhead. This may not hold in settings where post-acceptance monitoring or reporting is required. The test used only 7 agents; at larger scales, the binary threshold may introduce cliff effects near p = 0.5 that a softer mechanism could smooth.

**Open questions.**
- Is the p = 0.5 threshold optimal, or would a calibrated threshold improve the welfare-safety frontier?
- Does the quality gate remain effective under adversarial manipulation of the proxy score?
- How does gate performance interact with proxy miscalibration?

<!-- topics: governance, quality-gate, welfare, refinery -->
