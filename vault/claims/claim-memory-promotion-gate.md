---
description: Quality-based promotion gate blocks 100% of poisoned content from reaching higher memory tiers
type: claim
status: active
confidence: low
domain: memory
evidence:
  supporting:
  - run: 20260211-232952_gastown_composition_study
    metric: tier_poisoning_rate
    detail: Ephemeral tier 50.7% poisoned, tier 2+ 0.0% poisoned, single seed
  weakening: []
  boundary_conditions:
  - 20 epochs, 9 agents, quality threshold p>=0.5, single seed=42
sensitivity:
  topology: Not directly topology-dependent; promotion gate operates on per-item quality scores
  agent_count: 9 agents; adversarial saturation may overwhelm the gate at higher ratios
supersedes: []
superseded_by: []
related_claims:
- claim-quality-gate-dominates
- claim-governance-cost-paradox
created: 2026-02-19
updated: 2026-02-19
aliases:
- memory-promotion-gate
- quality-based-promotion-gate-blocks-100-of
cssclasses:
- claim
- claim-low
tags:
- memory
- governance
- poisoning
- promotion-gate
graph-group: claim
---

## Memory Promotion Gate

A quality-based promotion gate with threshold p >= 0.5 blocks 100% of poisoned content from reaching memory tiers 2 and above, despite 50.7% poisoning in the ephemeral tier.

**Evidence summary.** In the memory tiers study (20 epochs, 9 agents, seed=42), the ephemeral tier accumulated 50.7% poisoned entries. The promotion gate, which requires p >= 0.5 for advancement to tier 2, filtered all poisoned content perfectly — no poisoned entries were observed in tier 2 or above. This demonstrates that the same quality gate mechanism effective for interaction filtering (see [[claim-quality-gate-dominates]]) generalizes to memory tier promotion. The result also extends [[claim-governance-cost-paradox]] by showing that a simple, zero-overhead gate achieves perfect defense in the memory domain without imposing the welfare costs of the full governance stack.

**Boundary conditions.** This is a single-seed result with only 9 agents and 20 epochs. The 100% blocking rate is likely an artifact of the small sample and the gap between poisoned content quality scores and the threshold. In larger runs or under adversarial optimization of quality scores, some poisoned content may approach or exceed the threshold. The confidence is rated low because the perfect blocking rate has not been stress-tested.

**Threat model.** The promotion gate's fixed p >= 0.5 threshold is structurally analogous to the circuit breaker freeze threshold exploited in [[failure-threshold-dancing]] — adversaries who learn the gate threshold could craft content calibrated to score just above it while remaining poisoned. Similarly, [[failure-information-laundering-via-proxies]] suggests that adversaries could route poisoned content through proxy agents whose quality scoring inflates apparent content quality, bypassing the gate. The [[failure-reputation-farming-exploit]] pattern demonstrates that trust-based thresholds can be gamed through behavioral accumulation — an adversary building a history of high-quality contributions could calibrate poisoned content to pass the gate.

**Open questions.**
- At what adversarial penetration rate does the promotion gate begin to leak?
- Can adversarial agents craft content that scores above p = 0.5 while still being poisoned? (See [[failure-threshold-dancing]] for analogous threshold gaming.)
- Does the promotion gate interact with the proxy calibration — i.e., would a miscalibrated proxy allow poisoned content through? (See [[failure-information-laundering-via-proxies]] for proxy-based evasion.)
- What is the false-rejection rate for legitimate content near the threshold?

<!-- topics: memory, governance, poisoning, promotion-gate -->
