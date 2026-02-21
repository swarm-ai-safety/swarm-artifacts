---
description: Recursive spawn infrastructure (max_depth=3, max_total=50) may provide cover for sybil identity creation
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260214-094622_redteam
    metric: damage
    detail: "Sybil attack caused highest damage (117.6) in recursive_spawn scenario with spawn_enabled=true, spawn_max_depth=3, spawn_max_total=50"
  weakening: []
  boundary_conditions:
  - Open question; no direct evidence of spawn-sybil interaction, only structural concern
  - Sybil succeeds in 100% of configs (per failure-sybil-identity-amplification), so spawn may not be the cause
  - Single run
sensitivity:
  topology: untested
  agent_count: untested
  governance_interaction: spawn governance (cascade_ban/freeze) does not address sybil identity verification
supersedes: []
superseded_by: []
related_claims:
- claim-coordination-attacks-dominate-redteam-damage
- claim-collusion-detection-is-binding-constraint-on-robustness
- claim-cascade-mechanisms-ineffective-against-governance-gaming
- claim-staking-backfires
created: 2026-02-20
updated: 2026-02-20
aliases:
- spawn-infrastructure-may-amplify-sybil-surface
cssclasses:
- claim
- claim-low
tags:
- governance
- sybil
- spawn
- open-question
graph-group: claim
---

# recursive spawn infrastructure may amplify sybil attack surface

## Evidence summary

In the [[20260214-094622_redteam]] evaluation, the [[failure-sybil-identity-amplification]] attack caused the highest individual damage (117.6) in a scenario using recursive_spawn with spawn_enabled = true, spawn_max_depth = 3, and spawn_max_total = 50. The structural concern: legitimate spawn infrastructure creates a mechanism for identity multiplication that sybil attackers could exploit to create identities indistinguishable from legitimate spawned agents.

However, this is currently an **open question**, not a confirmed finding. [[failure-sybil-identity-amplification]] reports 100% success rate across all configurations including fully hardened stacks, so the high damage may not be spawn-specific — sybil attacks may simply be universally effective regardless of spawn settings.

## Mechanism (hypothesized)

In spawn-enabled scenarios, agents can create child agents as part of normal operation. A sybil attacker could create malicious child agents that appear identical to legitimate spawns — same creation pathway, same initial parameters, same parent-child relationship structure. This would make sybil detection harder because the baseline rate of new identity creation is high, masking adversarial identity multiplication in the noise of legitimate spawning.

## Connections

This claim extends [[claim-coordination-attacks-dominate-redteam-damage]] by hypothesizing a scenario-specific amplifier for the sybil component of coordination damage. It also extends [[claim-collusion-detection-is-binding-constraint-on-robustness]]: if spawn infrastructure amplifies the sybil surface, collusion detection becomes even more critical in spawn-enabled scenarios. [[claim-cascade-mechanisms-ineffective-against-governance-gaming]] reveals that cascade mechanisms govern spawn hierarchies (parent-child propagation) but not identity verification — the same gap this claim identifies. A potential mitigation through proof-of-stake identity binding connects to [[claim-staking-backfires]]: staking-as-identity-cost could address sybil multiplication, but staking backfires against honest agents, creating a design tension between sybil defense and honest-agent welfare.

## Open questions

- Run the same redteam battery with spawn_enabled = false to measure sybil damage differential
- Does spawn_max_total cap sybil effectiveness, or can sybil attackers work within the cap?
- Would requiring identity verification for spawned agents (not just cascade governance) address this?
- Is the 117.6 damage statistically higher than sybil damage in non-spawn scenarios from prior runs?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[failures-dashboard]]

<!-- topics: governance, sybil, spawn, open-question -->
