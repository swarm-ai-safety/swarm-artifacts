---
description: Sybil + collusion ring attacks account for 52.6% of total redteam damage when collusion detection is disabled
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260214-094622_redteam
    metric: damage
    detail: "Coordination damage 212.9/404.5 total (52.6%). Sybil: 117.6 (29.1%), Collusion ring: 95.3 (23.5%)"
  weakening: []
  boundary_conditions:
  - 8-attack test battery, recursive_spawn scenario
  - collusion_detection_enabled = false
  - Attack damage ranking consistent across prior redteam evaluations
sensitivity:
  topology: untested; coordination damage share may shift in constrained topologies
  agent_count: untested beyond default
  governance_interaction: enabling collusion detection would reduce coordination damage but not eliminate it
supersedes: []
superseded_by: []
related_claims:
- claim-collusion-detection-is-binding-constraint-on-robustness
- claim-cb-audit-sufficient-for-solo-exploits
created: 2026-02-20
updated: 2026-02-20
aliases:
- coordination-attacks-dominate-redteam-damage
cssclasses:
- claim
- claim-medium
tags:
- governance
- redteam
- coordination
- sybil
- collusion
graph-group: claim
---

# coordination attacks account for over half of total redteam damage when collusion detection is disabled

## Evidence summary

In the [[20260214-094622_redteam]] evaluation (8-attack battery), the two coordination attacks — [[failure-sybil-identity-amplification]] (117.6 damage, 29.1%) and [[failure-collusion-ring-mutual-boosting]] (95.3 damage, 23.5%) — together account for 212.9 of 404.5 total damage (52.6%). The remaining six attacks, including two other successes (threshold dancing: 21.2, governance gaming: 23.5) and four prevented attacks, contributed the other 47.4%.

This damage concentration establishes coordination attacks as the primary threat vector in multi-agent systems. Solo exploits are individually less damaging and more easily prevented (see [[claim-cb-audit-sufficient-for-solo-exploits]]).

## Mechanism

Coordination attacks exploit the fundamental multi-agent property: multiple entities acting in concert can create damage that scales super-linearly with participant count. Sybil attacks multiply identity to amplify a single adversary's influence. Collusion rings create mutual boosting loops where each participant elevates the others' reputation, compounding trust scores beyond what any individual could achieve.

## Boundary conditions

- Collusion detection disabled; with detection enabled, coordination damage is substantially reduced in prior runs
- The 52.6% figure is for this specific attack battery; different attack portfolios would produce different ratios
- recursive_spawn scenario may inflate sybil effectiveness due to legitimate spawn infrastructure

## Open questions

- What is the coordination damage share when collusion detection IS enabled?
- Is the 50%+ coordination damage share consistent across topologies?
- Does [[claim-spawn-infrastructure-may-amplify-sybil-surface]] explain the unusually high sybil damage?

---

Topics:
- [[_index]]

<!-- topics: governance, redteam, coordination, sybil, collusion -->
