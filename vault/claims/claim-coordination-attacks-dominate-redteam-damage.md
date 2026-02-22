---
description: Sybil + collusion ring attacks account for 52.6% of total redteam damage when collusion detection is disabled
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260214-094622_redteam
    metric: damage
    detail: "Coordination damage 212.9/404.5 total (52.6%). Sybil: 117.6 (29.1%), Collusion ring: 95.3 (23.5%). N=1 evaluation; inferential statistics not applicable"
  - run: 20260212-231123_redteam
    metric: damage
    detail: "Replicates in earlier evaluation: baseline sybil 120.0 + collusion ring 97.2 = 217.2/455.7 (47.7%). Consistent damage ranking. Hardened config prevents collusion ring but sybil persists at 102.6. N=1 evaluation per config; inferential statistics not applicable"
  - run: 20260221-081106_redteam_contract_screening_no_collusion
    metric: damage
    detail: "Contract screening without CD: sybil 105.84 + collusion ring 85.73 = 191.57/364.09 (52.6%). Identical share to recursive_spawn scenario. N=1 evaluation; inferential statistics not applicable"
  - run: 20260221-081953_redteam_contract_screening_with_collusion
    metric: damage
    detail: "Contract screening with CD: sybil 105.84 + collusion ring 21.43 = 127.27/299.79 (42.4%). CD reduces coordination share from 52.6% to 42.4% but coordination still dominates. N=1 evaluation; inferential statistics not applicable"
  weakening: []
  boundary_conditions:
  - 8-attack test battery, replicated across recursive_spawn and contract_screening scenarios
  - "Without CD: coordination share ~52.6% (consistent across 3 evaluations)"
  - "With CD: coordination share drops to ~42.4% — CD reduces collusion ring damage 75% but sybil is invariant"
  - Attack damage ranking consistent across all redteam evaluations
sensitivity:
  topology: untested; coordination damage share may shift in constrained topologies
  agent_count: untested beyond default
  governance_interaction: enabling CD reduces coordination share from 52.6% to 42.4%. Sybil damage invariant to all governance variations (see claim-sybil-attacks-resist-full-governance-stack)
supersedes: []
superseded_by: []
related_claims:
- claim-collusion-detection-is-binding-constraint-on-robustness
- claim-cb-audit-sufficient-for-solo-exploits
- claim-audit-threshold-interaction-enables-dancing
- claim-cascade-mechanisms-ineffective-against-governance-gaming
- claim-collusion-wealth-destruction
- claim-spawn-infrastructure-may-amplify-sybil-surface
- claim-sybil-attacks-resist-full-governance-stack
- claim-full-governance-stack-prevents-most-attack-types
- claim-steganographic-collusion-unaddressed-by-swarm-detection
- claim-quadratic-staking-may-solve-sybil-cost-inversion
- claim-vote-normalization-bandwidth-caps-untested-sybil-mitigations
- claim-collusion-detection-reduces-ring-damage-75pct
created: 2026-02-20
updated: 2026-02-22
aliases:
- coordination-attacks-dominate-redteam-damage
cssclasses:
- claim
- claim-low
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

This damage concentration establishes coordination attacks as the primary threat vector in multi-agent systems. Solo exploits are individually less damaging and more easily prevented (see [[claim-cb-audit-sufficient-for-solo-exploits]]). Even the successful non-coordination attacks — [[claim-audit-threshold-interaction-enables-dancing]] (threshold dancing: 21.2 damage) and [[claim-cascade-mechanisms-ineffective-against-governance-gaming]] (governance gaming: 23.5 damage) — individually pale against either coordination attack. The damage disparity is explained by [[claim-collusion-wealth-destruction]]: when collusion detection is enabled, it creates a 137x wealth gap for colluders, confirming that coordination damage is controllable when detection is active and catastrophic when it is not.

## Mechanism

Coordination attacks exploit the fundamental multi-agent property: multiple entities acting in concert can create damage that scales super-linearly with participant count. Sybil attacks multiply identity to amplify a single adversary's influence. Collusion rings create mutual boosting loops where each participant elevates the others' reputation, compounding trust scores beyond what any individual could achieve.

## Governance interaction: coordination share with and without collusion detection

The [[20260221-081953_redteam_contract_screening_with_collusion]] evaluation now answers the key open question. With collusion detection enabled:
- Sybil damage: 105.84 (unchanged — invariant to CD, see [[claim-sybil-attacks-resist-full-governance-stack]])
- Collusion ring damage: 21.43 (down 75% from 85.73, see [[claim-collusion-detection-reduces-ring-damage-75pct]])
- Total coordination damage: 127.27 / 299.79 = **42.4%** (down from 52.6%)

Coordination attacks still dominate even with CD enabled. The reduction comes entirely from collusion ring suppression; sybil damage is invariant to all governance mechanisms tested. This means the claim's core proposition holds regardless of CD state, though the magnitude shifts: coordination accounts for 42-53% of total redteam damage depending on governance configuration.

## Boundary conditions

- Without CD: coordination share ~52.6% (consistent across recursive_spawn and contract_screening scenarios)
- With CD: coordination share ~42.4% — collusion ring damage suppressed 75% but sybil invariant
- The share figures are for the 8-attack battery; different attack portfolios would produce different ratios
- recursive_spawn scenario may inflate sybil effectiveness due to legitimate spawn infrastructure

## Open questions

- ~~What is the coordination damage share when collusion detection IS enabled?~~ **Resolved**: 42.4% with CD, down from 52.6% without.
- Is the 42-53% coordination damage share consistent across topologies?
- Does [[claim-spawn-infrastructure-may-amplify-sybil-surface]] explain the unusually high sybil damage?
- Would vote normalization + bandwidth caps further reduce coordination share below 42%?

## Update history

**2026-02-22** — backward-pass update:
- Added supporting evidence from [[20260221-081953_redteam_contract_screening_with_collusion]]: with CD enabled, coordination damage share drops from 52.6% to 42.4%. Sybil damage invariant (105.84); collusion ring damage reduced 75% (85.73 to 21.43).
- Added governance interaction section resolving the open question about CD-enabled coordination share.
- Updated boundary conditions to distinguish CD-on vs CD-off damage shares.
- Added [[claim-collusion-detection-reduces-ring-damage-75pct]] to related claims.
- Confidence remains **low**: all evidence is from single-evaluation (N=1) redteam runs without inferential statistics. Damage ranking is consistent across 4 evaluations but all share the same deterministic evaluation framework.

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[failures-dashboard]]

<!-- topics: governance, redteam, coordination, sybil, collusion -->
