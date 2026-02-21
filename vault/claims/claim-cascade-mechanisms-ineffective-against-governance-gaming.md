---
description: Governance gaming succeeds (23.5 damage) even with cascade_ban and cascade_freeze enabled, targeting mechanism seams
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260214-094622_redteam
    metric: damage
    detail: "governance_gaming: damage 23.52, evasion_rate 0.329, never detected. cascade_ban=true, cascade_freeze=true"
  weakening: []
  boundary_conditions:
  - recursive_spawn scenario, expert-difficulty single adversary
  - All standard levers active except collusion detection and staking
  - Cascade mechanisms address spawn hierarchies, not single-agent loophole exploitation
  - Single run
sensitivity:
  topology: untested
  agent_count: untested
  governance_interaction: cascade mechanisms are orthogonal to governance gaming vector
supersedes: []
superseded_by: []
related_claims:
- claim-cb-audit-sufficient-for-solo-exploits
- claim-collusion-detection-is-binding-constraint-on-robustness
- claim-coordination-attacks-dominate-redteam-damage
- claim-audit-threshold-interaction-enables-dancing
- claim-quality-gate-dominates
- claim-spawn-infrastructure-may-amplify-sybil-surface
created: 2026-02-20
updated: 2026-02-20
aliases:
- cascade-mechanisms-ineffective-against-governance-gaming
cssclasses:
- claim
- claim-low
tags:
- governance
- governance-gaming
- cascade
- adversarial
graph-group: claim
---

# cascade ban and freeze mechanisms are ineffective against governance gaming attacks

## Evidence summary

In the [[20260214-094622_redteam]] evaluation, the [[failure-governance-gaming-loophole-exploitation]] attack succeeded with 23.52 damage and 0.329 evasion rate despite cascade_ban = true and cascade_freeze = true being enabled. The adversary was never detected across 20 epochs.

Cascade mechanisms (cascade_ban, cascade_freeze) are designed to propagate governance actions through spawn hierarchies: if a parent agent is frozen or banned, its spawned children inherit the governance action. However, governance gaming targets **mechanism seams** — gaps between governance levers — rather than exploiting any single mechanism. The adversary finds sequences of individually-compliant actions that collectively produce harmful outcomes, a strategy that cascade propagation does not address.

## Mechanism

Governance gaming operates at a different abstraction level than cascade mechanisms. Cascade addresses vertical propagation (parent → child) while gaming exploits horizontal gaps (between mechanisms). The adversary identifies action sequences where: (1) each action is below CB freeze threshold, (2) no single transaction triggers audit flags, (3) the cumulative effect creates damage through mechanism blind spots. Adding cascade mechanisms does not close these horizontal gaps.

## Boundary conditions

- Single run with recursive_spawn scenario; gaming effectiveness may differ in non-spawn scenarios
- Expert-difficulty adversary; less sophisticated adversaries may not find the mechanism seams
- Collusion detection and staking were disabled; they might provide cross-cutting detection that closes some seams

## Connections

Cascade ineffectiveness against gaming parallels [[claim-collusion-detection-is-binding-constraint-on-robustness]]: both reveal that governance mechanisms have dimensional blind spots — cascade addresses vertical (parent-child) propagation while gaming exploits horizontal (inter-mechanism) gaps. This positions governance gaming as an intermediate threat between solo exploits (fully prevented by CB + audit per [[claim-cb-audit-sufficient-for-solo-exploits]]) and coordination attacks (dominant per [[claim-coordination-attacks-dominate-redteam-damage]]). The structural similarity with [[claim-audit-threshold-interaction-enables-dancing]] is notable: both expose parameter-specific blind spots where individually compliant behavior accumulates harm. [[claim-quality-gate-dominates]] faces the same limitation — a quality gate addresses transaction-level quality but not inter-mechanism seam exploitation. [[claim-spawn-infrastructure-may-amplify-sybil-surface]] extends the concern: cascade mechanisms govern spawn hierarchies, but neither cascade nor gaming defenses address identity-level attacks that bypass the governance stack entirely.

## Open questions

- Would enabling collusion detection reduce governance gaming success? Gaming behavior may look like anomalous coordination patterns even from a single agent.
- Is there a governance mechanism specifically designed to detect cumulative harm from individually-compliant actions?
- Does the 0.329 evasion rate represent a hard floor, or could mechanism-aware adversaries achieve higher evasion?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[failures-dashboard]]

<!-- topics: governance, governance-gaming, cascade, adversarial -->
