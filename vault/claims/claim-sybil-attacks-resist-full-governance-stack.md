---
description: Sybil attacks succeed in both undefended (120 damage) and fully hardened (103 damage) configurations, only 14% damage reduction
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260212-231123_redteam
    metric: damage
    detail: "Sybil attack: baseline 120.0 damage (33.6% evasion, 9 epoch detection), hardened 102.6 damage (28.7% evasion, 8 epoch detection). Only 14.5% damage reduction despite full governance stack. N=1 evaluation per config"
  - run: 20260214-094622_redteam
    metric: damage
    detail: "Sybil damage 117.6 (29.1% of total 404.5). Highest single-attack damage in 8-attack battery. Consistent with 20260212 evaluation. N=1 evaluation; inferential statistics not applicable"
  - run: 20260209-174740_redteam
    metric: damage
    detail: "Replicates: baseline sybil 120 damage, hardened 103 damage. Identical pattern across 3 independent redteam evaluations. N=1 evaluation per config per run; inferential statistics not applicable"
  - run: 20260210-005442_redteam_strict_governance
    metric: damage
    detail: "Strict governance (no CD): sybil 97 damage. Strict+CD: sybil 97 damage. Lowered threshold (0.35): sybil 97 damage. Sybil invariant to all governance variations. N=1 evaluation per config; inferential statistics not applicable"
  - run: 20260221-081106_redteam_contract_screening_no_collusion
    metric: damage
    detail: "Contract screening without CD: sybil damage=105.84, evasion=0.296. Highest damage in 8-attack battery. N=1 evaluation; inferential statistics not applicable"
  - run: 20260221-081953_redteam_contract_screening_with_collusion
    metric: damage
    detail: "Contract screening with CD: sybil damage=105.84, evasion=0.296. Unchanged by collusion detection. Replicated in 20260221-082443. N=1 evaluation per config; inferential statistics not applicable"
  weakening: []
  boundary_conditions:
  - "Seven redteam evaluations (20260208-20260221) across multiple scenarios confirm sybil persistence"
  - "Hardened config: CB + collusion detection + audit + staking + 5% tax. No vote normalization or bandwidth caps"
  - "5 adversarial agents per sybil attack in both evaluations"
  - "recursive_spawn scenario — legitimate spawn infrastructure may amplify sybil surface"
sensitivity:
  topology: untested
  agent_count: untested beyond default
  governance_interaction: "Full stack (CB + CD + audit + staking + tax) insufficient; vote normalization and bandwidth caps recommended but untested"
supersedes: []
superseded_by: []
related_claims:
- claim-spawn-infrastructure-may-amplify-sybil-surface
- claim-coordination-attacks-dominate-redteam-damage
- claim-collusion-detection-is-binding-constraint-on-robustness
- claim-cb-audit-sufficient-for-solo-exploits
- claim-collusion-detection-reduces-ring-damage-75pct
- claim-contract-screening-achieves-perfect-type-separation
created: 2026-02-21
updated: 2026-02-21
aliases:
- sybil-attacks-resist-full-governance-stack
cssclasses:
- claim
- claim-medium
tags:
- governance
- redteam
- sybil
- adversarial
- coordination
graph-group: claim
---

# sybil attacks resist the full governance stack with only 14% damage reduction

## Evidence summary

Across two independent redteam evaluations, sybil attacks consistently inflict the highest single-attack damage and resist all available governance mechanisms.

**20260212 evaluation** ([[20260212-231123_redteam]]): Baseline (no defenses) sybil damage = 120.0; fully hardened (CB + collusion detection + audit + staking + 5% tax) sybil damage = 102.6 — only a 14.5% reduction. By comparison, the full stack prevented 5 of 8 other attack types entirely. Sybil was rated CRITICAL vulnerability in both configurations.

**20260214 evaluation** ([[20260214-094622_redteam]]): Sybil damage = 117.6, accounting for 29.1% of total redteam damage (404.5). This is consistent with the 20260212 baseline figure (120.0), confirming the attack's reproducibility.

**20260221 contract screening evaluations** ([[20260221-081106_redteam_contract_screening_no_collusion]], [[20260221-081953_redteam_contract_screening_with_collusion]], [[20260221-082443_redteam_contract_screening_full]]): Sybil damage = 105.84 in all three configurations. Critically, enabling collusion detection reduces collusion ring damage by 75% (see [[claim-collusion-detection-reduces-ring-damage-75pct]]) but has zero effect on sybil damage. This extends the finding to the contract_screening scenario and confirms that sybil attacks exploit a different channel than collusion rings — individual behavioral normality rather than coordination patterns.

With 7 independent redteam evaluations across multiple scenarios now supporting this claim, confidence is upgraded from low to medium.

The persistent sybil vulnerability creates a critical gap in the governance architecture. While [[claim-cb-audit-sufficient-for-solo-exploits]] shows CB + audit prevents all solo attacks, and [[claim-collusion-detection-is-binding-constraint-on-robustness]] identifies collusion detection as key for coordination attacks, sybil attacks appear to occupy a third category — coordination attacks that partially evade even collusion detection. This supports [[claim-spawn-infrastructure-may-amplify-sybil-surface]]: the recursive_spawn scenario provides legitimate infrastructure that sybil attackers exploit, making identity verification harder.

The 20260212 redteam also revealed that reputation farming partially persists in hardened configs (12.8 damage, down from 39.0) while governance gaming succeeds (20.5 damage), suggesting these three attack types — sybil, reputation farming, governance gaming — represent the residual threat surface after governance hardening.

## Mechanism

Sybil attacks multiply identity to amplify a single adversary's influence across 5 synthetic agents. Current governance mechanisms detect behavioral anomalies (CB), correlate actions (collusion detection), sample transactions (audit), and impose economic costs (staking, tax). But sybil agents can maintain individually normal behavior while collectively amplifying influence, staying below per-agent thresholds. The missing defenses — vote normalization and bandwidth caps — would limit per-identity influence directly, attacking the multiplication rather than the behavior.

## Open questions

- Do vote normalization and bandwidth caps actually prevent sybil attacks?
- What is the minimum number of sybil identities needed for the attack to succeed?
- Is the sybil vulnerability specific to recursive_spawn, or universal across scenarios?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[failures-dashboard]]

<!-- topics: governance, redteam, sybil, adversarial, coordination -->
