---
description: Enabling all governance levers prevents 5/8 attack types and reduces total damage 36%, but sybil, reputation farming, and governance gaming persist
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260212-231123_redteam
    metric: damage
    detail: "Baseline (no defenses): 6/8 attacks succeed, 455.7 total damage, 42% evasion rate. Hardened (full stack): 3/8 succeed, 290.6 total damage, 26% evasion rate. 36.2% damage reduction, 38.4% detection improvement. N=1 evaluation per config"
  - run: 20260213-151729_redteam
    metric: damage
    detail: "Graduated 4-tier progression on 3-attack battery: no_defenses 176.7, baseline(CB) 157.8, moderate(CB+audit+staking+5%tax) 114.4, strict(+CD+10%tax) 49.3. 69% reduction baseline→strict. Collusion detection provides largest marginal gain"
  weakening: []
  boundary_conditions:
  - "Single redteam evaluation, single seed — limited statistical power"
  - "Hardened config: CB + collusion detection + audit + staking + 5% tax"
  - "8-attack battery: reputation farming, collusion ring, threshold dancing, sybil, timing, laundering, resource drain, governance gaming"
  - "Grade improved from F (0.40) to D (0.66) — still below passing threshold"
sensitivity:
  topology: untested
  agent_count: untested beyond default
  governance_interaction: "Full stack interaction provides 36% improvement over no governance; marginal contribution of individual levers untested in this run"
supersedes: []
superseded_by: []
related_claims:
- claim-cb-audit-sufficient-for-solo-exploits
- claim-sybil-attacks-resist-full-governance-stack
- claim-coordination-attacks-dominate-redteam-damage
- claim-collusion-detection-is-binding-constraint-on-robustness
- claim-governance-cost-paradox
- claim-cascade-mechanisms-ineffective-against-governance-gaming
- claim-audit-threshold-interaction-enables-dancing
- claim-graduated-defense-reduces-damage-monotonically
created: 2026-02-21
updated: 2026-02-21
aliases:
- full-governance-stack-prevents-most-attack-types
cssclasses:
- claim
- claim-low
tags:
- governance
- redteam
- adversarial
- defense-in-depth
graph-group: claim
---

# Full governance stack prevents 5 of 8 attack types but residual threats persist

## Evidence summary

The [[20260212-231123_redteam]] evaluation compared an undefended baseline against a fully hardened configuration (CB + collusion detection + audit + staking + 5% tax) across an 8-attack battery.

**Attacks prevented by full stack** (0 in baseline → prevented in hardened):
- Collusion ring (97.2 → 20.8 damage, prevented)
- Threshold dancing (40.5 → 18.5, prevented)
- Timing attack (already prevented in baseline → confirmed prevented)
- Information laundering (48.0 → 41.0, prevented)
- Resource drain (60.0 → 51.3, prevented)

**Attacks persisting despite full stack:**
- Sybil attack: 120.0 → 102.6 damage (only 14.5% reduction) — see [[claim-sybil-attacks-resist-full-governance-stack]]
- Reputation farming: 39.0 → 12.8 damage (67% reduction but not fully prevented)
- Governance gaming: prevented in baseline → 20.5 damage in hardened (new vulnerability)

The paradoxical emergence of governance gaming as a hardened-only vulnerability is consistent with [[claim-cascade-mechanisms-ineffective-against-governance-gaming]]: more governance creates more mechanism seams to exploit. The collusion ring prevention validates [[claim-collusion-detection-is-binding-constraint-on-robustness]] — enabling collusion detection eliminates this attack entirely. The threshold dancing prevention in hardened mode partially contradicts [[claim-audit-threshold-interaction-enables-dancing]], suggesting the full stack's overlapping detection surfaces close the dancing window.

Overall, the full stack achieves 36% damage reduction and prevents 5/8 attack types, but receives a D grade (0.66) rather than passing. This reinforces [[claim-governance-cost-paradox]]: even maximum governance investment leaves significant residual risk, primarily from sybil attacks (35% of hardened damage).

## Mechanism

Defense-in-depth works through overlapping detection surfaces: CB handles behavioral thresholds, collusion detection catches coordination, audit provides stochastic sampling, staking imposes economic costs, and tax reduces transaction incentives. The combination closes gaps that individual mechanisms leave open. However, sybil attacks exploit a fundamentally different vector (identity multiplication) that behavioral and economic mechanisms cannot address, requiring structural defenses (vote normalization, bandwidth caps) not present in the current stack.

## Open questions

- Why does governance gaming emerge as a new vulnerability in hardened configs?
- What is the marginal contribution of each governance lever to the 36% damage reduction?
- Would adding vote normalization and bandwidth caps close the sybil gap and raise the grade above D?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[failures-dashboard]]

<!-- topics: governance, redteam, adversarial, defense-in-depth -->
