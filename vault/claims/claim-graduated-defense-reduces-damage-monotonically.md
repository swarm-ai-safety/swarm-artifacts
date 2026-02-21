---
description: Adding governance layers progressively reduces redteam damage from 157.8 (baseline) to 49.3 (strict), a 69% monotonic reduction
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260213-151729_redteam
    metric: damage
    detail: "4-tier progression: no_defenses 176.7, baseline(CB only) 157.8, moderate(CB+audit+staking+5%tax) 114.4, strict(+collusion_detection+10%tax) 49.3. 69% reduction baseline→strict. Evasion rate: 52%→43%→28%→17%"
  - run: 20260212-231123_redteam
    metric: damage
    detail: "2-tier comparison: baseline 455.7, hardened 290.6. 36% reduction. Consistent direction with graduated finding"
  weakening: []
  boundary_conditions:
  - "3-attack battery (reputation farming, collusion ring, threshold dancing) vs 8-attack battery in other redteams"
  - "Single seed per configuration — limited statistical power"
  - "Strict config (10% tax) may impose welfare costs per claim-tax-welfare-tradeoff"
  - "No-defenses config paradoxically prevents all 3 attacks (natural dynamics) — damage measured as absorbed harm, not attack success"
sensitivity:
  topology: untested
  agent_count: untested beyond default
  governance_interaction: "Each layer adds marginal protection; collusion detection provides largest marginal reduction (114.4→49.3)"
supersedes: []
superseded_by: []
related_claims:
- claim-full-governance-stack-prevents-most-attack-types
- claim-sybil-attacks-resist-full-governance-stack
- claim-collusion-detection-is-binding-constraint-on-robustness
- claim-governance-cost-paradox
- claim-cb-audit-sufficient-for-solo-exploits
- claim-tax-welfare-tradeoff
created: 2026-02-21
updated: 2026-02-21
aliases:
- graduated-defense-reduces-damage-monotonically
cssclasses:
- claim
- claim-low
tags:
- governance
- redteam
- defense-in-depth
- adversarial
graph-group: claim
---

# graduated governance defense reduces adversarial damage monotonically across 4 tiers

## Evidence summary

The [[20260213-151729_redteam]] evaluation tested 4 progressive governance tiers against a 3-attack battery (reputation farming, collusion ring, threshold dancing):

| Tier | Config | Total damage | Evasion rate | Attacks prevented |
|------|--------|-------------|--------------|-------------------|
| None | All disabled | 176.7 | 52.2% | 3/3 (paradoxical) |
| Baseline | CB only | 157.8 | 43.4% | 1/3 |
| Moderate | CB + audit + staking + 5% tax | 114.4 | 27.5% | 1/3 |
| Strict | + collusion detection + 10% tax | 49.3 | 16.9% | 2/3 |

Damage reduction is monotonic: each additional governance layer reduces total damage. The largest marginal improvement comes from adding collusion detection (moderate→strict: 114.4→49.3, -57%), validating [[claim-collusion-detection-is-binding-constraint-on-robustness]].

The [[20260212-231123_redteam]] 8-attack evaluation confirms the direction: undefended 455.7 → hardened 290.6 (-36%). The smaller reduction percentage likely reflects the inclusion of sybil attacks, which resist all governance layers ([[claim-sybil-attacks-resist-full-governance-stack]]).

A key nuance: the "no defenses" tier paradoxically prevents all 3 attacks through natural system dynamics (agents naturally punish bad actors through reputation), though it absorbs the highest total damage. This means governance layers don't prevent attacks that would otherwise succeed — they reduce the damage absorbed before detection.

## Mechanism

Each governance layer addresses a different attack surface: CB detects behavioral anomalies, audit provides stochastic sampling, staking imposes economic costs, tax reduces transaction incentives, and collusion detection identifies coordination. The monotonic damage reduction suggests these surfaces are complementary rather than redundant — each closes a gap the others leave open. This is consistent with [[claim-governance-cost-paradox]]: the welfare cost of each layer must be weighed against its marginal security benefit.

## Open questions

- What is the marginal cost (welfare loss) of each governance layer, enabling cost-benefit analysis?
- Does the monotonic reduction hold with sybil attacks included (or does sybil create a floor)?
- Is the optimal tier "moderate" or "strict" when accounting for both security and welfare?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[failures-dashboard]]

<!-- topics: governance, redteam, defense-in-depth, adversarial -->
