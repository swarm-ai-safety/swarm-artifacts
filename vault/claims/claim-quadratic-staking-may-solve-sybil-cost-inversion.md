---
description: "Super-linear staking costs per identity would impose escalating costs on sybil controllers while preserving flat costs for honest agents"
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: research-mechanism-design-screening-2026-02-22
    metric: sybil_cost_ratio
    detail: 'HCO (arXiv:2601.03923) formally proves linear sybil cost enforcement. SWARM flat staking hurts honest agents (d=0.41, p=0.37 per claim-staking-backfires). Quadratic staking would cost N^2 for N sybil identities vs N for N honest agents'
    source_type: research
  weakening: []
  boundary_conditions:
  - Requires mechanism for detecting identity clusters to apply super-linear costs
  - Assumes sybil controller manages multiple identities from a single resource pool
supersedes: []
superseded_by: []
related_claims:
- claim-staking-backfires
- claim-sybil-attacks-resist-full-governance-stack
created: 2026-02-22
cssclasses:
- claim
- claim-low
tags:
- governance
- sybil
- staking
- mechanism-design
graph-group: claim
---

# quadratic staking may solve the sybil cost inversion by imposing super-linear costs on identity multiplication

SWARM's current flat staking requirement creates a cost inversion: [[claim-staking-backfires|staking hurts honest agents more than adversarial ones]] because adversarial agents extract enough value from attacks to amortize the staking cost. Quadratic (or more generally, super-linear) staking would flip this dynamic by making the cost of maintaining N identities grow as N^2, while honest agents operating single identities pay a flat cost.

## Evidence summary

HCO (arXiv:2601.03923) formally proves that linear sybil cost enforcement is achievable through cryptographic mechanisms that impose per-identity costs scaling linearly with the number of identities controlled. SWARM's current flat staking mechanism fails to achieve even this: [[claim-staking-backfires|staking has d=0.41 effect against honest agents but p=0.37 against adversarial, suggesting no reliable anti-sybil effect]].

The theoretical proposal is: if staking cost for agent i's k-th identity is proportional to k (rather than constant), then a sybil controller running N identities pays 1+2+...+N = N(N+1)/2 total stake, while N honest agents each pay 1, for a total of N. The sybil controller's cost grows quadratically while honest agents' costs grow linearly. At N=5 sybil identities, the sybil controller pays 3x more per identity than an honest agent.

This maps to SWARM as a modification to the staking governance parameter: instead of `stake_amount: fixed`, use `stake_amount: f(identity_count)` with super-linear scaling.

## Boundary conditions

- Requires a mechanism for detecting or constraining identity clusters — without this, sybil controllers simply create independent-looking identities
- Assumes sybil controllers manage multiple identities from a single resource pool (may not hold if identities are funded independently)
- The formal proofs in HCO rely on cryptographic primitives (proof-of-personhood) not directly available in SWARM's simulation

## Mechanism

Super-linear staking works by exploiting an asymmetry between honest agents and sybil controllers: honest agents need exactly one identity, while sybil controllers need many. Any cost function that grows faster than linearly with the number of identities disproportionately penalizes the sybil strategy. The quadratic form is the simplest super-linear option and has closed-form cost analysis.

## Open questions

- How does SWARM detect or constrain identity clusters in practice? Without this, quadratic staking cannot be applied
- What is the minimum super-linearity exponent (between 1 and 2) needed to flip the cost inversion?
- Does [[claim-sybil-attacks-resist-full-governance-stack|sybil resistance]] improve with quadratic staking, or do sybil controllers adapt by reducing identity count?
- Could quadratic staking interact with the [[claim-governance-cost-paradox|governance cost paradox]] — is the welfare cost acceptable?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, sybil, staking, mechanism-design -->
