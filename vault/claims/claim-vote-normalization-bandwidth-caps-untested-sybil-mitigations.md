---
description: "SWARM's vote_normalization and bandwidth_cap parameters have cryptographic precedent but zero experimental testing"
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: research-mechanism-design-screening-2026-02-22
    metric: parameter_coverage
    detail: 'SyRA (IACR 2024) achieves sybil resistance via rate-limiting, maps to SWARM untested vote_normalization and bandwidth_cap parameters. failure-sybil-identity-amplification recommends these but no runs exercise them'
    source_type: research
  weakening: []
  boundary_conditions:
  - Parameters exist in SWARM codebase but no runs exercise them
  - SyRA operates in a cryptographic context different from SWARM simulation
supersedes: []
superseded_by: []
related_claims:
- claim-sybil-attacks-resist-full-governance-stack
created: 2026-02-22
cssclasses:
- claim
- claim-low
tags:
- governance
- sybil
- vote-normalization
- bandwidth-cap
graph-group: claim
---

# vote normalization and bandwidth caps are untested sybil mitigations with cryptographic precedent

SWARM's codebase includes `vote_normalization` and `bandwidth_cap` governance parameters that have never been exercised in any experimental run. These parameters have direct precedent in the cryptographic sybil resistance literature (SyRA, IACR 2024) and were recommended by [[failure-sybil-identity-amplification]] as potential mitigations, but remain at zero experimental coverage.

## Evidence summary

SyRA (IACR 2024) demonstrates that rate-limiting mechanisms can achieve sybil resistance without requiring proof-of-personhood or trusted identity infrastructure. The core insight is that limiting the influence any single identity can exert per unit time bounds the advantage of identity multiplication. This maps directly to two SWARM parameters:

- **vote_normalization** — normalizes each agent's voting power, bounding the influence of any single identity regardless of stake or reputation
- **bandwidth_cap** — limits the rate at which any agent can submit contributions, bounding the throughput advantage of running multiple identities

The [[failure-sybil-identity-amplification]] failure pattern identified sybil attacks as succeeding in 100% of configurations including fully hardened stacks, and explicitly recommended testing these parameters. Despite this, no SWARM run in the `runs/` directory exercises either parameter.

## Boundary conditions

- Parameters exist in the SWARM codebase but their implementation may be incomplete or untested
- SyRA's rate-limiting operates in a cryptographic protocol context; effectiveness may differ in SWARM's simulation
- The interaction between these parameters and existing governance mechanisms (CB, tax, CD) is unknown

## Mechanism

Vote normalization works by capping the influence of each identity at 1/N of total voting power, regardless of how many identities a single controller operates. If a sybil controller runs K identities, their total influence is K/N — which grows linearly, matching the cost scaling. Bandwidth caps complement this by limiting the rate of influence exertion, preventing sybil controllers from using parallel identities to achieve throughput advantages.

## Open questions

- Are vote_normalization and bandwidth_cap fully implemented in the SWARM codebase, or are they stub parameters?
- What parameter values should the first experimental sweep test?
- Do these parameters interact with [[claim-sybil-attacks-resist-full-governance-stack|the full governance stack]], or are they orthogonal?
- Would bandwidth caps create unacceptable latency for honest agents in time-sensitive scenarios?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, sybil, vote-normalization, bandwidth-cap -->
