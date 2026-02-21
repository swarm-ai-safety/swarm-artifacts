---
description: Write cap k_max<=6 destroys up to 75% of welfare with zero toxicity benefit; k_max>=12 imposes zero overhead
type: claim
status: active
confidence: low
domain: memory
evidence:
  supporting:
  - run: 20260214-020518_tau_k_calibration
    metric: total_welfare
    detail: "k=2: welfare 91 (75% reduction vs baseline 368), 271 cap hits, toxicity unchanged at 0.313. k=4: welfare 228 (38% reduction). k=6: welfare 300 (19% reduction)"
  - run: 20260214-014153_tau_k_calibration
    metric: write_cap_hits
    detail: "k=12,16,20: zero write_cap_hits across all seeds and tau values. Memory writes ~440-455/run, cap never binds"
  weakening: []
  boundary_conditions:
  - memory_tiers scenario, non-adversarial (0% adversarial fraction)
  - 10 epochs, 8 steps/epoch, 5 seeds per cell
  - k_max threshold between 6 and 12 is uncharacterized
sensitivity:
  topology: untested
  agent_count: 8 agents; write patterns may differ with more agents
  governance_interaction: write cap compounds with tau rejection at tau=0.65
supersedes: []
superseded_by: []
related_claims:
- claim-governance-cost-paradox
- claim-memory-promotion-gate
- claim-tau-065-triggers-acceptance-phase-transition
- claim-optimal-tau-range-050-to-060
- claim-quality-gate-dominates
- claim-staking-backfires
created: 2026-02-20
updated: 2026-02-20
aliases:
- write-cap-below-12-destroys-welfare
cssclasses:
- claim
- claim-low
tags:
- memory
- calibration
- governance-cost
graph-group: claim
---

# write cap k_max below 12 destroys welfare without safety benefit while k_max above 12 imposes zero overhead

## Evidence summary

In the [[20260214-020518_tau_k_calibration]] and [[20260214-014153_tau_k_calibration]] calibration runs:

| k_max | Welfare | % of baseline | Cap hits/run | Toxicity |
|-------|---------|---------------|--------------|----------|
| 2 | 91 | 25% | 271 | 0.313 |
| 4 | 228 | 62% | 140 | 0.313 |
| 6 | 300 | 81% | 61 | 0.313 |
| 12 | 355-374 | ~100% | 0 | 0.313 |
| 16 | 355-374 | ~100% | 0 | 0.313 |
| 20 | 355-374 | ~100% | 0 | 0.313 |

Toxicity is unchanged across all k values — the write cap provides **zero safety benefit** at any level. Below k=12, it only destroys welfare. This is a memory-domain instance of [[claim-governance-cost-paradox]]: governance overhead with no compensating safety improvement. The write cap is the anti-[[claim-quality-gate-dominates]] — whereas a quality gate achieves safety at near-zero welfare cost, the write cap achieves zero safety at severe welfare cost. The pattern also parallels [[claim-staking-backfires]], where another governance mechanism penalizes honest agents without deterring adversarial behavior.

## Mechanism

The write cap limits the number of memory writes per epoch per agent. At low k values, agents exhaust their write budget early in the epoch, preventing them from recording subsequent interactions. This destroys information flow without affecting the quality of interactions (hence unchanged toxicity). At k>=12, the cap exceeds the natural write rate (~440 writes / 10 epochs / 8 agents ≈ 5.5 writes/epoch/agent), so it never binds.

## Open questions

- What is the exact k_max threshold where cap hits reach zero? Between 6 and 12.
- Would adversarial agents exploit unlimited writes if k_max is removed? The non-adversarial setting may be misleading.
- Is there a k_max that provides memory poisoning defense without welfare cost?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: memory, calibration, governance-cost -->
