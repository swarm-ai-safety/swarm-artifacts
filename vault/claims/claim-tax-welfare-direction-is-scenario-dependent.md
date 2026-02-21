---
description: Tax-welfare relationship reverses between scenarios — declines in baseline governance but increases in kernel v4 code
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260214-113750_kernel_v4_code_sweep
    metric: welfare
    detail: "Welfare increases 0%→15% tax (12.18→16.96 without CB). Contradicts 5% threshold from baseline governance sweeps. N=5 seeds, high variance"
  - run: 20260217_memori_study
    metric: welfare
    detail: "No tax sensitivity detected (d<0.23, all p>0.60). 12 tests, 0 significant after Bonferroni. N=5 seeds, 2 epochs"
  weakening: []
  boundary_conditions:
  - kernel_v4_code: 8 agents, 5 seeds per config, 5 epochs — severely underpowered
  - memori: 5 LLM agents (all honest), 5 seeds, 2 epochs — severely underpowered and no adversarial agents
  - Both studies flagged by council review for insufficient sample size
sensitivity:
  topology: untested
  agent_count: different across scenarios (5-8)
  governance_interaction: CB interacts non-monotonically with tax in kernel v4
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-tax-phase-transition
- claim-optimal-tax-range-0-to-5pct
- claim-memori-agents-show-no-governance-sensitivity
- claim-cb-tax-interaction-non-monotonic-in-kernel-v4
- claim-welfare-plateaus-above-12pct-tax
- claim-governance-cost-paradox
- claim-tax-dominates-cb-kernel
created: 2026-02-20
updated: 2026-02-20
aliases:
- tax-welfare-direction-is-scenario-dependent
cssclasses:
- claim
- claim-low
tags:
- governance
- transaction-tax
- scenario-dependence
- boundary-condition
graph-group: claim
---

# tax-welfare relationship direction is scenario-dependent

## Evidence summary

The established tax-welfare tradeoff ([[claim-tax-welfare-tradeoff]], d=1.18-4.80, high confidence) shows welfare declining above 5% tax in baseline governance scenarios. However:

- **Kernel v4 code** ([[20260214-113750_kernel_v4_code_sweep]]): welfare *increases* from 12.18 (0% tax) to 16.96 (15% tax, no CB). The direction reverses entirely.
- **Memori LLM** ([[20260217_memori_study]]): no detectable tax sensitivity (d<0.23, 0/12 tests significant). Tax appears irrelevant.

Both studies are severely underpowered (N=5 seeds), so these results are suggestive, not conclusive. But they establish an important **boundary condition** on the high-confidence tax-welfare claims: the relationship may be scenario-specific rather than universal. The kernel v4 reversal coincides with the non-monotonic CB interaction in [[claim-cb-tax-interaction-non-monotonic-in-kernel-v4]] from the same sweep, suggesting the kernel v4 scenario produces qualitatively different governance dynamics. If the tax-welfare reversal is real, the welfare S-curve of [[claim-welfare-plateaus-above-12pct-tax]] and the safe operating range of [[claim-optimal-tax-range-0-to-5pct]] may apply only to baseline governance scenarios. This would narrow the scope of [[claim-governance-cost-paradox]] — if tax increases welfare in some scenarios, governance is not universally costly. The [[claim-tax-dominates-cb-kernel]] finding from the same kernel v4 data shows tax dominance even where its welfare direction reverses, creating an unusual configuration where the strongest governance lever is also beneficial.

## Mechanism (hypothesized)

In kernel v4 code markets, tax may redistribute value toward more productive agents or reduce destructive competition, producing net positive welfare effects. In memori (all-honest LLM agents), the absence of adversarial or opportunistic agents means tax has nothing to correct — it can only extract from cooperative interactions, but at low rates the extraction is negligible.

## Open questions

- Replicate kernel v4 with 20-30 seeds per config to confirm the reversal
- What structural property of kernel_v4_code causes the reversal? Agent types? Market mechanism?
- Does the memori null result persist with adversarial agents added?

---

Topics:
- [[_index]]
- [[governance-dashboard]]
- [[transaction-tax-rate]]

<!-- topics: governance, transaction-tax, scenario-dependence, boundary-condition -->
