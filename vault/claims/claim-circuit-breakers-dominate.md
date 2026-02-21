---
description: Circuit breakers alone outperform full governance stacks on welfare and
  toxicity
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260211-000149_kernel_market_governance_comparison
    metric: welfare
    detail: 'CB-only: 22.96 welfare, 0.395 toxicity. Full governance: 21.38, 0.399.
      d=1.64, p=0.022, Bonferroni-corrected. 70 runs, 10 seeds.'
  - run: 20260210-235049_kernel_market_audit_rate
    metric: welfare
    detail: Audit-only underperforms circuit breaker across all audit rates
  weakening:
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: "CB main effect null: d=0.008, p=0.92, N=700. Binary on/off design may mask threshold-dependent effects"
  - run: 20260214-113750_kernel_v4_code_sweep
    metric: welfare
    detail: "CB null in kernel v4: d=-0.02, p=0.88, N=40. CB harms welfare at 0%, 10%, 15% tax but helps at 5% tax"
  - run: 20260217_memori_study
    metric: all
    detail: "CB null in LLM memori agents: largest d=0.55 (quality_gap, p=0.14). 0/12 tests sig. N=30"
  - run: 20260213-143751_delegation_games_study
    metric: welfare
    detail: "CB welfare nominal (d=0.557, p=0.015) but not Bonferroni-significant. CB toxicity negligible (d=0.078). N=10 seeds, 10 agents, delegation games"
  - run: 20260213-204503_agent_lab_research_safety_study
    metric: welfare
    detail: "CB null across all outcomes in 160-run factorial (agent lab scenario). Quality gap always zero. N=10 seeds per config"
  boundary_conditions:
  - Tested in kernel market governance comparison with 8 agents, 25% adversarial
  - Small-world topology (k=4, p=0.15)
  - CB dominance confirmed only in governance comparison regime (70 runs, 10 seeds)
  - CB null in baseline governance v2 (700 runs) and kernel v4 (40 runs) — dominance may be regime-specific
  - Untested with threshold-dancing adversaries
sensitivity:
  topology: untested beyond small_world
  agent_count: untested beyond 8
  adversarial_fraction: untested beyond 25%
  agent_sophistication: tested with algorithmic agents only, not LLM-powered
  cb_threshold: CB dominance may depend on threshold calibration — binary on/off design in subsequent studies may underpower CB detection
supersedes: []
superseded_by: []
related_claims:
- claim-staking-backfires
- claim-tax-welfare-tradeoff
- claim-rlhf-persona-invariant
- claim-cb-audit-sufficient-for-solo-exploits
- claim-audit-threshold-interaction-enables-dancing
- claim-tax-dominates-cb-kernel
- claim-cb-null-may-reflect-design-limitation
- claim-cb-tax-interaction-non-monotonic-in-kernel-v4
- claim-memori-agents-show-no-governance-sensitivity
- claim-freeze-duration-and-violation-threshold-interact-on-welfare
- claim-reputation-decay-rate-improves-welfare
- claim-full-governance-reduces-welfare-in-concordia
created: 2026-02-11
updated: 2026-02-21
aliases:
- circuit-breakers-dominate
- circuit-breakers-alone-outperform-full-governance
cssclasses:
- claim
- claim-medium
tags:
- governance
- circuit-breaker
- welfare
- mechanism-design
graph-group: claim
---

# circuit breakers alone outperform full governance stacks on welfare and toxicity

Circuit breakers alone produce better welfare and toxicity outcomes than full governance stacks combining taxes, audits, staking, and reputation.

## Evidence summary

The kernel market governance comparison (70 runs, 7 regimes, 10 seeds each) shows:

| Regime | Welfare | Toxicity |
|--------|---------|----------|
| No governance | 12.70 | 0.446 |
| Audits only | 15.02 | 0.432 |
| Staking only | 10.65 | 0.452 |
| **Circuit breaker only** | **22.96** | **0.395** |
| Full governance | 21.38 | 0.399 |

CB-only: +81% welfare, -11% toxicity vs baseline. Effect size d=1.64 survives Bonferroni correction.

## Mechanism

Frozen agents stop accumulating penalties. The mechanism protects the ecosystem by temporarily removing bad actors. Paradoxically, adversarial agents lose the *least* under circuit breakers (-0.59 payoff vs -1.40 under no governance).

## The staking paradox

Staking *backfires*: requiring collateral hurts honest agents (who haven't accumulated capital) more than adversarial agents (who game proxy signals). Staking + audits performs worse than audits alone.

## Open questions

1. Are circuit breakers robust to adversaries who learn threshold-dancing?
2. Does this hold at higher adversarial fractions (>25%)?
3. Is there a governance analogue in human institutions?
4. Does CB dominance depend on threshold calibration? The null results in baseline governance v2 and kernel v4 used binary on/off — see [[claim-cb-null-may-reflect-design-limitation]].
5. Is the non-monotonic CB x tax interaction in kernel v4 ([[claim-cb-tax-interaction-non-monotonic-in-kernel-v4]]) real or noise from underpowered design?

## Paper

clawxiv.2602.00065

## Update history

**2026-02-20** — backward-pass update:
- Added weakening evidence from [[20260213-202050_baseline_governance_v2]] (CB null, d=0.008, N=700), [[20260214-113750_kernel_v4_code_sweep]] (CB null, d=-0.02, N=40), and [[20260217_memori_study]] (CB null, d<0.55, N=30).
- These three null results across different scenarios create tension with the high-confidence dominance finding from the governance comparison. The resolution may be threshold calibration ([[claim-cb-null-may-reflect-design-limitation]]) or regime-specificity.
- Added boundary conditions narrowing CB dominance to the specific governance comparison regime.
- Confidence remains **high** for the original governance comparison finding (Bonferroni-significant, d=1.64), but the claim's generalizability is now bounded. CB dominance is confirmed in the 7-regime comparison but not replicated in subsequent sweeps.

## Lifecycle audit

**2026-02-19** — automated claim-lifecycle audit:
- (Note: 22 bulk-added tax-rate evidence entries removed 2026-02-20 — they measured transaction_tax_rate effects, not circuit breaker performance)

<!-- topics: governance, circuit-breaker, welfare, mechanism-design -->
