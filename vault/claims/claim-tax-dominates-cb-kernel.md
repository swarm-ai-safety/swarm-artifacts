---
description: Transaction tax rate explains 32.4% of welfare variance; circuit breakers
  show no detectable effect in kernel markets
type: claim
status: active
confidence: high
domain: governance
evidence:
  supporting:
  - run: 20260214-113750_kernel_v4_code_sweep
    metric: welfare
    detail: Tax d=1.14-1.59, CB d=-0.02 (p=0.88), N=40, 5 seeds
  - run: 20260213-173805_baseline_governance
    metric: welfare
    detail: 'Tax dominance replicates in baseline governance v1: d=1.13-1.41 across pairwise comparisons, N=80, 10 seeds, Bonferroni-corrected'
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: 'Tax dominance replicates at scale in v2: d=0.51-1.18, welfare and honest_payoff, N=700, 100 seeds, Bonferroni-corrected'
  weakening:
  - run: 20260214-113750_kernel_v4_code_sweep
    metric: welfare
    detail: "CB x tax interaction non-monotonic: CB helps at 5% tax (+2.42) but harms at 0% (-2.02), 10% (-2.15), 15% (-7.65). CB null main effect may mask conditional effectiveness. N=5 seeds"
  boundary_conditions:
  - GPU kernel marketplace, 8 agents, small-world topology
  - Prior n=2 study had false positive on CB effect
  - CB tested as binary on/off with default thresholds — null may reflect insufficient threshold variation
  - Kernel v4 shows CB x tax interaction, suggesting CB matters conditionally even where main effect is null
sensitivity:
  topology: Small-world; circuit breakers may matter more in hub-and-spoke topologies
    where halting a hub cascades
  agent_count: 8 agents; CB effect may emerge at larger scales where systemic risk
    accumulates
  cb_threshold: CB tested only as on/off — threshold sweep needed to determine true CB effectiveness range
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-circuit-breakers-dominate
- claim-tax-phase-transition
- claim-cb-null-may-reflect-design-limitation
- claim-cb-tax-interaction-non-monotonic-in-kernel-v4
- claim-tax-welfare-direction-is-scenario-dependent
created: 2026-02-19
updated: '2026-02-20'
aliases:
- tax-dominates-cb-kernel
- transaction-tax-rate-explains-324-of
cssclasses:
- claim
- claim-high
tags:
- governance
- transaction-tax
- circuit-breaker
- kernel-market
graph-group: claim
---

# Transaction tax rate explains 32.4% of welfare variance while circuit breakers show no detectable effect in kernel markets

In a GPU kernel marketplace simulation, the transaction tax rate explains 32.4% of welfare variance (d = 1.14–1.59), while circuit breakers show no statistically detectable effect (d = -0.02, p = 0.88).

**Evidence summary.** The kernel market v4 study (N=40 runs across 5 seeds, 8 agents) performed a factorial analysis of tax rate and circuit breaker activation. Tax rate was the dominant governance lever, with large effect sizes across all seeds. Circuit breakers produced a near-zero effect size with p = 0.88, indicating no meaningful contribution to welfare outcomes. Notably, a prior n=2 pilot study had produced a false positive for circuit breaker effectiveness, underscoring the importance of adequate replication.

**Boundary conditions.** This result is specific to the GPU kernel marketplace with small-world topology and 8 agents. Circuit breakers are designed to halt cascading failures; in this setting, the interaction structure may not generate the kind of systemic shocks that circuit breakers are intended to arrest. The result should not be generalized to topologies with high-degree hubs or settings with correlated agent failures.

**Open questions.**
- Do circuit breakers become effective in hub-and-spoke topologies where halting a hub has cascading effects?
- Is the null CB result driven by the small agent count, or is it a fundamental feature of kernel markets?
- What is the interaction between tax rate and circuit breaker threshold?
- Would a CB threshold sweep (freeze threshold x freeze duration) reveal hidden CB effectiveness? See [[claim-cb-null-may-reflect-design-limitation]].
- The non-monotonic CB x tax interaction in kernel v4 ([[claim-cb-tax-interaction-non-monotonic-in-kernel-v4]]) — does it replicate with adequate power?

## Update history

**2026-02-20** — backward-pass update:
- Added weakening evidence from [[20260214-113750_kernel_v4_code_sweep]]: CB x tax interaction is non-monotonic in kernel v4, suggesting CB has conditional effects even where the main effect is null. This weakens the interpretation that CB is simply irrelevant.
- Added boundary condition noting binary on/off CB design limitation per [[claim-cb-null-may-reflect-design-limitation]].
- Added related claims: claim-cb-null-may-reflect-design-limitation, claim-cb-tax-interaction-non-monotonic-in-kernel-v4, claim-tax-welfare-direction-is-scenario-dependent.
- Confidence remains **high** for the main effect finding (tax dominates CB main effect in kernel markets). However, the claim's interpretation is now qualified: CB null may be a design artifact rather than a fundamental property. A CB threshold sweep is the decisive next experiment.

## Lifecycle audit

**2026-02-19** — automated claim-lifecycle audit:
- (Note: 22 bulk-added tax-rate evidence entries consolidated 2026-02-20 into 2 representative entries per source run)

<!-- topics: governance, transaction-tax, circuit-breaker, kernel-market -->
