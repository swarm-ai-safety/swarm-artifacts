---
description: Transaction tax rate explains 32.4% of welfare variance; circuit breakers show no detectable effect in kernel
  markets
type: claim
status: active
confidence: high
domain: governance
evidence:
  supporting:
  - run: 20260214-113750_kernel_v4_code_sweep
    metric: welfare
    detail: Tax d=1.14-1.59, CB d=-0.02 (p=0.88), N=40, 5 seeds
  weakening: []
  boundary_conditions:
  - GPU kernel marketplace, 8 agents, small-world topology
  - Prior n=2 study had false positive on CB effect
sensitivity:
  topology: Small-world; circuit breakers may matter more in hub-and-spoke topologies where halting a hub cascades
  agent_count: 8 agents; CB effect may emerge at larger scales where systemic risk accumulates
supersedes: []
superseded_by: []
related_claims:
- claim-tax-welfare-tradeoff
- claim-circuit-breakers-dominate
- claim-tax-phase-transition
created: 2026-02-19
updated: 2026-02-19
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

## Tax Dominates Circuit Breakers in Kernel Markets

In a GPU kernel marketplace simulation, the transaction tax rate explains 32.4% of welfare variance (d = 1.14–1.59), while circuit breakers show no statistically detectable effect (d = -0.02, p = 0.88).

**Evidence summary.** The kernel market v4 study (N=40 runs across 5 seeds, 8 agents) performed a factorial analysis of tax rate and circuit breaker activation. Tax rate was the dominant governance lever, with large effect sizes across all seeds. Circuit breakers produced a near-zero effect size with p = 0.88, indicating no meaningful contribution to welfare outcomes. Notably, a prior n=2 pilot study had produced a false positive for circuit breaker effectiveness, underscoring the importance of adequate replication.

**Boundary conditions.** This result is specific to the GPU kernel marketplace with small-world topology and 8 agents. Circuit breakers are designed to halt cascading failures; in this setting, the interaction structure may not generate the kind of systemic shocks that circuit breakers are intended to arrest. The result should not be generalized to topologies with high-degree hubs or settings with correlated agent failures.

**Open questions.**
- Do circuit breakers become effective in hub-and-spoke topologies where halting a hub has cascading effects?
- Is the null CB result driven by the small agent count, or is it a fundamental feature of kernel markets?
- What is the interaction between tax rate and circuit breaker threshold?

<!-- topics: governance, transaction-tax, circuit-breaker, kernel-market -->
