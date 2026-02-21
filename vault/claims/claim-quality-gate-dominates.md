---
description: Deterministic quality gate (reject p<0.5) achieves comparable safety
  to full governance while preserving welfare
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260211-232952_gastown_composition_study
    metric: welfare, toxicity
    detail: "Refinery regime preserves near-ungoverned welfare with comparable toxicity reduction. N=63 (9 configs x 7 agents). No formal effect sizes computed — descriptive comparison only. 3 seeds per config"
  weakening: []
  boundary_conditions:
  - GasTown workspace, 7 agents, 30 epochs
  - Zero friction on accepted interactions
  - Gate may be unnecessary in all-honest LLM populations where there is nothing to filter
sensitivity:
  topology: Tested on GasTown small-world; gate effectiveness may vary on denser topologies
    where agents have more interaction partners
  agent_count: 7 agents; gate false-rejection rate may matter more at scale
  agent_type: Tested with algorithmic agents; LLM agents may behave differently near p=0.5 threshold
supersedes: []
superseded_by: []
related_claims:
- claim-governance-cost-paradox
- claim-circuit-breakers-dominate
- claim-memory-promotion-gate
- claim-collusion-detection-is-binding-constraint-on-robustness
- claim-cb-audit-sufficient-for-solo-exploits
- claim-cascade-mechanisms-ineffective-against-governance-gaming
- claim-memori-agents-show-no-governance-sensitivity
- claim-cb-null-may-reflect-design-limitation
created: 2026-02-19
updated: 2026-02-21
aliases:
- quality-gate-dominates
- deterministic-quality-gate-reject-p05-achieves
cssclasses:
- claim
- claim-low
tags:
- governance
- quality-gate
- welfare
- refinery
graph-group: claim
---

# Deterministic quality gate achieves comparable safety to full governance while preserving welfare

A simple deterministic quality gate — rejecting all interactions with p < 0.5 — achieves toxicity reduction comparable to the full governance stack while preserving near-ungoverned welfare levels.

**Evidence summary.** In the GasTown governance cost study (N=63 runs, 7 agents, 30 epochs), the "Refinery" regime (quality gate only, no tax, no circuit breakers, no collusion penalties) preserved welfare at levels close to the ungoverned baseline. Toxicity reduction was comparable to the fully governed regime, indicating that the additional governance mechanisms contribute marginal safety benefit at disproportionate welfare cost.

**Boundary conditions.** The result assumes zero friction on accepted interactions — that is, once an interaction passes the p >= 0.5 gate, it incurs no additional governance overhead. This may not hold in settings where post-acceptance monitoring or reporting is required. The test used only 7 agents; at larger scales, the binary threshold may introduce cliff effects near p = 0.5 that a softer mechanism could smooth.

**Open questions.**
- Is the p = 0.5 threshold optimal, or would a calibrated threshold improve the welfare-safety frontier?
- Does the quality gate remain effective under adversarial manipulation of the proxy score?
- How does gate performance interact with proxy miscalibration?
- Is the gate necessary at all in LLM-only populations where agents show zero governance sensitivity ([[claim-memori-agents-show-no-governance-sensitivity]])?

## Update history

**2026-02-20** — backward-pass update:
- Added boundary condition: gate may be unnecessary in all-honest LLM populations (per [[claim-memori-agents-show-no-governance-sensitivity]], no adversarial behavior to filter).
- Added sensitivity note for agent type (algorithmic vs LLM).
- Added related claims: claim-memori-agents-show-no-governance-sensitivity, claim-cb-null-may-reflect-design-limitation.
- Confidence remains **high** within the established GasTown boundary. No direct weakening evidence against the quality gate mechanism itself.

**2026-02-21** — Gate 2 statistical rigor fix:
- Downgraded **medium → low**: no formal effect sizes (Cohen's d), p-values, or correction methods computed. Run data contains only descriptive aggregated means with 3 seeds per config.
- Upgrade requires: formal pairwise tests between refinery and full-governance regimes with ≥10 seeds per config, Bonferroni-corrected across regime comparisons.

## Lifecycle audit

**2026-02-19** — automated claim-lifecycle audit:
- Upgraded confidence: medium -> high
- (Note: 22 bulk-added tax-rate evidence entries removed 2026-02-20 — they measured transaction_tax_rate effects, not quality gate performance)

<!-- topics: governance, quality-gate, welfare, refinery -->
