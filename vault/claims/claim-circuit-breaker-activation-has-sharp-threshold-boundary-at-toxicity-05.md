---
description: CB freezes agents at thresholds 0.3-0.5 but never fires at 0.7-0.9 — a binary activation cliff across 1440 runs
type: claim
status: active
confidence: high
domain: governance
evidence:
  supporting:
  - run: 20260301_cb_threshold_sweep
    metric: n_frozen
    detail: "Threshold 0.3: mean_frozen=1.63, 330/360 runs (92%) freeze agents. Threshold 0.5: mean_frozen=1.46, 315/360 runs (88%). Threshold 0.7: mean_frozen=0.00, 0/360 runs. Threshold 0.9: mean_frozen=0.00, 0/360 runs. N=1440 total, 10 seeds per config, Bonferroni-sig (0 vs nonzero is trivially significant)"
  - run: 20260301_cb_threshold_sweep
    metric: welfare
    detail: "Thresholds 0.7 and 0.9 are functionally CB-off conditions — welfare patterns at 0.7-0.9 match expected CB-off behavior. Replicated across all 36 configs (4 violations x 3 durations x 3 taxes) per threshold"
  weakening: []
  boundary_conditions:
  - "8 agents, small-world topology (k=4, p=0.15), 25% adversarial fraction"
  - "Baseline toxicity rate ~0.26 across all conditions — thresholds 0.7+ never reached by any agent"
  - "Sharp boundary is a consequence of the toxicity distribution, not a universal CB property"
  - "If agent behavior or toxicity scoring changes, the activation boundary would shift"
sensitivity:
  topology: "boundary location may shift with topology (hub topologies may have higher baseline toxicity)"
  agent_count: "untested beyond 8 agents"
  adversarial_fraction: "higher adversarial fractions may push baseline toxicity above 0.5, shifting the boundary"
  agent_sophistication: "LLM agents may have different toxicity distributions, shifting boundary"
supersedes: []
superseded_by: []
related_claims:
- claim: claim-cb-threshold-05-maximizes-welfare-in-small-world-topology
  relation: supports
- claim: claim-cb-null-may-reflect-design-limitation
  relation: supports
- claim: claim-tax-dominates-cb-kernel
  relation: refines
- claim: claim-optimal-cb-threshold-predicted-in-03-05-range
  relation: supports
- claim: claim-aggressive-cb-threshold-harms-honest-agents-through-false-positive-freezing
  relation: supports
created: 2026-03-01
updated: 2026-03-01
aliases:
- cb-activation-sharp-threshold-boundary
cssclasses:
- claim
- claim-high
tags:
- governance
- circuit-breaker
- threshold-calibration
- activation-dynamics
graph-group: claim
---

# circuit breaker activation has a sharp threshold boundary at toxicity 0.5 — above this threshold CB never fires

## Evidence summary

The [[20260301_cb_threshold_sweep]] provides definitive evidence of a binary activation cliff in the circuit breaker mechanism. Across 1,440 runs (10 seeds x 144 configurations), the CB freezes agents at thresholds 0.3 and 0.5 but **never** freezes a single agent at thresholds 0.7 or 0.9:

| Threshold | Runs with freeze | Mean agents frozen | Mean toxicity |
|-----------|------------------|--------------------|---------------|
| 0.3 | 330/360 (92%) | 1.63 | 0.260 |
| 0.5 | 315/360 (88%) | 1.46 | 0.261 |
| 0.7 | 0/360 (0%) | 0.00 | 0.260 |
| 0.9 | 0/360 (0%) | 0.00 | 0.260 |

This is not a gradual decline in activation rate — it is a complete cutoff. The 720 runs at thresholds 0.7 and 0.9 had exactly zero frozen agents. The replication across 36 configurations per threshold (4 violation levels x 3 durations x 3 tax rates) and 10 seeds per configuration makes this finding robust: it is not a sampling artifact.

## Mechanism

The baseline toxicity rate in this scenario is approximately 0.26 across all conditions. Because no agent (honest or adversarial) ever produces toxicity exceeding 0.7 in the small-world 8-agent scenario, thresholds set at 0.7 or above are unreachable. The CB is structurally inert at these settings.

This explains the CB null effect observed in prior studies ([[claim-cb-null-may-reflect-design-limitation]]): if the default CB threshold in those studies was 0.6 or above, the CB may have rarely or never fired, producing a trivial null result. The finding also refines [[claim-tax-dominates-cb-kernel]] — tax dominates CB only when CB is set to a non-activating threshold; when CB is properly calibrated at 0.5, its effect size (eta2 = 0.106) exceeds the tax effect (eta2 = 0.077).

## Implications

This finding has important implications for SWARM experimental design. Any study comparing "CB on" vs "CB off" must verify that the CB actually fires under the "on" condition. If the default threshold exceeds the toxicity distribution ceiling, "CB on" and "CB off" are operationally identical, and the resulting null effect is a tautology rather than a scientific finding.

The sharp boundary also predicts that the optimal threshold must lie below the boundary (since thresholds above it are inert). Combined with [[claim-aggressive-cb-threshold-harms-honest-agents-through-false-positive-freezing]], the safe operating range for CB is a narrow band just below the activation cliff — at 0.5 in this scenario.

## Open questions

1. Where does the activation boundary fall in other scenarios (different topologies, agent counts, adversarial fractions)?
2. Is the boundary determined by the maximum toxicity any agent produces, or by some percentile of the toxicity distribution?
3. How does the boundary shift with agent sophistication (LLM agents may produce different toxicity profiles)?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, circuit-breaker, threshold-calibration, activation-dynamics -->
