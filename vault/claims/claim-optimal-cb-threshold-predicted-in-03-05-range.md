---
description: Game-theoretic punishment calibration and ROC tradeoff analysis predict 0.3-0.5 as the welfare-maximizing freeze threshold range
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260211-000149_kernel_market_governance_comparison
    metric: welfare
    detail: "CB-only achieves d=1.64 welfare advantage under unknown threshold configuration — consistent with threshold in effective range"
  - run: 20260214-094622_redteam
    metric: damage
    detail: "Threshold dancing succeeds at 0.7 but fails at 0.35-0.5 — consistent with 0.3-0.5 as critical range"
  - run: 20260208-215009_sweep_freeze_duration
    metric: welfare
    detail: "Duration sweep shows CB parameters matter when varied — violation threshold 3 outperforms 8, consistent with tighter thresholds improving welfare"
  weakening:
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: "CB null at d=0.008, N=700 under default 0.6 threshold — but 0.6 is above the predicted optimal range"
  boundary_conditions:
  - Prediction based on theoretical synthesis, not direct SWARM sweep
  - Assumes 8-agent small-world topology with 25% adversarial fraction
  - ROC tradeoff assumes toxicity scores are well-calibrated continuous measures
  - Untested whether the optimal range shifts with adversarial fraction or topology
sensitivity:
  topology: untested
  agent_count: untested
  adversarial_fraction: "predicted range may narrow at higher adversarial fractions"
  agent_sophistication: untested with LLM agents
supersedes: []
superseded_by: []
related_claims:
- claim-cb-null-may-reflect-design-limitation
- claim-circuit-breakers-dominate
- claim-tax-dominates-cb-kernel
- claim-audit-threshold-interaction-enables-dancing
- claim-freeze-duration-and-violation-threshold-interact-on-welfare
- claim-adaptive-cb-thresholds-should-dominate-static
created: 2026-03-01
updated: 2026-03-01
aliases:
- optimal-cb-threshold-predicted-in-03-05-range
cssclasses:
- claim
- claim-low
tags:
- governance
- circuit-breaker
- parameter-sensitivity
- threshold-calibration
graph-group: claim
---

# optimal CB freeze threshold is predicted to lie in the 0.3-0.5 range based on ROC tradeoff analysis and game-theoretic punishment calibration

## Theoretical basis

The prediction synthesizes three independent lines of evidence:

1. **Repeated game theory** (MIT OCW 17.810, Lecture 5): intermediate punishment strategies with finite duration k outperform both grim trigger (permanent exclusion) and tit-for-tat (single-period response) when there is noise. The SWARM circuit breaker maps directly onto this framework — `freeze_threshold_toxicity` determines the trigger sensitivity, and `freeze_duration_epochs` determines punishment severity. Optimal trigger sensitivity balances false positives (freezing honest agents) against false negatives (missing adversaries).

2. **AI safety circuit breaker literature** (Zou et al. 2024, arXiv:2406.04313): Representation Rerouting uses cosine similarity thresholds to trigger circuit breaking in LLMs. Threshold optimization follows a standard ROC curve — too low causes over-refusal (analogous to false positive freezing in SWARM), too high allows harmful outputs (analogous to threshold dancing). The literature reports that moderate thresholds (e.g., cosine similarity ~0.5) optimize the Pareto frontier.

3. **Existing SWARM data**: threshold dancing succeeds at freeze_threshold=0.7 but fails at 0.35-0.5 ([[20260214-094622_redteam]]). The default 0.6 threshold falls on the boundary of effectiveness. Violation threshold 3 outperforms 8 in the freeze duration sweep ([[20260208-215009_sweep_freeze_duration]]), consistent with tighter thresholds improving welfare.

## Predicted mechanism

At freeze_threshold_toxicity=0.3-0.5:
- Adversarial agents are frozen before accumulating significant ecosystem damage
- The operating margin for threshold dancing is too narrow for evasion (toxicity must stay below 0.3-0.5, severely limiting adversarial payoff)
- False positive rate remains manageable because honest agents with well-calibrated behavior stay below 0.3
- The welfare improvement over default 0.6 should be detectable as a medium-to-large effect (d >= 0.5)

At freeze_threshold_toxicity < 0.3:
- False positive rate spikes — honest agents with noisy behavior patterns get frozen
- Net welfare decreases despite catching more adversaries
- This represents the "too harsh" regime from game theory

## Decisive experiment

The 4x4x3x3 factorial sweep proposed in `runs/research-cb-threshold-sweep-design-20260301.md` Section 6.1 (1,440 runs) will directly test this prediction. The sweep includes threshold values bracketing the predicted range (0.3, 0.5 vs 0.7, 0.9) with sufficient power to detect d >= 0.5 at 10 seeds per cell.

## Open questions

1. Does the optimal range shift with adversarial fraction (>25%)?
2. Is the optimal threshold topology-dependent (small-world vs scale-free vs random)?
3. Does the prediction hold for LLM-powered agents with more sophisticated evasion strategies?
4. Is 0.3-0.5 a universal range or specific to the SWARM toxicity scoring system?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, circuit-breaker, parameter-sensitivity, threshold-calibration -->
