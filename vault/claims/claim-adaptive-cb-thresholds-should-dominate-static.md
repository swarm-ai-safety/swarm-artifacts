---
description: EWMA-based adaptive freeze thresholds should reduce false positives while maintaining adversary detection, dominating any fixed threshold
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260214-094622_redteam
    metric: damage
    detail: "Threshold dancing succeeds at static 0.7 — adaptive threshold tightening when persistent sub-threshold behavior detected would eliminate the dancing operating margin"
  - run: 20260208-215009_sweep_freeze_duration
    metric: welfare
    detail: "CB parameters have real effects when varied — adaptive variation should capture best-case threshold at each point in time"
  weakening: []
  boundary_conditions:
  - Theoretical prediction based on adaptive monitoring literature, not SWARM experiment
  - Assumes the adaptive mechanism can be implemented in SWARM without excessive computational overhead
  - EWMA lambda parameter itself requires calibration
sensitivity:
  topology: untested
  agent_count: untested
  adversarial_fraction: "adaptive advantage should increase with adversarial fraction as static thresholds face tighter tradeoffs"
supersedes: []
superseded_by: []
related_claims:
- claim-optimal-cb-threshold-predicted-in-03-05-range
- claim-cb-null-may-reflect-design-limitation
- claim-audit-threshold-interaction-enables-dancing
- claim-circuit-breakers-dominate
created: 2026-03-01
updated: 2026-03-01
aliases:
- adaptive-cb-thresholds-should-dominate-static
cssclasses:
- claim
- claim-low
tags:
- governance
- circuit-breaker
- adaptive-mechanisms
- threshold-calibration
graph-group: claim
---

# adaptive circuit breaker thresholds using EWMA decay should dominate static thresholds by reducing false positives while maintaining adversary detection

## Theoretical basis

Static freeze thresholds face a fundamental tradeoff: a threshold low enough to catch adversaries (e.g., 0.3) will also freeze honest agents with noisy behavior, while a threshold high enough to avoid false positives (e.g., 0.7) enables threshold dancing. This is the classic ROC operating point problem.

Adaptive thresholds resolve this tradeoff by adjusting per-agent based on behavioral history. The proposed mechanism:

1. **Baseline threshold:** Start at a moderate level (e.g., 0.5)
2. **EWMA update:** theta_i(t) = lambda * toxicity_i(t) + (1-lambda) * theta_i(t-1)
3. **Dancing detection:** If agent i's toxicity stays within epsilon of the freeze threshold for k consecutive epochs, tighten threshold by delta for that agent
4. **Recovery:** If agent cooperates cleanly for m epochs, relax threshold back toward baseline

This mirrors the Adaptive Multi-Dimensional Monitoring (AMDM) algorithm from Shukla 2025 (arXiv:2509.00115), which achieves:
- False positive rate reduction from 4.5% to 0.9% vs static thresholds
- Detection latency reduction from 12.3s to 5.6s
- EWMA smoothing factor lambda=0.25 balances reactivity and stability

## Why adaptive should dominate static

1. **Against standard adversaries:** Adaptive threshold converges to same detection rate as optimally-calibrated static threshold, but with lower false positives because honest agents with stable behavior get relaxed thresholds.

2. **Against threshold dancers:** This is where adaptive strictly dominates. A static threshold at 0.7 allows dancing ([[20260214-094622_redteam]], evasion rate 0.296). An adaptive threshold that detects persistent sub-threshold operation would tighten for the dancing agent specifically, making evasion impossible without also reducing adversarial payoff below the cooperation payoff.

3. **Under regime change:** If adversarial fraction shifts during a run, adaptive thresholds self-adjust. Static thresholds optimized for 25% adversarial may fail at 50%.

## Decisive experiment

Section 6.3 of `runs/research-cb-threshold-sweep-design-20260301.md` proposes: 1 adaptive condition x 3 lambda values (0.1, 0.25, 0.5) x 10 seeds = 30 runs, compared against the best static threshold from the primary sweep.

If the adaptive condition outperforms the best static threshold on welfare while also reducing threshold dancing success, the claim upgrades to `medium` confidence.

## Connections

This claim, if confirmed, has implications beyond circuit breakers. It would establish that **adaptive governance mechanisms are generically superior to static governance** in multi-agent systems with adversarial participants. This parallels the finding in the literature that tolerant grim trigger (with randomized forgiveness probability phi) approaches efficiency as the discount factor approaches 1, while pure grim trigger does not.

The parallel to [[claim-reputation-decay-rate-improves-welfare]] is structural: reputation decay is itself an adaptive mechanism (decaying old information to reflect current behavior). Both adaptive CB thresholds and reputation decay share the principle that governance should weight recent behavior more heavily than historical behavior.

## Open questions

1. What is the optimal EWMA lambda for SWARM specifically?
2. Does adaptive threshold introduce new adversarial strategies (e.g., "threshold probing" to map the adaptation dynamics)?
3. Is the EWMA update rule optimal, or would Bayesian updating outperform?
4. How does adaptive threshold interact with audit probability?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, circuit-breaker, adaptive-mechanisms, threshold-calibration -->
