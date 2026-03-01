---
description: Circuit breaker null effect in baseline v2 may reflect insufficient threshold variation in 2-level on/off design
type: claim
status: active
confidence: medium
domain: methodology
evidence:
  supporting:
  - run: 20260213-202050_baseline_governance_v2
    metric: welfare
    detail: "CB on vs off: d=0.008, p=0.92, N=700. But significant tax x CB interactions on 5 metrics suggest CB matters conditionally"
  - run: 20260213-173805_baseline_governance
    metric: all
    detail: "CB null across all 6 metrics: welfare d=-0.10 p=0.66, honest_payoff d=-0.27 p=0.24, toxicity d=0.10 p=0.64. N=80, 10 seeds"
  - run: 20260217_memori_study
    metric: all
    detail: "CB null in LLM memori scenario: largest d=0.55 (quality_gap, p=0.14). 0/12 tests significant. N=30, 5 seeds"
  - run: 20260213-143751_delegation_games_study
    metric: toxicity_rate
    detail: "CB effect on toxicity negligible: d=0.078, p=0.73. CB welfare effect nominal (d=0.557, p=0.015) but not Bonferroni-significant. N=10 seeds, delegation games scenario"
  - run: 20260213-204503_agent_lab_research_safety_study
    metric: welfare
    detail: "CB null across welfare, toxicity, honest payoff in 160-run factorial. Quality gap invariant (always zero). N=10 seeds per config, 4x2x2 design"
  - run: 20260210-220048_kernel_governance
    metric: welfare
    detail: "CB marginal toxicity effect (d=0.55, p=0.017) fails Bonferroni. 0/12 hypotheses significant. 80 runs, 10 seeds per config, kernel governance scenario"
  weakening:
  - run: 20260208-215009_sweep_freeze_duration
    metric: welfare
    detail: "Freeze duration sweep shows CB parameters DO matter when varied: 5 vs 1 epoch freeze gives 17% welfare improvement. Binary on/off misses this"
  - run: 20260301_cb_threshold_sweep
    metric: n_frozen
    detail: "CONFIRMED: CB fires only at thresholds <=0.5 (mean_frozen=1.46-1.63), never at 0.7-0.9 (0/720 runs). Default threshold 0.6 sits above activation boundary. 1440 runs, 10 seeds, 144 configs"
  - run: 20260301_cb_threshold_sweep
    metric: welfare
    detail: "1-way ANOVA F(3,1436)=56.87, eta2=0.106, p<0.0001. CB threshold explains 10.6% of welfare variance when varied (vs ~0% in binary on/off designs)"
  boundary_conditions:
  - "CB tested as binary on/off in 8-agent small-world (v1 N=80, v2 N=700), 8-agent kernel v4 (N=40), 5-agent memori (N=10), 10-agent contract screening"
  - "Always default CB thresholds — no threshold variation tested except freeze_duration sweep"
  - "All 3 council reviewers flagged CB recalibration as top priority"
  - "RESOLVED: 1440-run threshold sweep confirms CB null was design artifact — default 0.6 above activation boundary at 0.5"
sensitivity:
  topology: n/a (methodology note)
  agent_count: n/a
  governance_interaction: the claim IS about interaction design limitations
supersedes: []
superseded_by: []
related_claims:
- claim-tax-dominates-cb-kernel
- claim-circuit-breakers-dominate
- claim-tax-cb-interact-on-quality-gap
- claim-governance-cost-paradox
- claim-tax-and-penalty-effects-are-orthogonal
- claim-optimal-tax-range-0-to-5pct
- claim-freeze-duration-and-violation-threshold-interact-on-welfare
- claim-optimal-cb-threshold-predicted-in-03-05-range
- claim-adaptive-cb-thresholds-should-dominate-static
- claim-cb-threshold-05-maximizes-welfare-in-small-world-topology
- claim-circuit-breaker-activation-has-sharp-threshold-boundary-at-toxicity-05
- claim-aggressive-cb-threshold-harms-honest-agents-through-false-positive-freezing
created: 2026-02-20
updated: 2026-03-01
aliases:
- cb-null-may-reflect-design-limitation
cssclasses:
- claim
- claim-medium
tags:
- methodology
- circuit-breaker
- experimental-design
graph-group: claim
---

# circuit breaker null effect may reflect insufficient threshold variation in the experimental design

## Evidence summary

In both the [[20260213-202050_baseline_governance_v2]] sweep (700 runs, d=0.008, p=0.92) and the [[20260213-173805_baseline_governance]] sweep (80 runs, d=-0.10, p=0.66), circuit breakers show essentially zero main effect on welfare. This is a cornerstone finding supporting [[claim-tax-dominates-cb-kernel]]. However, the experimental design only tests CB as binary on/off with default thresholds, without varying the freeze threshold, freeze duration, or activation sensitivity.

The significant tax x CB interactions on 5 metrics ([[claim-tax-cb-interact-on-quality-gap]]) demonstrate that CB *does* matter conditionally, undermining the interpretation that CB is simply ineffective. The null main effect may mask threshold-dependent effects that a finer-grained sweep would reveal. All three council reviewers flagged "circuit breaker recalibration" as the top experimental priority.

## Implications

If the CB null effect is a design artifact, then [[claim-circuit-breakers-dominate]] (from other runs with different CB configurations) and [[claim-tax-dominates-cb-kernel]] may be measuring different aspects of CB effectiveness rather than contradicting each other. The resolution requires a CB threshold sweep within the baseline governance v2 framework.

If CB is effective when properly calibrated, [[claim-governance-cost-paradox]] may be partially resolvable: the welfare cost of governance stacks could be reduced by replacing high tax rates with optimized CB thresholds. This would also expand the safe operating range identified in [[claim-optimal-tax-range-0-to-5pct]] — if CB can compensate for security at low tax rates, designers gain more policy headroom. A CB threshold sweep would also reveal whether CB operates as a third orthogonal axis alongside tax and penalty ([[claim-tax-and-penalty-effects-are-orthogonal]]), or whether it interacts with both.

## Recommended next experiment

**Primary sweep (refined 2026-03-01):** 4x4x3x3 full factorial = 1,440 runs

| Parameter | Levels | Values | Rationale |
|-----------|--------|--------|-----------|
| `freeze_threshold_toxicity` | 4 | 0.3, 0.5, 0.7, 0.9 | Spans aggressive to lenient; default 0.6 falls between levels 2-3 |
| `freeze_threshold_violations` | 4 | 1, 3, 5, 8 | Tests single-strike through tolerant |
| `freeze_duration_epochs` | 3 | 1, 3, 5 | Validated range from prior sweep |
| `transaction_tax_rate` | 3 | 0.0, 0.05, 0.10 | Tests CB x tax interaction |

10 seeds per configuration. Analysis: 3-way ANOVA (Type II SS) with BH correction. Power: detects d >= 0.5 at 80% power. See `runs/research-cb-threshold-sweep-design-20260301.md` for full design rationale including game-theoretic foundations and ROC tradeoff analysis.

**Directional prediction:** [[claim-optimal-cb-threshold-predicted-in-03-05-range]] predicts the 0.3-0.5 range will maximize welfare, based on synthesis of repeated game punishment calibration theory and existing threshold dancing data.

**Secondary sweep:** threshold dancing resistance across 4 threshold levels x 2 adversary types x 2 audit probabilities = 80 runs. Addresses [[failure-threshold-dancing]] directly.

**Exploratory:** adaptive EWMA thresholds vs best static threshold. See [[claim-adaptive-cb-thresholds-should-dominate-static]].

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: methodology, circuit-breaker, experimental-design -->
