---
description: Evolved governance parameters consistently maximize audit+penalty severity but diverge on freeze thresholds and tax rates
type: claim
status: active
confidence: low
domain: calibration
evidence:
  supporting:
  - run: 20260228_093125_evolve_baseline
    metric: best_params
    detail: "50-iter run: audit_prob=0.9, penalty_mult=9.5, slash_rate=0.8, freeze_tox=0.06, tax=0.18. Most aggressive parameter set. Score 0.693"
  - run: 20260227_222203_evolve_baseline
    metric: best_params
    detail: "5-iter run: audit_prob=0.6, penalty_mult=6.0, slash_rate=0.4, tax=0.15. Moderate parameters. Score 0.693"
  - run: 20260227_222439_evolve_baseline
    metric: best_params
    detail: "20-iter run: audit_prob=0.6, penalty_mult=4.0, slash_rate=0.5, tax=0.1, freeze_tox=0.25. Least aggressive enforcement. Score 0.693"
  weakening:
  - run: 20260227_222439_evolve_baseline
    metric: best_params
    detail: "20-iter run finds lowest penalty multiplier (4.0) and most lenient freeze threshold (0.25) yet achieves identical fitness score — aggressive enforcement may not be necessary"
  boundary_conditions:
  - "All runs use same fitness weights: toxicity=0.35, welfare=0.30, quality_gap=0.20, payoff_gap=0.15"
  - "Single seed base (42) — parameter sensitivity to random seed unknown"
  - "Baseline scenario only — other scenarios may favor different governance styles"
  - "Toxicity and welfare metrics averaged across all agents — may mask distributional effects"
  - "quality_gap = 0.0 in all runs — this fitness component is uninformative"
sensitivity:
  topology: untested
  agent_count: untested
  fitness_weights: "Current weights heavily favor toxicity (0.35). Different weights would shift optimal governance parameters"
supersedes: []
superseded_by: []
related_claims:
- claim-llm-guided-evolution-converges-to-aggressive-governance-within-5-iterations
- claim-tax-welfare-tradeoff
- claim-circuit-breakers-dominate
- claim-freeze-duration-and-violation-threshold-interact-on-welfare
- claim-audit-threshold-interaction-enables-dancing
- claim-optimal-tax-range-0-to-5pct
created: 2026-02-28
updated: 2026-02-28
aliases:
- evo-governance-aggressive-optima
cssclasses:
- claim
- claim-low
tags:
- evolutionary-optimization
- governance-calibration
- audit
- penalty
- parameter-sensitivity
graph-group: claim
---

# evolutionary governance optimization finds multiple equally-fit parameter regimes from lenient to aggressive

## Evidence summary

Three LLM-guided evolutionary optimization runs on the baseline scenario converge to **nearly identical fitness scores (0.693)** but with **markedly different governance parameter sets**. This reveals a flat fitness ridge where multiple governance philosophies achieve equivalent performance:

**Aggressive regime (50-iter run):** audit probability 0.9, penalty multiplier 9.5x, stake slash 80%, freeze at 0.06 toxicity, tax 18%. This is a surveillance-heavy governance model with severe punishments and tight trigger thresholds.

**Moderate regime (5-iter run):** audit probability 0.6, penalty multiplier 6.0x, stake slash 40%, freeze at 0.1 toxicity, tax 15%. Moderate enforcement with balanced penalties.

**Lenient regime (20-iter run):** audit probability 0.6, penalty multiplier 4.0x, stake slash 50%, freeze at 0.25 toxicity, tax 10%. Lower enforcement intensity, more permissive thresholds.

All three achieve avg_toxicity ~0.306 and zero frozen agents, suggesting the toxicity floor is set by agent behavior rather than governance intensity. The welfare difference (25-30) correlates weakly with iteration count but may reflect evaluation noise rather than governance regime effects.

## Connection to prior claims

This finding has important implications for several existing claims:

The [[claim-tax-welfare-tradeoff]] established that tax above 5% significantly reduces welfare (d=1.18). Yet the evolutionary optimizer converges to tax rates of 10-18% in all three runs, suggesting the welfare cost of moderate taxation is offset by other fitness components (toxicity reduction, payoff gap) in the composite score. The tax-welfare tradeoff may be real for welfare in isolation but not decisive for overall governance fitness.

The [[claim-freeze-duration-and-violation-threshold-interact-on-welfare]] found that longer freeze durations (5 epochs) and tighter violation thresholds (3) improve welfare. The 50-iteration evolutionary run independently converges to a similar regime: freeze_duration=9, violations=2 — even more aggressive than the sweep's best config. This provides convergent evidence from a different methodology (evolutionary search vs factorial sweep).

The [[claim-circuit-breakers-dominate]] finding is nuanced by this evidence: CB parameters appear in all three optimal configurations, but the wide range of effective freeze thresholds (0.06 to 0.25) suggests CB effectiveness is not parameter-sensitive within the range explored by evolution.

## Mechanism

The flat fitness ridge likely arises because the composite fitness function (weighted sum of toxicity, welfare, quality gap, payoff gap) creates compensatory dynamics: aggressive governance reduces toxicity but costs welfare via higher taxes, while lenient governance preserves welfare but allows more toxicity. The fitness weights (tox=0.35, welfare=0.30) are close enough that these effects approximately cancel out. The quality_gap component is uniformly 0.0, providing no gradient for optimization.

## Open questions

- Would Pareto frontier analysis (rather than scalar fitness) reveal meaningful tradeoffs between governance regimes?
- Does the flat ridge persist with different agent populations or scenarios?
- Is the zero quality_gap a design limitation or a genuine finding about the baseline scenario?
- How do the different governance regimes perform under adversarial conditions (red-team scenarios)?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: evolutionary-optimization, governance-calibration, audit, penalty, parameter-sensitivity, fitness-landscape -->
