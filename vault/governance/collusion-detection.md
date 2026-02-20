---
description: Detects coordinated agent behavior via pairwise similarity scores and penalizes flagged pairs, devastating to
  colluders when calibrated
type: governance
status: active
mechanism: collusion-detection
parameters:
- name: collusion_detection_enabled
  type: bool
  default: true
  range: toggle
- name: collusion_frequency_threshold
  type: float
  default: 2.0
  range: 1.0–5.0, interaction frequency z-score to flag
- name: collusion_correlation_threshold
  type: float
  default: 0.6
  range: 0.0–1.0, behavioral correlation above which pair is flagged
- name: collusion_score_threshold
  type: float
  default: 0.4
  range: 0.0–1.0, composite score threshold for penalty trigger
- name: collusion_min_interactions
  type: int
  default: 3
  range: 1–10, minimum interactions before pair can be evaluated
- name: collusion_penalty_multiplier
  type: float
  default: 2.0
  range: 0.5–5.0, penalty scaling for confirmed collusion
- name: collusion_realtime_penalty
  type: bool
  default: true
  range: toggle; applies penalties during epoch rather than at end
- name: collusion_realtime_rate
  type: float
  default: 0.15
  range: 0.0–1.0, fraction of interactions checked in real-time
created: 2026-02-19
updated: 2026-02-19
aliases:
- collusion-detection
- behavioral-similarity-detection
- pairwise-collusion-monitor
cssclasses:
- governance
graph-group: governance
tags:
- governance
- collusion
- detection
- behavioral-similarity
- wealth
- penalty
---

# behavioral similarity detection destroys collusive wealth but destabilizes the ecosystem when penalty multipliers exceed 1.5x

## How it works

The collusion detector monitors pairwise agent interactions across two dimensions: *frequency* (how often two agents interact relative to baseline) and *behavioral correlation* (how similar their action sequences are). When a pair exceeds `collusion_frequency_threshold` standard deviations above mean interaction frequency *and* their behavioral correlation exceeds `collusion_correlation_threshold`, they receive a composite collusion score. If this score exceeds `collusion_score_threshold` and the pair has at least `collusion_min_interactions`, penalties are applied.

Penalties can be applied at epoch end or in real-time (`collusion_realtime_penalty`). Real-time detection samples `collusion_realtime_rate` of interactions per step, enabling faster response but higher computational cost.

The similarity threshold of 0.70 used in the AI Economist GTB experiments is the key calibration point: it balances detection sensitivity against false positives on legitimately correlated honest behavior.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `collusion_detection_enabled` | bool | true | toggles detection |
| `collusion_frequency_threshold` | float | 2.0 | z-score for interaction frequency |
| `collusion_correlation_threshold` | float | 0.6 | behavioral similarity threshold |
| `collusion_score_threshold` | float | 0.4 | composite score to trigger penalty |
| `collusion_min_interactions` | int | 3 | minimum interactions before evaluation |
| `collusion_penalty_multiplier` | float | 2.0 | penalty scaling factor |
| `collusion_realtime_penalty` | bool | true | applies penalties within epoch |
| `collusion_realtime_rate` | float | 0.15 | real-time sampling rate |

## Evidence

The AI Economist GTB study ([[20260213-221500_collusion_tax_effect]]) demonstrated that collusion detection with a similarity threshold of 0.70 creates overwhelming economic disincentives: collusive agents accumulated 137x less wealth than honest agents (3.4 +/- 1.2 vs. 467.3 +/- 186.9, d=3.51, p<0.001, Bonferroni-corrected, N=10 seeds).

- [[claim-collusion-wealth-destruction]] — the primary finding on wealth destruction (high confidence, d=3.51)
- [[20260213-221500_collusion_tax_effect]] — the definitive experiment (10 seeds, 14 agents, 15x15 gridworld)

However, the penalty multiplier must be carefully calibrated. Sweeping collusion_penalty_multiplier from 0.5x to 2.0x across 160 runs showed that multipliers above 1.5x *increase* toxicity (d=-1.12, p<0.0001) with no compensating welfare benefit, because agents shift to individually toxic but non-collusive strategies.

- [[claim-collusion-penalty-destabilizes]] — penalty above 1.5x destabilizes (medium confidence)
- [[20260213-123944_moltbook_captcha_study]] — also swept collusion_penalty_multiplier

The recursive collusion experiments ([[20260210-211721_rlm_recursive_collusion_seed42]], [[20260210-211753_rlm_recursive_collusion_seed7]], [[20260210-211800_rlm_recursive_collusion_seed256]], [[20260210-211803_rlm_recursive_collusion_seed999]]) tested multi-seed collusion dynamics, and the collusion governance run ([[20260210-213833_collusion_governance]]) evaluated detection within a governance stack.

The agent lab research safety study ([[20260213-204503_agent_lab_research_safety_study]]) included `collusion_detection_enabled` as a swept factor, contributing additional evidence on collusion detection in multi-factor governance designs.

Full governance stacks incorporating collusion detection ([[20260213-173805_baseline_governance]], [[20260213-202050_baseline_governance_v2]]) are part of the evidence base for [[claim-governance-cost-paradox]].

## Interactions

- **With transaction tax**: the GTB study used tax as the penalty delivery mechanism for detected collusion. Tax and collusion detection are synergistic when penalty multipliers are below 1.5x.
- **With circuit breaker**: collusion detection flags *pairs*, while circuit breakers freeze *individuals*. A collusive pair can be detected before either member exceeds the toxicity threshold, making the two mechanisms complementary in principle.
- **With audits**: audits detect individual misbehavior; collusion detection targets coordinated behavior. They operate on orthogonal signals (individual vs. pairwise).
- **With reputation decay**: reputation decay penalizes sustained bad behavior; collusion detection penalizes coordinated behavior. An agent can have high individual reputation but still be flagged for collusion.

## Known failure modes

- **Penalty overshoot**: multipliers above 1.5x induce strategy substitution — agents avoid collusion but adopt individually toxic behaviors ([[claim-collusion-penalty-destabilizes]]).
- **Similarity threshold sensitivity**: the 0.70 threshold in GTB experiments may not transfer to other domains. Lower thresholds increase false positives on legitimately correlated honest behavior; higher thresholds allow sophisticated collusion to evade detection.
- **Behavioral diversification**: collusive agents may learn to diversify their action sequences to stay below the correlation threshold while maintaining coordination through less detectable channels.
- **Spatial dependence**: the 15x15 gridworld's spatial constraints may make collusion more detectable than in abstract interaction graphs where spatial structure doesn't constrain behavior.

## Open questions

1. What is the optimal penalty multiplier in the 1.0–1.5x range?
2. Can collusive agents learn to diversify behavior below the 0.70 similarity threshold?
3. Does the 137x wealth destruction ratio hold under learned (rather than heuristic) tax policies?
4. How does detection difficulty scale with the number of colluding agents?
5. Does the correlation threshold need per-domain calibration, or is 0.70 robust across scenarios?

---

Topics:
- [[_index]]

<!-- topics: governance, collusion, detection, behavioral-similarity, wealth, penalty -->