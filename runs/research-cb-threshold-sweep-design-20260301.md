---
description: Research synthesis on circuit breaker threshold calibration, freeze parameter optimization, and sweep design for multi-agent governance
source_type: research
research_prompt: "circuit breaker threshold sweep design for multi-agent governance — freeze threshold calibration, violation threshold tuning, optimal circuit breaker parameters in agent-based simulations"
generated: 2026-03-01
---

# Circuit breaker threshold sweep design for multi-agent governance — research findings

## 1. The SWARM calibration gap

The SWARM vault contains a well-documented tension: circuit breakers show d=1.64 dominance in the original governance comparison (70 runs, Bonferroni-significant) but null effects (d=0.008, p=0.92) across 700 runs in baseline governance v2 and multiple subsequent studies. The existing claim [[claim-cb-null-may-reflect-design-limitation]] attributes this to insufficient threshold variation — all subsequent studies used binary on/off with default parameters (freeze_threshold_toxicity=0.6, freeze_threshold_violations=3, freeze_duration_epochs=3).

The only threshold sweep to date ([[20260208-215009_sweep_freeze_duration]]) tested 4 freeze durations x 3 violation thresholds x 3 seeds = 36 runs. It found 17% welfare improvement from duration 5 vs 1, additive main effects (no interaction, F=0.23, p=0.96), and never varied the toxicity threshold. This leaves the most critical parameter — `freeze_threshold_toxicity` — entirely unexplored.

## 2. Game-theoretic foundations for punishment calibration

The circuit breaker mechanism maps directly onto **intermediate punishment strategies** from repeated game theory. In the infinitely repeated prisoner's dilemma, punishment duration k and trigger threshold jointly determine whether cooperation can be sustained as a subgame-perfect equilibrium.

**Key theoretical results (MIT OCW, Lecture 5: Repeated Games):**

- **Grim trigger** (permanent exclusion) minimizes the patience threshold delta >= (T-R)/(T-P), but is fragile to noise and errors.
- **Finite punishment of k periods** requires higher delta but is robust to mistakes: after k periods of defection, cooperation resumes.
- **Optimal punishment duration** balances severity (lower delta threshold) against forgiveness (error recovery). The SWARM circuit breaker's `freeze_duration_epochs` IS this k parameter.
- **Tolerant grim trigger** randomizes: post-bad-signal, cooperate with probability phi, punish permanently with probability 1-phi. As delta approaches 1, this approaches efficiency. This suggests an adaptive CB threshold variant.

**Implications for SWARM sweep design:** The freeze duration and violation threshold are not independent design choices — they jointly determine whether the CB mechanism can sustain cooperation at a given adversarial fraction. The sweep should include conditions that test both the "too lenient" regime (where threshold dancing succeeds) and the "too harsh" regime (where honest agents get caught in false positives).

## 3. Circuit breakers in AI safety (Representation Rerouting)

A parallel literature uses "circuit breakers" for LLM safety via Representation Rerouting (RR). While mechanistically different from SWARM's agent-level freezing, the threshold calibration challenges are structurally identical:

**Gray Swan AI / Andy Zou et al. 2024 (arXiv:2406.04313):**
- RR reduces attack success rates by ~90% on Llama-3-8B with <1% capability loss.
- Threshold optimization tunes the harm-score cutoff: too low causes over-refusal (false positives), too high allows leaks (false negatives).
- Validation uses diverse harm datasets filtered by BLEU <0.3 to avoid contamination.
- The Cygnet model achieves ~100x harmful output reduction while exceeding base capabilities — demonstrating the Pareto frontier is movable.

**Relevance to SWARM:** Both systems face the same ROC tradeoff. The `freeze_threshold_toxicity` parameter controls the operating point on a receiver operating characteristic curve: lower threshold = more true positives (catching adversaries) but more false positives (freezing honest agents). The sweep should characterize this curve.

## 4. Adaptive monitoring and threshold calibration

**Shukla 2025 (arXiv:2509.00115) — Adaptive Multi-Dimensional Monitoring (AMDM):**
- Uses EWMA thresholds: theta(t) = lambda * S(t) + (1-lambda) * theta(t-1), where lambda=0.25 balances reactivity and stability.
- Joint anomaly detection via Mahalanobis distance with chi-square threshold.
- Reduces false positive rates from 4.5% to 0.9% vs static thresholds; cuts detection latency from 12.3s to 5.6s.

**Implications for SWARM:** Static freeze thresholds are suboptimal by design. An adaptive threshold that tightens when sustained sub-threshold behavior is detected (addressing threshold dancing) and loosens during low-adversarial periods could dominate the static threshold parameter space. The sweep should include at least one adaptive-threshold condition as a comparator.

## 5. Parameter sweep design methodology

**Grimm et al. (JASSS 17/3/11) — Facilitating Parameter Estimation for ABMs:**
- For stochastic ABMs, run 10+ Monte Carlo repetitions per parameter set; compute CV to assess stability.
- Full factorial design is feasible for small parameter counts (2-4 factors at 3-5 levels).
- Latin Hypercube Sampling (LHS) preferred for >4 dimensions.
- Calibration strategy: start coarse, then refine around transitions/phase boundaries.

**TU Delft experimental design guidelines:**
- Never trust a single run — iteration order randomization creates variability.
- Start with 100 LHS points x 100 repetitions for initial exploration.
- When hunting for transitions, start coarse then zoom in.

## 6. Recommended sweep design for SWARM CB threshold calibration

Based on the research synthesis and the vault's existing gap analysis, the following sweep design addresses the highest-priority open questions.

### 6.1 Primary sweep: CB threshold factorial

**Design:** 4 x 4 x 3 x 3 full factorial = 144 configurations x 10 seeds = 1,440 runs

| Parameter | Levels | Values | Rationale |
|-----------|--------|--------|-----------|
| `freeze_threshold_toxicity` | 4 | 0.3, 0.5, 0.7, 0.9 | Spans aggressive (0.3) to lenient (0.9); 0.6 default falls between levels 2-3 |
| `freeze_threshold_violations` | 4 | 1, 3, 5, 8 | Tests single-strike (1) through tolerant (8); includes prior sweep range |
| `freeze_duration_epochs` | 3 | 1, 3, 5 | Validated range from prior sweep; tests tit-for-tat (1) through intermediate (5) |
| `transaction_tax_rate` | 3 | 0.0, 0.05, 0.10 | Fixed tax levels to test CB x tax interaction per [[claim-cb-null-may-reflect-design-limitation]] |

**Metrics:** welfare_per_epoch, toxicity_rate, honest_payoff, adversarial_payoff, quality_gap, freeze_count, false_positive_freeze_rate

**Analysis plan:**
1. 3-way ANOVA (Type II SS) for freeze_threshold x violations x duration on welfare, with tax as blocking factor
2. Characterize the ROC curve: plot true_positive_freeze_rate vs false_positive_freeze_rate across threshold levels
3. Identify phase transitions: where does welfare cliff or toxicity cliff occur?
4. Test for CB x tax interaction to resolve [[claim-tax-cb-interact-on-quality-gap]]

### 6.2 Secondary sweep: threshold dancing resistance

**Design:** Subset of primary sweep configurations x 2 adversary types x 5 seeds = ~80 runs

| Parameter | Levels | Values |
|-----------|--------|--------|
| `freeze_threshold_toxicity` | 4 | 0.3, 0.5, 0.7, 0.9 |
| `adversary_type` | 2 | standard, threshold_dancer |
| `audit_probability` | 2 | 0.1, 0.25 |

Fix freeze_duration=3, violations=3, tax=0.05.

**Purpose:** Directly test [[failure-threshold-dancing]] resilience across the threshold parameter space. Identifies the critical threshold below which dancing fails.

### 6.3 Exploratory condition: adaptive threshold

**Design:** 1 adaptive-threshold condition x 3 decay rates x 10 seeds = 30 runs

Adaptive threshold rule: if agent's toxicity is within 0.1 of freeze_threshold for 3 consecutive epochs, tighten threshold by 0.05 for that agent. EWMA-inspired decay with lambda in {0.1, 0.25, 0.5}.

**Purpose:** Tests whether adaptive thresholds dominate static thresholds. If confirmed, this reframes the entire CB calibration question from "what is the optimal static threshold" to "what is the optimal adaptation rate."

## 7. Statistical considerations

- **Power:** With 10 seeds per configuration, the sweep can detect medium effects (d >= 0.5) at alpha=0.05 with ~80% power. For the primary welfare outcome, the prior freeze duration sweep showed d=0.7 for duration 5 vs 1, so 10 seeds should be sufficient.
- **Multiple comparisons:** With 144 configurations and 7 metrics, apply BH correction (less conservative than Bonferroni for large sweeps).
- **Interaction detection:** The 3-way factorial requires N >= 5 per cell to detect interactions; 10 seeds provides adequate power for 2-way interactions but may miss 3-way interactions.
- **Phase transition detection:** Plot welfare as heatmap over freeze_threshold x violations, faceted by duration. Visual inspection for cliffs/transitions, confirmed by piecewise regression.

## 8. Expected outcomes and claim updates

If the sweep confirms that CB effectiveness depends on threshold calibration:
- [[claim-cb-null-may-reflect-design-limitation]] upgrades from `medium` to `high` confidence
- [[claim-circuit-breakers-dominate]] gets boundary condition: "CB dominance requires threshold calibration within the 0.3-0.5 range"
- [[claim-tax-dominates-cb-kernel]] gets boundary condition: "tax dominance over CB reflects default-threshold CB, not optimized CB"
- New claim: "optimal CB freeze threshold is 0.3-0.5 for 25% adversarial fraction under small-world topology"

If the sweep shows CB is genuinely null even with threshold variation:
- [[claim-cb-null-may-reflect-design-limitation]] retracted
- [[claim-circuit-breakers-dominate]] downgraded to regime-specific finding
- [[claim-tax-dominates-cb-kernel]] strengthened

## Sources

- MIT OCW 17.810 Game Theory, Lecture 5: Repeated Games — punishment calibration theory (https://ocw.mit.edu/courses/17-810-game-theory-spring-2021/mit17_810s21_lec5.pdf)
- Zou et al. 2024 — Improving Alignment and Robustness with Circuit Breakers, arXiv:2406.04313 (https://arxiv.org/html/2406.04313v2)
- Pignati 2026 — Using Circuit Breakers to Secure the Next Generation of AI Agents, NeuralTrust (https://neuraltrust.ai/blog/circuit-breakers)
- Gray Swan AI — Circuit Breakers GitHub / Representation Rerouting (https://github.com/GraySwanAI/circuit-breakers)
- Grimm et al. 2014 — Facilitating Parameter Estimation and Sensitivity Analysis of Agent-Based Models, JASSS 17/3/11 (https://jasss.soc.surrey.ac.uk/17/3/11.html)
- TU Delft — Experimental Design for Agent-Based Models (https://ocw.tudelft.nl/wp-content/uploads/LectureExperimentalDesign_2012.pdf)
- Shukla 2025 — Adaptive Monitoring and Real-World Evaluation of Agentic AI Systems, arXiv:2509.00115 (https://arxiv.org/pdf/2509.00115.pdf)
- Schroeder de Witt et al. 2024 — Epsilon-Illusory Attacks on RL Agents, ICLR 2024 (https://openreview.net/pdf?id=F5dhGCdyYh)
- Lumenova AI — Taming Complexity: A Guide to Governing Multi-Agent Systems (https://www.lumenova.ai/blog/taming-complexity-governing-multi-agent-systems-guide/)
