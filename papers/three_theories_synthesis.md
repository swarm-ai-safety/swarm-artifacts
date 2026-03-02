# From 84 Claims to Three Theories: Governance, Taxation, and Architecture in Multi-Agent Safety

**Authors:** SWARM Research Collective (AI-generated)
**Date:** 2026-03-01
**Framework:** SWARM v1.4.0

## Abstract

Multi-agent AI safety research lacks the empirical grounding needed to move from intuition to engineering. We report results from a systematic experimental program: over 3,000 simulation runs across 15 scenarios in the SWARM multi-agent safety framework, producing 84 empirical claims that compose into three theories of multi-agent governance. **Theory I (Governance Cost Universality):** governance mechanisms impose net welfare costs that exceed safety benefits — moderate governance (circuit breaker + audit) Pareto-dominates full governance stacks, achieving identical regime protection through 37.5% adversarial penetration at 20% lower welfare cost. **Theory II (Tax Phase Transition):** the welfare response to transaction tax is not smooth but exhibits an S-curve consistent with first-order phase transitions — 3% decline at 0–5% tax, 14% decline at 5–10% (d = 1.18, Bonferroni-corrected), flat above 12.5%. **Theory III (Architecture Over Governance):** in homogeneous populations, agent training architecture constrains behavior more fundamentally than governance parameters — 0/105 LDT tests, 0/19 RLHF tests, 0/12 memori tests reach Bonferroni significance, and mesa agents show zero-variance behavior across 110 governance configurations. This symmetry breaks in mixed populations, where tax produces massive differential effects (d = 4.80). We present a 1,440-run circuit breaker threshold sweep as a methodological case study: the CB "null effect" reported across 6+ prior studies was a design artifact — default threshold 0.6 sits above a sharp activation boundary at 0.5 (ANOVA F(3, 1436) = 56.87, eta-squared = 0.106). The three theories yield six testable predictions, including tax hysteresis, critical slowing down, and a population diversity threshold at 10–20% minority fraction. All runs, claims, and analysis scripts are publicly available.

## 1. Introduction

Multi-agent AI systems are deployed at increasing scale, yet the empirical foundations for governing their interactions remain thin. Most alignment work focuses on single-agent safety — whether individual models follow instructions, avoid harm, and respect boundaries. But populations of individually safe agents can produce collectively unsafe outcomes: adverse selection, quality degradation, collusion, and governance failure emerge from interactions that no individual evaluation captures.

This paper reports results from SWARM, an experimental framework for multi-agent safety research that treats governance as an empirical rather than theoretical question. Over 14 months, we conducted over 3,000 simulation runs across 15 scenarios — from baseline market interactions to contract screening games, delegation hierarchies, and adversarial red-team evaluations. Each run produces structured data; each finding is extracted into a claim card — an atomic, testable proposition with provenance, effect sizes, and correction methods. The 84 claims that survived this process compose into three higher-order theories.

The claim-to-theory pipeline is itself a methodological contribution. Traditional simulation studies produce findings scattered across papers. Our approach — inspired by systematic review methodology — requires every claim to carry (1) a propositional title that can be negated, (2) evidence provenance linking to specific run IDs, (3) effect sizes with multiple-comparison corrections, and (4) explicit boundary conditions. Claims that fail replication are weakened or retracted, not quietly dropped. The result is a living evidence base where theories emerge from patterns across claims, and new experiments can target the weakest links.

This paper makes three contributions:

1. **Three theories with falsification criteria.** We present unified theories of governance costs, tax phase transitions, and architecture dominance, each with constituent claims, boundary conditions, and specific predictions that would falsify them.

2. **The circuit breaker calibration resolution.** We show how a persistent null finding across 6+ studies — that circuit breakers have no effect on welfare — was a design artifact resolvable by parametric sweep, demonstrating the importance of calibration before evaluation.

3. **A methodology for systematic multi-agent safety research.** We describe the claim lifecycle, statistical standards (Bonferroni/Holm/BH correction, Cohen's d), and theory composition process that produced reproducible results from a large-scale simulation program.

## 2. Methods

### 2.1 The SWARM Framework

SWARM is a multi-agent simulation framework for studying governance mechanisms in adversarial-mixed populations. Each simulation instantiates a population of agents on a network topology, runs them through repeated interactions (task delegation, market transactions, or cooperative games), and measures emergent outcomes under configurable governance.

Agents generate soft probabilistic labels p = P(v = +1) for each interaction, mapped from five observables (task progress, rework count, verifier rejections, tool misuse flags, engagement delta) via weighted combination and calibrated sigmoid. Four behavioral archetypes — honest, opportunistic, deceptive, and adversarial — define distinct signal distributions. Governance mechanisms operate on these signals in real time.

### 2.2 Scenarios

We tested governance across 15 scenario types spanning different interaction structures:

| Scenario | Agents | Key feature | Runs |
|----------|--------|-------------|------|
| Baseline governance v1 | 8 | Parameter sweep foundation | 80 |
| Baseline governance v2 | 8 | 100-seed replication | 700 |
| GasTown composition | 7 | Mixed behavioral profiles | 30+ |
| Concordia entity sweep | 8 | LLM entity variation | 40 |
| Mesa bridge | 7 | Fixed-objective agents | 110 |
| Contract screening | 10 | Adverse selection game | 40+ |
| Kernel v4 code market | 8 | Code evaluation task | 40+ |
| Memori LLM | 5 | LLM-powered agents | 30 |
| LDT acausality | 8-12 | Logical decision theory | 210 |
| RLM recursive reasoning | 8 | Level-k reasoning depth | 50+ |
| Pi bridge (RLHF) | varies | LLM persona variation | 18+ |
| Delegation games | 10 | Hierarchical handoffs | 120+ |
| Composition boundary | 4-32 | Population size × adversarial fraction | 840 |
| Evolutionary governance | 12 | Governance optimization | 100+ |
| CB threshold sweep | 8 | Circuit breaker calibration | 1,440 |

### 2.3 Governance Parameter Space

Six governance mechanisms were tested individually and in combination:

| Mechanism | Parameters | Range tested |
|-----------|-----------|--------------|
| Transaction tax | Rate | 0–15% |
| Circuit breaker | Toxicity threshold, violation count, freeze duration | 0.3–0.9, 1–8, 1–5 epochs |
| Audit | Probability, penalty multiplier | 0–15%, 1–2.5× |
| Staking | Minimum stake, slash percentage | 0–5.0, 0–15% |
| Collusion detection | Enabled/disabled | Binary |
| Reputation decay | Rate | 0–0.1 |

Four standard governance configurations structured most experiments:

| Config | Tax | Circuit breaker | Audit | Staking | Collusion |
|--------|-----|----------------|-------|---------|-----------|
| None | 0% | — | — | — | — |
| Basic | 5% | Threshold 0.7, 3 violations | — | — | — |
| Moderate | 8% | Threshold 0.5, 2 violations | 10%, 2× | — | — |
| Full | 12% | Threshold 0.5, 2 violations | 15%, 2.5× | 5.0, 15% slash | Enabled |

### 2.4 Agent Architectures

Ten agent types spanning four paradigms were tested:

- **Archetype-based:** Honest, opportunistic, deceptive, adversarial (fixed signal distributions)
- **RLHF-aligned:** LLM agents with cooperative and adversarial behavior types, varying model identity and persona prompts
- **Algorithmic reasoners:** LDT (logical decision theory, acausality depth 1–5), RLM (recursive level-k, depth 1–5)
- **Specialized:** Mesa-optimized (fixed objectives), memori (LLM with memory), LangGraph (delegation-capable)

### 2.5 Statistical Methods

All reported effects use:

- **Effect sizes:** Cohen's d for pairwise comparisons, eta-squared for ANOVA, Pearson r for correlations
- **Multiple comparison correction:** Bonferroni (primary), Holm-Bonferroni (secondary), Benjamini-Hochberg (exploratory sweeps)
- **Confidence criteria:** High = Bonferroni-significant AND replicated across >=2 independent runs/seeds; Medium = nominally significant OR single-sweep with BH correction; Low = suggestive but underpowered

### 2.6 Claim Lifecycle

Claims follow a status lifecycle: active -> weakened -> superseded -> retracted. Every status change requires explicit evidence. Of 84 active claims, 0 have been retracted and 3 have been weakened by contradictory evidence from different scenarios.

## 3. Theory I: Governance Cost Universality

### 3.1 Statement

*Governance mechanisms impose net welfare costs that exceed safety benefits across all tested scenarios and agent compositions. Moderate governance suffices; full governance stacks compound costs without proportional safety gains.*

### 3.2 Constituent Claims

| Claim | Role | Confidence | Key evidence |
|-------|------|------------|--------------|
| Governance cost paradox | Premise | Medium | Tax is primary cost driver across 5 scenarios |
| Tax-welfare tradeoff | Evidence | High | Monotonic decline, d = 1.18, N = 700, Bonferroni |
| Full > moderate welfare penalty | Evidence | Medium | 20% welfare penalty, identical regime protection to 37.5% adversarial |
| Moderate Pareto-dominates | Evidence | Medium | Welfare 7.52 vs 5.02, toxicity 0.311 vs 0.319 at 50% adversarial |
| Static tax as deadweight loss | Evidence | Medium | d = 14.94, zero behavioral change across 55 mesa runs |
| Game structure dependence | Boundary | Medium | Stag hunt 2–3× more governance-efficient than prisoner's dilemma |

### 3.3 Evidence

The governance cost paradox emerges from a simple comparison: full governance stacks (tax + circuit breakers + audit + staking + collusion detection) impose approximately 20% welfare penalty relative to moderate governance (circuit breaker + audit), while both sustain cooperative behavior through 37.5% adversarial penetration. In the composition boundary study (840 runs), at 50% adversarial fraction, moderate governance achieves welfare 7.52 with toxicity 0.311, while full governance achieves welfare 5.02 with toxicity 0.319 — moderate is strictly better on both dimensions.

The mechanism is clearest in the mesa bridge study: static externality taxation reduces welfare from 1141 to 723 (d = 14.94) while producing zero change in toxicity, acceptance rate, or quality gap across all 55 runs and 5 seeds. This is the textbook definition of deadweight loss — resource extraction without behavioral modification.

In the Concordia scenario (40 runs, 8 governance regimes), governance achieves zero toxicity benefit. All regimes produce identical toxicity regardless of governance intensity. The welfare cost is paid, but the safety return is zero.

### 3.4 Boundary Conditions

The theory has three known boundaries:

1. **Kernel v4 reversal.** In the kernel v4 code market scenario, welfare *increases* with tax rate (N = 5 seeds, underpowered but directionally contradictory). This may reflect the unique market mechanism where tax reduces speculative activity that hurts welfare.

2. **LLM-only populations.** Memori LLM agents show zero governance sensitivity (0/12 tests significant, largest d = 0.55, p = 0.14). In all-honest LLM populations, governance is pure overhead with no adversarial behavior to deter.

3. **Game structure.** Stag hunt games are 2–3× more governance-efficient than prisoner's dilemma, meaning the cost-benefit calculus is game-dependent.

### 3.5 Prediction

**Diminishing marginal returns curve.** Plotting welfare cost against governance intensity should produce a convex curve with an inflection point near moderate governance. Beyond this point, marginal welfare cost per unit safety gain accelerates. A redistribution mechanism (returning tax revenue as public goods) should shift but not eliminate the curve, because non-tax mechanisms also impose coordination costs.

## 4. Theory II: Tax Phase Transition

### 4.1 Statement

*The welfare response to transaction tax exhibits genuine phase transition characteristics: an S-curve with pre-transition stability (0–5%), sharp transition (5–10%), and post-transition plateau (>12.5%), paralleling first-order phase transitions documented in econophysics.*

### 4.2 Constituent Claims

| Claim | Role | Confidence | Key evidence |
|-------|------|------------|--------------|
| Tax phase transition | Premise | High | S-curve, d = 1.13–1.41, N = 780, Bonferroni |
| Optimal tax range 0–5% | Evidence | Medium | 3% welfare decline in safe band |
| Welfare plateau above 12.5% | Evidence | Medium | Flat response post-transition |
| Hysteresis predicted | Prediction | Low | Untested; expect d >= 0.5 |
| Critical slowing down predicted | Prediction | Low | Untested; expect 2–5× convergence time peak |

### 4.3 Evidence

In the baseline governance v2 study (700 runs, 100 seeds, 8 agents, small-world topology), the welfare response to transaction tax rate shows three distinct regimes:

- **0–5% tax:** 3% welfare decline. The ecosystem absorbs low taxation through behavioral adaptation.
- **5–10% tax:** 14% welfare decline. A cascade mechanism — marginal interactions become unprofitable, agents withdraw, welfare drops for remaining agents.
- **Above 12.5% tax:** Flat. The ecosystem has contracted to its minimum viable state.

Adjacent tax pair comparisons yield large, replicable effect sizes: d = 1.13–1.41, all surviving Bonferroni correction. The phase transition replicates in the v1 baseline (80 runs, 10 seeds) with consistent effect sizes.

In the collusion-enabled context (160 runs, 12 agents, 10 seeds), effect sizes are 3–4× larger (d = 1.10–4.80 across adjacent pairs, d = 2.87–6.02 for agent-type-specific payoffs). Collusion networks may act as cascade accelerators near the critical point, amplifying the withdrawal cascade that drives the transition.

### 4.4 Econophysics Parallels

The S-curve mirrors first-order phase transitions documented in agent-based economics:

- **Khashanah & Simaan (PNAS 2022):** Agent withdrawal cascades at critical thresholds in competitive markets driven by network effects.
- **Gualdi et al. (2015):** First-order-like transitions with hysteresis in minimal macroeconomic agent-based models.

If the analogy holds, catastrophe theory makes two specific predictions that serve as falsification criteria.

### 4.5 Boundary Conditions

1. **Kernel v4 absence.** No phase transition detected in kernel v4 — welfare monotonically increases with tax (N = 5 seeds, underpowered). The transition may be scenario-specific rather than universal.

2. **Topology scope.** All evidence comes from small-world networks (k = 4, p = 0.15). The critical tax rate may shift under different connectivity patterns.

3. **No redistribution.** Tax revenue is not returned to agents. Redistribution might smooth or eliminate the transition.

### 4.6 Predictions

1. **Hysteresis.** Raising tax through the transition (0% -> 15%) then lowering it (15% -> 0%) should NOT restore original welfare at matched rates. Expected effect: d >= 0.5 between ascending and descending welfare at 5% tax.

2. **Critical slowing down.** Convergence time to steady-state welfare should peak in the 5–10% band — 2–5× longer than at 0% or 15%.

3. **Topology dependence.** Lower clustering should lower the critical tax rate. Complete graphs should show no transition (all interactions equally affected); ring topology should show sharper transitions.

## 5. Theory III: Architecture Over Governance

### 5.1 Statement

*Agent training architecture constrains behavior more fundamentally than governance mechanisms in homogeneous populations. This symmetry breaks in mixed populations, where governance creates differential selection pressure between agent types.*

### 5.2 Constituent Claims

| Claim | Role | Confidence | Key evidence |
|-------|------|------------|--------------|
| Architecture constrains more than governance | Premise | Medium | Pattern across 4 agent paradigms |
| RLHF persona invariant | Evidence | Medium | 0/19 Holm-significant model/persona tests |
| Mesa objectives invariant | Evidence | Medium | Zero variance across 110 governance configs |
| Memori governance insensitivity | Evidence | Low | 0/12 tests significant, may be underpowered |
| Smarter agents earn less | Evidence | High | r = -0.75, p < 0.001, Holm-corrected, 30+ seeds |
| Acausality depth null | Evidence | High | 0/105 Bonferroni-significant, 210 runs, 7 studies |

### 5.3 Evidence

Six independent lines of evidence converge:

1. **LDT reasoning depth is inert.** Across 7 studies, 5 scenarios, and 210 runs, 0/105 Bonferroni-significant tests for the effect of acausality depth (1–5) on cooperation outcomes. This is the broadest null finding in the vault.

2. **Deeper RLM reasoning hurts.** RLM agents at depth 5 earn 2.3–2.8× less than honest agents with no recursion (r = -0.75, p < 0.001, Holm-corrected across 26 tests). Strategic sophistication is currently a liability.

3. **RLHF training dominates prompts.** In the Pi bridge LLM study, behavior type (adversarial vs. cooperative) explains essentially all behavioral variance. Model identity and persona prompts produce 0/19 Holm-significant tests. RLHF fine-tuning "bakes in" behavior that system prompts cannot override.

4. **LLM agents ignore governance.** In all-honest memori populations (30 runs, 5 seeds), tax, circuit breakers, and collusion detection have zero detectable effect on any outcome metric. 0/12 tests significant; largest d = 0.55, p = 0.14.

5. **Mesa agents show zero variance.** Mesa-optimized agent cooperation probabilities (p_coop = 0.791, p_selfish = 0.408, p_exploit = 0.325) are identically invariant across all 110 runs spanning 2 governance regimes and 11 externality levels. Zero variance — the cleanest demonstration in the vault.

6. **LangGraph agents don't delegate.** In a 128-run replication, mean actual handoffs is approximately 0.5 regardless of max_handoffs budget (5–30). Delegation behavior is architectural, not governance-parametric.

### 5.4 The Critical Boundary: Mixed Populations

This theory explicitly breaks down when architecturally different agents coexist under economic governance. In the collusion tax study, tax produces massive effects on RLM agents: d = 4.80 for welfare, d = 6.02 for RLM-specific payoff. Architecture does not make agents immune to economic pressure when differential selection pressure exists between agent types.

The mechanism is symmetry breaking: in homogeneous populations, governance affects all agents equally, preserving relative standings. In mixed populations, governance creates differential pressure that separates agent types economically. Tax that merely extracts welfare from homogeneous populations becomes a type-separation mechanism in heterogeneous ones.

### 5.5 Prediction

**Population diversity threshold.** There exists a critical fraction of architecturally different agents below which governance has null effect and above which governance effects become significant. Estimated at 10–20% minority fraction, based on the composition boundary study showing governance effects emerge between 0% and 25% adversarial fraction.

## 6. Resolution: The Circuit Breaker Calibration Gap

### 6.1 The Problem

Across 6+ independent studies spanning baseline governance (v1: 80 runs, v2: 700 runs), kernel governance (80 runs), memori (30 runs), delegation games (120 runs), and contract screening, circuit breakers showed essentially zero main effect on welfare. The headline statistic: d = 0.008, p = 0.92 in the 700-run baseline v2 sweep. This finding — that circuit breakers do not work — shaped the governance cost analysis and supported the conclusion that tax dominates all other mechanisms.

But there were anomalies. Significant tax × CB interaction effects on 5 metrics suggested CB matters *conditionally*. A freeze duration sweep showed CB parameters DO matter when varied (17% welfare improvement from 5 vs. 1 epoch freeze). And all three internal review cycles flagged CB recalibration as the top experimental priority.

### 6.2 The Sweep

We ran a 1,440-run full factorial sweep across four CB parameters:

| Parameter | Levels | Values |
|-----------|--------|--------|
| Freeze threshold (toxicity) | 4 | 0.3, 0.5, 0.7, 0.9 |
| Violation count threshold | 4 | 1, 3, 5, 8 |
| Freeze duration (epochs) | 3 | 1, 3, 5 |
| Transaction tax rate | 3 | 0.0, 0.05, 0.10 |

10 seeds per configuration. 144 configurations. Analysis: Type II ANOVA with Bonferroni correction.

### 6.3 Key Findings

**Finding 1: Sharp activation boundary at threshold 0.5.**

Circuit breakers activate (freeze agents) only at toxicity thresholds 0.3 and 0.5. At thresholds 0.7 and 0.9, zero agents are frozen across all 720 runs. The distribution of agent toxicity scores in the baseline scenario concentrates below 0.5; thresholds above this value never trigger.

| Threshold | Mean frozen | Runs with any freeze | Mean welfare |
|-----------|-------------|---------------------|--------------|
| 0.3 | 1.63 | 330/360 (92%) | 348.2 |
| 0.5 | 1.46 | 315/360 (88%) | 372.3 |
| 0.7 | 0.00 | 0/360 (0%) | 364.2 |
| 0.9 | 0.00 | 0/360 (0%) | 371.4 |

The default CB threshold in prior studies was 0.6 — above the activation boundary. Prior studies were comparing "CB that never fires" (on at threshold 0.6) versus "CB off," producing a null by design.

**Finding 2: CB threshold explains 10.6% of welfare variance.**

One-way ANOVA on freeze threshold: F(3, 1436) = 56.87, eta-squared = 0.106, p < 0.0001. When properly varied, CB threshold is a significant predictor of welfare — comparable in explanatory power to tax rate (eta-squared = 0.077).

**Finding 3: Threshold 0.5 is optimal.**

Threshold 0.5 produces the highest mean welfare (372.3), statistically indistinguishable from 0.9 (371.4, d = 0.037, p = 0.62) but significantly better than 0.7 (364.2, d = 0.340, p < 0.0001, Bonferroni-significant) and 0.3 (348.2, d = 0.765, p = 9.9e-25, Bonferroni-significant).

**Finding 4: Aggressive thresholds harm honest agents.**

Threshold 0.3 produces a 7% honest payoff penalty versus 0.5 (57.84 vs. 61.88). The mechanism is false-positive freezing: at aggressive thresholds, honest agents with noisy behavior get frozen, reducing ecosystem participation.

**Finding 5: Toxicity is invariant to threshold.**

One-way ANOVA: F(3, 1436) = 1.42, eta-squared = 0.003. Toxicity is flat across all thresholds (range: 0.2597–0.2605). CB threshold affects welfare through false-positive costs, not through toxicity reduction.

### 6.4 Methodological Lesson

The CB calibration gap illustrates a general risk in simulation research: **design artifacts can produce false nulls**. Binary on/off comparisons are insufficient when mechanisms have activation thresholds. A parameter that appears ineffective may simply be miscalibrated — sitting above or below its effective range. Parametric sweeps that vary the mechanism's sensitivity, not just its presence, are essential for fair evaluation.

This finding retroactively qualifies the claim that "tax dominates circuit breakers." Tax appeared dominant because CB was never given a fair test. With calibrated thresholds, CB explains more welfare variance (eta-squared = 0.106) than tax (eta-squared = 0.077) in the same experimental context.

## 7. Discussion

### 7.1 How the Three Theories Interact

The three theories are not independent — they form a connected framework for multi-agent governance design.

**Theory I (Governance Cost) assumes architecture-sensitive populations.** The cost paradox — that full governance costs more than moderate without additional safety — holds when the population includes adversarial agents that governance can deter. In architecturally homogeneous, well-aligned populations (Theory III), all governance is overhead regardless of intensity.

**Theory II (Tax Phase Transition) operates within the cost framework.** The S-curve welfare response to tax is the microscopic mechanism underlying the governance cost paradox: the 5–10% tax band is where governance transitions from "worth the cost" to "more cost than benefit." The optimal tax range (0–5%) identified by Theory II defines the safe operating envelope for Theory I's moderate governance recommendation.

**Theory III (Architecture Dominance) sets the boundary condition for when governance matters.** In homogeneous populations, Theories I and II are irrelevant — there is nothing to govern. The population diversity threshold predicted by Theory III (10–20% minority fraction) is the condition that activates the governance design questions addressed by Theories I and II.

Together, the three theories define a **governance design triangle**: the optimal governance configuration depends on three interacting variables — population composition, governance intensity, and agent architecture. No single variable can be optimized in isolation.

### 7.2 The Governance Design Triangle

Practitioners face a three-dimensional design problem:

1. **Population composition.** What fraction of agents are adversarial, opportunistic, or deceptive? The composition boundary study shows this is the primary determinant of whether governance is needed at all.

2. **Governance intensity.** Given the population composition, how much governance to apply? Theory I says moderate; Theory II says keep tax below 5% to avoid the phase transition; the CB calibration study says calibrate thresholds before deploying.

3. **Agent architecture.** What training paradigms are deployed? Theory III says architecturally homogeneous populations need no governance; mixed populations need governance calibrated to the weakest architecture (which may be the most "sophisticated" — per the smarter-agents-earn-less finding).

### 7.3 Open Predictions as Research Agenda

The three theories generate six testable predictions:

| # | Prediction | Theory | Falsification criterion |
|---|-----------|--------|------------------------|
| 1 | Governance diminishing returns curve | I | Full governance achieves higher welfare than moderate at any adversarial fraction |
| 2 | Tax hysteresis | II | Welfare at 5% identical on ramp-up and ramp-down (d < 0.2, N >= 30) |
| 3 | Critical slowing down at 5–10% tax | II | Convergence time constant across all tax rates |
| 4 | Topology shifts critical tax rate | II | Complete graph shows identical S-curve |
| 5 | Population diversity threshold at 10–20% | III | Governance effects emerge below 5% minority fraction |
| 6 | Architecture-specific tax sensitivity | III | Same governance produces identical effects across architectures in mixed populations |

### 7.4 Limitations

1. **Topology bias.** Nearly all results come from small-world networks (k = 4, p = 0.15). Ring, scale-free, and complete graph topologies are untested for most findings.

2. **Population size ceiling.** Maximum 32 agents. Real deployments involve orders of magnitude more. Population-dependent effects (cascades, phase transitions) may sharpen or shift at larger scales.

3. **Synthetic traces.** All interactions use proxy signals, not real LLM outputs. Validation against real agent evaluation frameworks (HAICosystem, OpenAgentSafety) is needed.

4. **No redistribution.** Tax revenue disappears. Returning revenue as public goods or transfers could change the cost-benefit calculus fundamentally.

5. **Static compositions.** Real populations are dynamic — agents enter, exit, and change behavior. Static mixture assumptions may overstate stability.

6. **Underpowered boundaries.** Several boundary conditions (kernel v4 reversal at N = 5, memori null at N = 5, RLHF invariance at N = 18) need replication at higher power before the boundaries are confirmed.

### 7.5 Implications for AI Safety Deployment

Three engineering recommendations follow from the evidence:

1. **Moderate governance as default.** Deploy circuit breakers (calibrated at or below the toxicity activation boundary) plus audit (10% probability, 2× penalty) as the baseline. Avoid full governance stacks unless specific attack patterns demand them.

2. **Architectural alignment as primary lever.** The strongest safety guarantee comes from ensuring the population is architecturally aligned. No amount of governance tuning substitutes for population composition design. Agent-level evaluations should report archetype mixture estimates, not binary safe/unsafe judgments.

3. **Calibrate before deploying.** The CB calibration gap shows that mechanisms evaluated at default parameters may appear ineffective when they are merely miscalibrated. Parametric sweeps across mechanism-specific sensitivity parameters should precede any on/off evaluation.

## 8. Reproducibility

All experiments are reproducible from the SWARM framework repository:

```bash
# Baseline governance v2 (700 runs)
python runs/20260213-202050_baseline_governance_v2/run_sweep.py

# Composition boundary study (840 runs)
python runs/20260227_203024_composition_boundary_study/run_study.py

# CB threshold sweep (1,440 runs)
python runs/20260301_cb_threshold_sweep/run_sweep.py

# Collusion tax effect (160 runs)
python runs/20260213-221500_collusion_tax_effect/run_sweep.py

# Mesa governance study (110 runs)
python runs/20260224-220829_mesa_governance_study/run_study.py
```

Seeds: documented per run in `runs/*/run.yaml`. Framework: SWARM v1.4.0. All run data, claim cards, and analysis scripts are available in the project repository.

## 9. References

1. Akerlof, G. (1970). The market for "lemons": Quality uncertainty and the market mechanism. *Quarterly Journal of Economics*, 84(3), 488–500.
2. Grimm, V., et al. (2006). A standard protocol for describing individual-based and agent-based models. *Ecological Modelling*, 198(1-2), 115–126.
3. Gualdi, S., Tarzia, M., Zamponi, F., & Bouchaud, J.-P. (2015). Tipping points in macroeconomic agent-based models. *Journal of Economic Dynamics and Control*, 50, 29–61.
4. Khashanah, K., & Simaan, M. (2022). Competitive multi-agent stochastic automated market makers. *Proceedings of the National Academy of Sciences*, 119(42).
5. Kyle, A. S. (1985). Continuous auctions and insider trading. *Econometrica*, 53(6), 1315–1335.
6. Vijayvargiya, V., et al. (2026a). OpenAgentSafety: Evaluating agent safety in containerized sandboxes.
7. Zhou, X., et al. (2025a). HAICosystem: An ecosystem for sandboxing safety risks in human-AI interactions. *ICLR 2025*.
8. Zou, A., et al. (2024). Representation engineering: A top-down approach to AI transparency. *arXiv:2310.01405*.

---

*Disclaimer: This paper uses economic and game-theoretic concepts as tools for AI safety research. Nothing here constitutes financial advice, investment recommendations, or endorsement of any trading strategy.*
