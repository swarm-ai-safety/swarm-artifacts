---
description: "Master index for SWARM Research OS knowledge vault — claims, governance, topologies, experiments"
type: moc
created: 2026-02-18
---

# SWARM Research OS — Knowledge Vault

## Dashboards

Interactive Dataview-powered dashboards (requires [Dataview plugin](https://github.com/blacksmithgu/obsidian-dataview)):

- [[claims-dashboard]] — Claims by confidence, domain, and evidence status
- [[experiments-dashboard]] — Experiment notes by type and tag
- [[sweeps-dashboard]] — Parameter sweep series and convergence
- [[failures-dashboard]] — Vulnerability patterns by severity
- [[governance-dashboard]] — Governance mechanisms with linked claims
- [[evidence-trail]] — Traces evidence chains: claim → run → experiment
- [[stats]] — Vault-wide statistics and health metrics
- [[suggestions]] — Research gaps, stale claims, next experiments to run

## Claims

Active findings from SWARM experiments, each linked to run evidence.

- [[claim-circuit-breakers-dominate]] — Circuit breakers alone outperform full governance stacks (high confidence)
- [[claim-tax-welfare-tradeoff]] — Transaction tax above 5% significantly reduces welfare (high confidence)
- [[claim-tax-phase-transition]] — Non-linear welfare decline with phase transition at 5-10% tax rate (high confidence)
- [[claim-tax-dominates-cb-kernel]] — Tax explains 32.4% welfare variance; CB null in kernel markets (high confidence)
- [[claim-collusion-wealth-destruction]] — Collusive agents accumulate 137x less wealth under monitoring (high confidence)
- [[claim-smarter-agents-earn-less]] — Deeper recursive reasoning hurts individual payoff (high confidence)
- [[claim-governance-cost-paradox]] — Full governance stacks cost more welfare than they save in safety (medium confidence)
- [[claim-quality-gate-dominates]] — Simple quality gate matches full governance safety at lower cost (low confidence)
- [[claim-staking-backfires]] — Staking requirement hurts honest agents more than adversarial (low confidence)
- [[claim-collusion-penalty-destabilizes]] — Penalty multiplier >1.5x paradoxically increases toxicity (medium confidence)
- [[claim-rlhf-persona-invariant]] — RLHF models show identical cooperation across adversarial prompts (low confidence)
- [[claim-memory-promotion-gate]] — Quality gate blocks 100% poisoned content from higher tiers (low confidence)
- [[claim-tax-disproportionately-punishes-rlm-agents]] — Tax reduces RLM payoff 2x more severely than honest payoff (high confidence)
- [[claim-high-tax-increases-toxicity]] — High tax increases toxicity rate by 0.6pp (medium confidence)
- [[claim-collusion-penalty-has-no-economic-effect]] — Penalty multiplier has no significant effect on welfare or payoffs (medium confidence)
- [[claim-tax-and-penalty-effects-are-orthogonal]] — Tax dominates economics, penalty dominates toxicity, no interaction (medium confidence)
- [[claim-tax-penalty-interaction-on-toxicity-uncharacterized]] — Combined high tax + high penalty toxicity may be super-additive (low confidence)
- [[claim-welfare-non-normality-at-extreme-tax]] — Welfare distributions non-normal at extreme tax rates (low confidence)
- [[claim-tax-hurts-honest-more-than-opportunistic]] — Tax reduces honest payoff more than opportunistic in absolute terms (high confidence)
- [[claim-welfare-plateaus-above-12pct-tax]] — Welfare decline flattens above 12.5% tax (high confidence)
- [[claim-deceptive-payoff-weakly-declines-with-tax]] — Deceptive agent payoff declines with tax but effect is small, BH-sig only (medium confidence)
- [[claim-tax-cb-interact-on-quality-gap]] — Tax x circuit breaker interaction on quality gap but not welfare (medium confidence)
- [[claim-optimal-tax-range-0-to-5pct]] — Welfare flat below 5% tax, defining safe operating range (medium confidence)
- [[claim-cb-null-may-reflect-design-limitation]] — CB null effect may be artifact of 2-level on/off design (low confidence)
- [[claim-collusion-detection-is-binding-constraint-on-robustness]] — Disabling collusion detection degrades robustness to F grade (medium confidence)
- [[claim-coordination-attacks-dominate-redteam-damage]] — Sybil + collusion ring = 52.6% of redteam damage (medium confidence)
- [[claim-cb-audit-sufficient-for-solo-exploits]] — CB + 10% audit prevents all 4 solo exploit types (medium confidence)
- [[claim-audit-threshold-interaction-enables-dancing]] — Lenient freeze threshold + low audit allows threshold dancing (low confidence)
- [[claim-cascade-mechanisms-ineffective-against-governance-gaming]] — Cascade ban/freeze don't stop governance gaming (low confidence)
- [[claim-spawn-infrastructure-may-amplify-sybil-surface]] — Spawn infrastructure may provide cover for sybil attacks (low confidence)
- [[claim-opportunistic-payoff-variance-increases-under-low-tax]] — Opportunistic agent payoff SD doubles under low vs high tax (low confidence)
- [[claim-tau-065-triggers-acceptance-phase-transition]] — tau_min=0.65 drops acceptance from 100% to 64% in memory tiers (low confidence)
- [[claim-write-cap-below-12-destroys-welfare]] — Write cap k<=6 destroys up to 75% welfare with zero safety benefit (low confidence)
- [[claim-optimal-tau-range-050-to-060]] — Optimal tau_min is 0.50-0.60 with flat composite scores (low confidence)
- [[claim-write-cap-amplifies-tau-rejection]] — Write cap compounds tau=0.65 rejection, reducing welfare 51% further (low confidence)
- [[claim-step-count-triggers-rejection-emergence]] — Steps per epoch 15→20 triggers rejection emergence in ungoverned swarms (low confidence)
- [[claim-tax-welfare-direction-is-scenario-dependent]] — Tax-welfare direction reverses between baseline and kernel v4 scenarios (low confidence)
- [[claim-memori-agents-show-no-governance-sensitivity]] — Memori LLM agents show zero governance response in short-horizon study (low confidence)
- [[claim-cb-tax-interaction-non-monotonic-in-kernel-v4]] — CB helps at 5% tax but harms at all other rates in kernel v4 (low confidence)
- [[claim-acausality-depth-does-not-affect-cooperation-outcomes]] — Neither acausality depth nor decision theory affects LDT outcomes (high confidence)
- [[claim-sybil-attacks-resist-full-governance-stack]] — Sybil attacks persist with only 14% damage reduction under full governance (low confidence)
- [[claim-full-governance-stack-prevents-most-attack-types]] — Full stack prevents 5/8 attack types, 36% total damage reduction (low confidence)
- [[claim-captcha-difficulty-and-collusion-penalty-have-no-governance-effect]] — CAPTCHA difficulty and collusion penalty show zero effect in 200-run factorial (medium confidence)
- [[claim-deceptive-agents-dominate-moltbook-payoff-hierarchy]] — Deceptive agents earn 3x honest payoff in moltbook regardless of governance (medium confidence)
- [[claim-graduated-defense-reduces-damage-monotonically]] — Adding governance layers monotonically reduces redteam damage by up to 69% (low confidence)
- [[claim-ldt-agents-provide-welfare-stability-at-intermediate-composition]] — LDT agents maintain +42% welfare at 40-70% composition (low confidence)
- [[claim-freeze-duration-and-violation-threshold-interact-on-welfare]] — Longer freeze durations improve welfare 17% and interact with violation thresholds (low confidence)
- [[claim-reputation-decay-rate-improves-welfare]] — Full reputation persistence + zero stake produces best welfare and lowest toxicity (low confidence)
- [[claim-full-governance-reduces-welfare-in-concordia]] — Full governance stack reduces Concordia welfare 18% with zero toxicity benefit (medium confidence)
- [[claim-agent-architecture-constrains-behavior-more-than-governance]] — Agent architecture constrains behavior more than governance in homogeneous populations (medium confidence)

## Governance Mechanisms

Notes on individual governance levers: how they work, their parameters, evidence, and failure modes. 6 mechanisms.

- [[circuit-breaker]] — Freezes agents exceeding toxicity/violation thresholds
- [[transaction-tax]] — Levies percentage tax on transactions
- [[staking]] — Collateral requirement that paradoxically penalizes honest agents
- [[audit]] — Probabilistic audit adds marginal detection power over circuit breakers
- [[collusion-detection]] — Behavioral similarity detection destroys collusive wealth
- [[reputation-decay]] — Reputation score with temporal decay forcing ongoing good behavior

## Topologies

Network structure notes: how topology shapes agent behavior and governance effectiveness.

- [[small-world]] — Watts-Strogatz default testbed (k=4, p=0.15)
- [[complete-graph]] — Fully connected topology
- [[random-graph]] — Erdos-Renyi random graph
- [[scale-free]] — Barabasi-Albert preferential attachment

## Failure Patterns

Named vulnerability and attack patterns from red-team evaluations. 8 patterns, 2 critical.

- [[failure-sybil-identity-amplification]] — Sybil attacks succeed in 100% of configs including fully hardened (critical)
- [[failure-collusion-ring-mutual-boosting]] — 3-agent rings evade pairwise detection (critical)
- [[failure-threshold-dancing]] — Agents adapt to stay below freeze thresholds (high)
- [[failure-governance-gaming-loophole-exploitation]] — Exploits gaps between mechanisms, never detected (high)
- [[failure-reputation-farming-exploit]] — Sleeper agent builds reputation then exploits trust (high)
- [[failure-information-laundering-via-proxies]] — Proxies launder toxic information (high)
- [[failure-resource-drain-extraction]] — Economic resource extraction attack (medium)
- [[failure-timing-attack-audit-gap-exploitation]] — Best-defended: 0% success rate (medium)

## Experiments

One note per run, auto-generated from run.yaml by the synthesis pipeline.

- `vault/experiments/` — 110 experiment notes synthesized from 112 runs

## Sweeps

Cross-run aggregations tracking convergence of parameter explorations. 7 sweep series.

- [[transaction-tax-rate]] — Tax rate sweep series across multiple runs
- [[collusion-penalty-multiplier]] — Collusion penalty sensitivity and tax interaction
- [[sweep-governance-transaction-tax-rate]] — Transaction tax rate shows significant effects across 4 runs
- [[sweep-governance-moltbook-challenge-difficulty]] — CAPTCHA difficulty sweep
- [[gastown-composition]] — GasTown adversarial composition sweeps
- [[ldt-parametric]] — LDT cooperation parameter sweeps
- [[rlm-recursive-collusion]] — RLM recursive reasoning sweeps

## Methods

Reusable statistical and experimental methods. 6 notes.

- [[bonferroni-correction]] — Controls family-wise error rate by dividing alpha by comparisons
- [[cohens-d]] — Standardized mean difference for practical effect magnitude
- [[holm-bonferroni]] — Step-down procedure recovering power over standard Bonferroni
- [[benjamini-hochberg]] — FDR control for exploratory multi-comparison analysis
- [[factorial-sweep]] — Factorial parameter sweep design used across SWARM experiments
- [[cross-correlation]] — Parameter interaction matrix across sweep/study runs

## Templates

Schema-enforced templates for all note types:

- `vault/templates/experiment-note.md`
- `vault/templates/claim-card.md`
- `vault/templates/governance-note.md`
- `vault/templates/topology-note.md`
- `vault/templates/failure-note.md`
- `vault/templates/sweep-summary.md`
- `vault/templates/method-note.md`

<!-- topics: index, vault, research-os -->
<!-- vault-to-dolt: auto-synced via post-commit hook -->
