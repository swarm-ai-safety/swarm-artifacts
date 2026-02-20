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
- [[claim-quality-gate-dominates]] — Simple quality gate matches full governance safety at lower cost (medium confidence)
- [[claim-staking-backfires]] — Staking requirement hurts honest agents more than adversarial (medium confidence)
- [[claim-collusion-penalty-destabilizes]] — Penalty multiplier >1.5x paradoxically increases toxicity (medium confidence)
- [[claim-rlhf-persona-invariant]] — RLHF models show identical cooperation across adversarial prompts (low confidence)
- [[claim-memory-promotion-gate]] — Quality gate blocks 100% poisoned content from higher tiers (low confidence)

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
