---
description: "Master index for SWARM Research OS knowledge vault — claims, governance, topologies, experiments"
type: moc
created: 2026-02-18
---

# SWARM Research OS — Knowledge Vault

## Claims

Active findings from SWARM experiments, each linked to run evidence.

- [[claim-circuit-breakers-dominate]] — Circuit breakers alone outperform full governance stacks (high confidence)
- [[claim-tax-welfare-tradeoff]] — Transaction tax above 5% significantly reduces welfare (high confidence)
- [[claim-smarter-agents-earn-less]] — Deeper recursive reasoning hurts individual payoff (high confidence)
- [[claim-staking-backfires]] — Staking requirement hurts honest agents more than adversarial (medium confidence)

## Governance Mechanisms

Notes on individual governance levers: how they work, their parameters, evidence, and failure modes.

- [[circuit-breaker]] — Freezes agents exceeding toxicity/violation thresholds
- [[transaction-tax]] — Levies percentage tax on transactions

## Topologies

Network structure notes: how topology shapes agent behavior and governance effectiveness.

- [[small-world]] — Watts-Strogatz default testbed (k=4, p=0.15)

## Failure Patterns

Named vulnerability and attack patterns from red-team evaluations.

- `vault/failures/` — auto-populated from red-team runs

## Experiments

One note per run, auto-generated from run.yaml by the synthesis pipeline.

- `vault/experiments/` — 110 experiment notes synthesized from 112 runs

## Sweeps

Cross-run aggregations tracking convergence of parameter explorations.

- `vault/sweeps/` — sweep series summaries

## Methods

Reusable statistical and experimental methods.

- `vault/methods/` — methodology notes

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
