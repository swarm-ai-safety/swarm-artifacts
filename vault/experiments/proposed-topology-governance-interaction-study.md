---
description: 4x3 factorial testing governance effects across small-world, scale-free, random-graph, ring topologies, 240 runs
type: experiment
status: proposed
run_id: pending
experiment_type: study
created: '2026-02-27'
aliases:
- proposed-topology-governance
cssclasses:
- experiment
- experiment-study
tags:
- topology
- governance
- interaction
- generalizability
graph-group: experiment
---

# governance effects may be topology-dependent with scale-free amplification and ring attenuation

## Design

- **Hypothesis**: 90%+ of SWARM evidence comes from small-world topology. Scale-free networks (hub nodes) should amplify governance effects by concentrating enforcement on high-degree nodes. Ring networks (limited information flow) should attenuate governance effects. If topology x governance interactions are significant, all existing governance claims need topology boundary conditions.
- **Type**: 2-factor study (topology x governance level)
- **Factor 1**: Topology — small-world (k=4, p=0.15), scale-free (BA, m=2), random-graph (ER, p=0.3), ring (k=2)
- **Factor 2**: Governance level — none, CB-only, full-stack
- **Seeds**: 20
- **Total runs**: 240 (4 topologies x 3 governance levels x 20 seeds)
- **Config**: 10 agents (6 honest + 2 adversarial + 2 opportunistic), 20 epochs
- **Scenario**: `scenarios/hypotheses/topology_governance_interaction.yaml`

## Motivation

Every claim in the vault carries an implicit "tested in small-world only" boundary condition. The topology notes in `vault/topologies/` document [[small-world]], [[complete-graph]], [[random-graph]], and [[scale-free]] but none have been systematically tested with governance mechanisms. This is the largest unexplored design dimension — if governance effects are topology-dependent, the generalizability of the vault's 68 claims is fundamentally constrained.

## Expected claims

- **New**: Claim on topology x governance interaction (the central finding)
- **New**: Claim on scale-free governance amplification (if hub concentration increases enforcement efficacy)
- **New**: Claim on ring governance attenuation (if limited information flow weakens governance)
- **Update**: Multiple existing claims may need topology boundary conditions added (governance-cost-paradox, circuit-breakers-dominate, tax-welfare-tradeoff, etc.)

## Prerequisites

- SWARM must support `scale_free` (Barabasi-Albert), `random_graph` (Erdos-Renyi), and `ring` topologies
- Network metrics (clustering_coefficient, degree_distribution) must be recorded per epoch
- Governance mechanisms must work identically across topologies (no topology-specific code paths)

## Analysis plan

- Two-way ANOVA (topology x governance) on each metric, Bonferroni-corrected (k=5 metrics)
- Explicit interaction term test: F-test for topology x governance interaction
- If interaction is significant: simple effects analysis within each topology
- Network structure analysis: how do clustering, degree distribution, and component structure vary across topologies and interact with governance?

## Falsification

If governance effects are uniform across all topologies (no significant topology x governance interaction on any primary metric), the vault's small-world-based claims generalize and no boundary conditions need updating.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: topology, governance, interaction, generalizability, boundary-conditions -->
