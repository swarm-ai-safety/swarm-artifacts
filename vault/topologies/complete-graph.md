---
description: Fully-connected graph where every agent interacts with every other, eliminating topology as an experimental variable
type: topology
status: active
topology: complete
properties:
  avg_degree: "n-1"
  clustering: 1.0
  diameter: 1
  dynamic: false
parameters:
  n: 8
aliases:
- complete-graph
- fully-connected
- clique
- complete
cssclasses:
- topology
graph-group: topology
tags:
- topology
- information-flow
- governance
created: 2026-02-19
updated: 2026-02-19
---

# Complete graph removes network structure as a variable exposing pure governance mechanism effects

## Structure

A complete graph (K_n) where every pair of agents shares a direct edge. With `n` agents, each node has degree `n-1`, the clustering coefficient is 1.0, and the diameter is 1. Every agent can interact with every other agent in a single hop. There are no bottlenecks, no privileged positions, and no structural asymmetries.

This is the **trivial topology** in SWARM: it eliminates network effects entirely, making it useful as a control condition to isolate governance mechanism behavior from topology-dependent dynamics.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `n` | int | 8 | number of agents |
| `dynamic` | bool | false | enable edge weight dynamics |
| `edge_strengthen_rate` | float | 0.12 | how fast successful edges grow |
| `edge_decay_rate` | float | 0.04 | how fast unused edges shrink |

Note: with dynamic edges enabled, the complete graph can evolve into an effectively sparser topology as unused edges decay. This creates an interesting experimental condition where topology emerges endogenously from agent behavior.

## Behavioral signature

- **Information flow**: instantaneous. Every agent observes every other agent directly. Gossip, reputation, and behavioral signals propagate in a single round.
- **Coalition formation**: maximally easy. Any subset of agents can form a coalition without needing to route through intermediaries. Collusion rings are trivial to establish.
- **Governance effectiveness**: collusion detection becomes critical because collusion is so easy to form. Circuit breakers lose their topological advantage (freezing one node does not partition the graph). Reputation decay is maximally effective because reputation updates reach all agents instantly.

## Theoretical properties

| Property | Value |
|----------|-------|
| Degree distribution | (n-1)-regular |
| Clustering coefficient | 1.0 |
| Average path length | 1 |
| Diameter | 1 |
| Edge connectivity | n-1 |
| Vertex connectivity | n-1 |
| Edge count | n(n-1)/2 |

## Relevance to SWARM experiments

The complete graph serves as the **upper bound on connectivity**. Any governance result that holds in the complete graph holds regardless of topology — the mechanism works even when agents have maximum interaction freedom.

Key predictions:

- **Circuit breakers**: the dominance established in [[claim-circuit-breakers-dominate]] is predicted to weaken. Freezing one node in K_n leaves K_{n-1}, which is still complete. The topological disruption that makes circuit breakers powerful in small-world vanishes here.
- **Collusion detection**: becomes essential. The ease of coalition formation means collusion rings form faster and with more members. The behavioral similarity detection tested in [[claim-collusion-wealth-destruction]] may need lower thresholds.
- **Tax sensitivity**: the welfare tradeoff in [[claim-tax-welfare-tradeoff]] may differ because agents have n-1 trading partners instead of 4, making the economy more resilient to per-transaction costs.
- **Staking**: the backfire effect in [[claim-staking-backfires]] may be amplified — adversarial agents can accumulate capital faster with more interaction partners.

## Comparison with small-world

| Property | Complete (K_8) | Small-world (k=4, p=0.15) |
|----------|---------------|---------------------------|
| Avg degree | 7 | 4 |
| Clustering | 1.0 | ~0.42 |
| Diameter | 1 | ~3 |
| Information speed | Instantaneous | Fast |
| Coalition stability | Very high | Moderate |
| Circuit breaker impact | Minimal (graph stays connected) | High (disrupts cluster) |

The complete graph is the opposite extreme from [[ring]]. Where the ring maximizes path length and minimizes connectivity, the complete graph minimizes path length and maximizes connectivity. [[small-world]] sits between these extremes, which is why it was chosen as the default SWARM testbed.

## Evidence from SWARM experiments

No SWARM runs have used complete graph topology to date. It is referenced in [[claim-collusion-penalty-destabilizes]] as an untested condition where penalty effects may differ because "collusion channels" are maximally available. The [[small-world]] note lists complete graph as the "trivial case" where topology effects vanish.

## Open questions

- Do governance mechanisms that dominate in small-world (circuit breakers) lose their edge in the complete graph?
- Does the complete graph represent a worst case for collusion containment — where adversarial agents can always find willing partners?
- How does dynamic edge decay interact with the complete graph? Does the endogenous topology that emerges resemble small-world?
- Is the complete graph too computationally expensive for large-n experiments, and if so, what is the practical ceiling?

---

Topics:
- [[_index]]

<!-- topics: topology, complete-graph, information-flow, governance, network-structure -->
