---
description: Cycle graph where each agent connects only to immediate neighbors, maximizing path length and isolating local
  clusters
type: topology
status: active
topology: ring
properties:
  avg_degree: 2
  clustering: 0.0
  diameter: n/2
  dynamic: false
parameters:
  n: 8
aliases:
- ring
- cycle
- circular
cssclasses:
- topology
graph-group: topology
tags:
- topology
- information-flow
- governance
- ring
- network-structure
created: 2026-02-19
updated: 2026-02-19
---

# Ring topology constrains information flow to nearest neighbors creating natural governance bottlenecks

## Structure

A ring (cycle) graph where each of `n` agents is connected to exactly two neighbors — one on each side. Information must traverse the ring sequentially: an agent at position 0 reaching position `n/2` requires `n/2` hops. There is no clustering (C = 0) and no shortcuts. The graph is 2-regular, meaning every node has identical degree.

With dynamic edges disabled (default), the ring is static. If dynamic edges are enabled, edge weight changes can effectively partition the ring into disconnected arcs when decay outpaces strengthening.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `n` | int | 8 | number of agents (ring size) |
| `dynamic` | bool | false | enable edge weight dynamics |
| `edge_strengthen_rate` | float | 0.12 | how fast successful edges grow |
| `edge_decay_rate` | float | 0.04 | how fast unused edges shrink |

## Behavioral signature

- **Information flow**: extremely slow. A signal originating at one node reaches the antipodal node only after `n/2` rounds of forwarding. This is the slowest-propagating topology in the SWARM repertoire.
- **Coalition formation**: difficult globally, trivial locally. Two adjacent agents can collude easily, but coordinating a ring-wide coalition requires passing messages through every intermediate node — any honest agent in the chain breaks it.
- **Governance effectiveness**: circuit breakers become disproportionately powerful. Freezing a single node partitions the ring into two disconnected arcs, completely severing communication. Reputation decay is less effective because reputation signals propagate slowly.

## Theoretical properties

| Property | Value |
|----------|-------|
| Degree distribution | 2-regular (every node has degree 2) |
| Clustering coefficient | 0 |
| Average path length | n/4 |
| Diameter | floor(n/2) |
| Edge connectivity | 2 (removing 2 edges disconnects the graph) |
| Vertex connectivity | 2 |

## Relevance to SWARM experiments

Ring topology represents the **minimal connectivity** extreme. Governance mechanisms that depend on information propagation (reputation decay, collusion detection via behavioral similarity) are expected to be weakest here. Mechanisms that act locally (circuit breakers, quality gates) should retain effectiveness or even gain power due to the bottleneck structure.

Key predictions:

- **Transaction tax**: the 5% welfare threshold identified in [[claim-tax-welfare-tradeoff]] may shift upward because constrained information flow already suppresses transaction volume.
- **Circuit breakers**: freezing one agent on a ring fully partitions the network. The dominance of circuit breakers found in [[claim-circuit-breakers-dominate]] should be even more pronounced.
- **Collusion penalties**: the destabilization observed in [[claim-collusion-penalty-destabilizes]] may be amplified — penalties on a ring can cascade through sequential neighbors more predictably.
- **Phase transitions**: the tax phase transition in [[claim-tax-phase-transition]] may shift because the ring's low connectivity means agents have fewer trading partners to begin with.

## Comparison with small-world

| Property | Ring | Small-world (k=4, p=0.15) |
|----------|------|---------------------------|
| Avg degree | 2 | 4 |
| Clustering | 0 | ~0.42 |
| Diameter (n=8) | 4 | ~3 |
| Information speed | Very slow | Fast |
| Coalition stability | Low (local only) | Moderate (cluster-based) |
| Circuit breaker impact | Extreme (partitions graph) | High (disrupts cluster) |

The ring removes the two defining features of [[small-world]]: clustering and short path lengths. It is the natural control topology for isolating whether SWARM governance results depend on these properties.

## Evidence from SWARM experiments

No SWARM runs have used ring topology to date. All existing claims carry the boundary condition "tested in small-world only" (see sensitivity sections of [[claim-circuit-breakers-dominate]], [[claim-tax-welfare-tradeoff]], [[claim-staking-backfires]]). The ring is referenced as an untested alternative in [[claim-governance-cost-paradox]] and [[claim-tax-welfare-tradeoff]].

## Open questions

- Does the 5% tax threshold shift in ring topology where information flow is constrained?
- Can adversarial agents exploit the sequential structure to create information bottlenecks (controlling the only path between two subgroups)?
- How does reputation decay perform when reputation updates must propagate hop-by-hop?
- Is the ring too disconnected for meaningful multi-agent governance experiments, or does the bottleneck structure reveal failure modes invisible in richer topologies?

---

Topics:
- [[_index]]

<!-- topics: topology, ring, information-flow, governance, network-structure -->
