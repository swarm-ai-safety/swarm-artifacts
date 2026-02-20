---
description: Watts-Strogatz small-world network balancing local clustering with short path lengths
type: topology
status: active
topology: small-world
properties:
  avg_degree: 4
  clustering: 0.42
  diameter: 3
  dynamic: true
created: 2026-02-08
updated: 2026-02-18
aliases:
- small-world
cssclasses:
- topology
graph-group: topology
---

# small-world topology is the default testbed for SWARM governance experiments

## Structure

Watts-Strogatz small-world graph with `k=4` nearest neighbors and rewiring probability `p=0.15`. Combines high local clustering (agents form cliques) with short global path lengths (information crosses the network quickly).

With dynamic edges enabled, edge weights strengthen on successful interactions and decay otherwise, allowing coalition formation and dissolution.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `k` | int | 4 | number of nearest neighbors |
| `p` | float | 0.15 | rewiring probability |
| `dynamic` | bool | true | enable edge weight dynamics |
| `edge_strengthen_rate` | float | 0.12 | how fast successful edges grow |
| `edge_decay_rate` | float | 0.04 | how fast unused edges shrink |

## Behavioral signature

- **Information flow**: fast across the network but locally clustered — gossip spreads quickly, but cliques can form persistent subgroups.
- **Coalition formation**: relatively easy due to clustering. Adversarial agents can form stable collusion rings within their cluster.
- **Governance effectiveness**: circuit breakers are highly effective because freezing one node disrupts the local cluster. Reputation decay is moderately effective.

## Evidence

Most SWARM governance experiments use small-world as the default topology. Key findings:

- [[claim-circuit-breakers-dominate]] — established in small-world
- [[claim-smarter-agents-earn-less]] — RLM agents outperform honest only in small-world (d=2.14)
- [[claim-tax-welfare-tradeoff]] — tax sensitivity established in small-world

## Comparison with other topologies

- **Ring**: more constrained information flow, governance effects may differ — untested
- **Random**: less clustering, collusion harder to sustain — untested
- **Complete**: no topology effects, all agents interact with all — trivial case

Most claims carry a boundary condition: "tested in small-world only."

---

Topics:
- [[_index]]
