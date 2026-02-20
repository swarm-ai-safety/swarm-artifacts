---
description: "Erd\u0151s-R\xE9nyi random graph with uniform edge probability, providing a null model for topology-dependent governance effects"
type: topology
status: active
topology: random
properties:
  avg_degree: "p(n-1)"
  clustering: "p"
  diameter: "O(log n)"
  dynamic: false
parameters:
  n: 8
  p: 0.5
aliases:
- random-graph
- "erd\u0151s-r\xE9nyi"
- ER-graph
- G(n,p)
cssclasses:
- topology
graph-group: topology
tags:
- topology
- information-flow
- governance
- null-model
created: 2026-02-19
updated: 2026-02-19
---

# Random graph provides the null model for testing whether governance results depend on network structure or emerge from mechanism alone

## Structure

An Erdos-Renyi random graph G(n, p) where each possible edge between `n` agents exists independently with probability `p`. The resulting graph has no preferential structure — no clusters, no hubs, no spatial locality. The degree distribution is binomial, approximating Poisson for large n.

In SWARM terms: agent interaction partners are assigned randomly with no structural bias. This is the **null model** for network topology — any governance effect that persists in the random graph cannot be attributed to network structure.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `n` | int | 8 | number of agents |
| `p` | float | 0.5 | edge probability (controls density) |
| `dynamic` | bool | false | enable edge weight dynamics |
| `edge_strengthen_rate` | float | 0.12 | how fast successful edges grow |
| `edge_decay_rate` | float | 0.04 | how fast unused edges shrink |

The edge probability `p` controls the expected average degree: E[degree] = p(n-1). At p = 0.5 with n = 8, the expected degree is 3.5, comparable to the small-world default of k = 4. The critical threshold for connectivity is p = ln(n)/n; below this, the graph is likely disconnected.

## Behavioral signature

- **Information flow**: moderately fast with high variance across graph instances. Unlike small-world, there are no guaranteed clusters or shortcuts — some random instances are well-connected while others have bottlenecks.
- **Coalition formation**: harder than small-world because there is no clustering. Agents lack the stable local neighborhoods that facilitate trust-building and repeated interactions. Coalition attempts must cross random, uncorrelated edges.
- **Governance effectiveness**: governance results should show higher variance across random seeds (each seed produces a different graph). Mechanisms that depend on local structure (circuit breakers) are expected to be less consistently effective. Mechanisms that are topology-agnostic (transaction tax, quality gates) should perform similarly to small-world.

## Theoretical properties

| Property | Value |
|----------|-------|
| Degree distribution | Binomial(n-1, p), approx Poisson(p(n-1)) |
| Clustering coefficient | p (expected) |
| Average path length | O(log n / log(np)) |
| Diameter | O(log n) for p > ln(n)/n |
| Connectivity threshold | p = ln(n)/n |
| Edge count (expected) | p * n(n-1)/2 |

## Relevance to SWARM experiments

The random graph is the essential **control topology** for SWARM. If a governance result holds in both small-world and random graph, it is likely a property of the mechanism itself, not an artifact of network structure. If a result holds only in small-world, the clustering or short-path structure is a necessary condition.

Key predictions:

- **Collusion**: the low clustering (relative to small-world at equivalent density) should make sustained collusion harder. The collusion rings observed in [[failure-collusion-ring-mutual-boosting]] may fail to form because the 3-agent cliques that enable ring collusion are less common when C = p rather than C = 0.42.
- **Circuit breakers**: the dominance in [[claim-circuit-breakers-dominate]] should weaken because there are no stable clusters to disrupt. Freezing a random node removes a random subset of edges, which is less structurally impactful than disrupting a clustered neighborhood.
- **Tax welfare tradeoff**: the threshold in [[claim-tax-welfare-tradeoff]] should be relatively stable because transaction tax operates on individual transactions regardless of topology. The random graph tests this prediction.
- **Variance**: all governance metrics should show higher between-seed variance because the underlying graph structure varies. This may require more seeds to achieve Bonferroni significance.

## Comparison with small-world

| Property | Random (p=0.5) | Small-world (k=4, p=0.15) |
|----------|----------------|---------------------------|
| Avg degree | ~3.5 | 4 |
| Clustering | ~0.5 | ~0.42 |
| Diameter (n=8) | ~2 | ~3 |
| Degree variance | Moderate (binomial) | Low (near-regular) |
| Structure | None (random) | Clustered + shortcuts |
| Reproducibility | Low (varies per seed) | High (deterministic given k, p) |

At p = 0.5, the random graph has comparable density and even slightly higher clustering than small-world (k=4, p=0.15). The key difference is that small-world clustering is **structured** (formed by local neighborhoods) while random graph clustering is **incidental** (formed by chance). This distinction matters for governance mechanisms that exploit local structure.

For a sharper comparison, use p ~ 0.3 to match the small-world average degree of 4 with n = 8 agents (expected degree = 0.3 * 7 = 2.1), or adjust n upward. The choice of p should be calibrated to produce comparable density.

## Evidence from SWARM experiments

No SWARM runs have used random graph topology to date. The topology is listed in the `TOPOLOGY_TAGS` mapping in `enrich-tags.py` but no scenario files reference it. The [[small-world]] note identifies random graphs as an untested alternative where "less clustering [makes] collusion harder to sustain."

## Open questions

- Does the absence of clustering in random graphs actually suppress collusion, or do adversarial agents find alternative coordination strategies?
- How many additional seeds are needed to achieve Bonferroni significance on random graphs due to higher structural variance?
- Is G(n, p) the right null model for SWARM, or would a degree-matched random graph (configuration model) be more appropriate?
- At what edge probability `p` do random graph governance results converge with complete graph results?
- Can SWARM's dynamic edge mechanism transform a random graph into something resembling small-world over time, as agents reinforce productive edges?

---

Topics:
- [[_index]]

<!-- topics: topology, random-graph, null-model, information-flow, governance, network-structure -->
