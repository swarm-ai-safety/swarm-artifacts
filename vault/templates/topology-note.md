---
description: One sentence on how this topology shapes agent behavior and outcomes (~150 chars)
type: topology
status: active | experimental
topology: ring | random | small-world | complete | scale-free | star | grid

properties:
  avg_degree: null
  clustering: null
  diameter: null
  dynamic: false

created: YYYY-MM-DD
updated: YYYY-MM-DD

_schema:
  required: [description, type, status, topology, created]
  optional: [properties, updated]
  enums:
    type: [topology]
    status: [active, experimental]
    topology: [ring, random, small-world, complete, scale-free, star, grid]
  constraints:
    description: "max 200 chars, no trailing period"
---

# prose-as-title describing the topology's behavioral signature

## Structure

Describe the topology: node connectivity, clustering, diameter,
information flow characteristics.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `k` | int | 4 | number of nearest neighbors (small-world) |
| `p` | float | 0.15 | rewiring probability (small-world) |

## Behavioral signature

How does agent behavior change under this topology?
What governance mechanisms are more/less effective here?

- Information flow: fast/slow, uniform/clustered
- Coalition formation: easy/hard
- Adversarial containment: effective/ineffective

## Evidence

- [[claim-id]] — topology-dependent claim
- [[experiment-run-id]] — key experiment in this topology

## Comparison with other topologies

What changes when you switch from this topology to another?
Which claims are topology-sensitive?

---

Topics:
- [[_index]]
