---
description: Second LangGraph governed delegation sweep with identical parameter grid, 3 seeds
type: experiment
status: completed
run_id: 20260221_104316_langgraph_governed
experiment_type: sweep
created: '2026-02-21'
aliases:
- 20260221_104316_langgraph_governed
cssclasses:
- experiment
- experiment-sweep
tags:
- langgraph
- delegation
- trust-boundaries
- handoffs
graph-group: experiment
---

# second LangGraph governed delegation sweep replicates trust boundary modification pattern with additional seeds

## Design

- **Hypothesis**: Replication of [[20260221_081328_langgraph_governed]] delegation findings with additional seeds
- **Type**: Parameter sweep
- **Seeds**: [42, 43, 44]
- **Swept parameters**:
  - `max_cycles`: [1, 2, 3, 5]
  - `max_handoffs`: [5, 10, 15, 30]
  - `trust_boundaries`: [true, false]

## Key results

Sweep results CSV shows the same patterns as the first langgraph governed sweep: trust boundaries modify 100% of handoffs but deny none, and task completion requires max_handoffs >= 30. The additional seeds (43, 44) replicate the seed-42 findings from the first sweep.

## Claims supported

- [[claim-trust-boundaries-modify-but-never-deny-handoffs]]
- [[claim-delegation-completion-requires-handoff-budget-above-15]]

## Source

- `runs/20260221_104316_langgraph_governed/sweep_results.csv`

<!-- topics: langgraph, delegation, trust-boundaries, handoffs -->
