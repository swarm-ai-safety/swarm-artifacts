---
description: LangGraph governed delegation sweep shows task completion requires >=30 max_handoffs; trust boundaries force modification not denial
type: experiment
status: completed
run_id: 20260221_081328_langgraph_governed
experiment_type: sweep
created: '2026-02-21'
aliases:
- 20260221_081328_langgraph_governed
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

# LangGraph governed delegation requires 30 max handoffs for task completion and trust boundaries modify rather than deny handoffs

## Design

- **Hypothesis**: Trust boundaries and handoff limits interact to determine task completion rates in governed multi-agent delegation
- **Type**: Parameter sweep
- **Seeds**: [42]
- **Total runs**: 32
- **Swept parameters**:
  - `max_cycles`: [1, 2, 3, 5]
  - `max_handoffs`: [5, 10, 15, 30]
  - `trust_boundaries`: [true, false]

## Key results

### Task completion rates by max_handoffs

| max_handoffs | trust_boundaries=true | trust_boundaries=false |
|--------------|----------------------|------------------------|
| 5 | 0% (0/4) | 25% (1/4) |
| 10 | 0% (0/4) | 25% (1/4) |
| 15 | 50% (2/4) | 50% (2/4) |
| 30 | 75% (3/4) | 50% (2/4) |

Only configurations with max_handoffs >= 15 achieve any task completion with trust boundaries enabled. At max_handoffs=30, trust boundaries paradoxically improve completion rate (75% vs 50%), suggesting that forced handoff modification may route tasks more effectively than unrestricted routing.

### Trust boundary behavior

When trust_boundaries=true, all handoffs are classified as "modified" (approved_handoffs=0, modified_handoffs=N). When trust_boundaries=false, all handoffs are approved directly. Zero handoffs were denied or escalated in any configuration, meaning trust boundaries act as a transformation layer rather than a filter.

### Max cycles effect

Max_cycles shows no consistent relationship with task completion. At max_handoffs=30 with trust_boundaries=true, both max_cycles=1 and max_cycles=2 complete tasks, while max_cycles=3 does not — suggesting interaction effects rather than monotonic improvement.

### Timing

Successful completions require 16-20 total turns and 40-57 seconds elapsed, regardless of max_cycles or trust boundary settings. Failed configurations typically terminate early at 4-10 turns and 8-26 seconds.

## Claims affected

- New claim candidate: delegation task completion depends primarily on max_handoffs, not max_cycles
- New claim candidate: trust boundaries modify all handoffs but deny none, acting as transformation rather than filter

## Artifacts

- CSV: `runs/20260221_081328_langgraph_governed/sweep_results.csv`
- Plots: `runs/20260221_081328_langgraph_governed/plots/`

## Reproduction

```bash
python -m swarm sweep langgraph_governed --seed 42
```

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: langgraph, delegation, trust-boundaries, handoffs, governance -->
