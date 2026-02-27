---
description: Multi-seed LangGraph governed sweep (128 runs) shows 55% completion rate with trust boundaries causing denials but not affecting completion
type: experiment
status: completed
run_id: 20260222_183539_langgraph_governed
experiment_type: sweep
created: '2026-02-27'
aliases:
- langgraph_governed_replication
cssclasses:
- experiment
- experiment-sweep
tags:
- langgraph
- delegation
- trust-boundaries
- handoffs
- replication
graph-group: experiment
---

# LangGraph governed replication shows trust boundaries increase denial rates but do not significantly affect task completion

## Design

- **Hypothesis**: Earlier finding that trust boundaries modify but never deny handoffs needs replication with more seeds
- **Type**: Parameter sweep (2 runs combined)
- **Run 1**: 20260222_183539_langgraph_governed — 96 runs (32 configs x 3 seeds)
- **Run 2**: 20260224_083213_langgraph_governed — 32 runs (32 configs x 1 seed)
- **Total**: 128 runs across 32 parameter configurations
- **Swept parameters**:
  - `max_cycles`: [1, 2, 3, 5]
  - `max_handoffs`: [5, 10, 15, 30]
  - `trust_boundaries`: [true, false]
- **Parent runs**: [[20260221_081328_langgraph_governed]], [[20260221_104316_langgraph_governed]]

## Key results

### Overall completion rate is modest

70/128 runs (54.7%) achieved task completion. This is strikingly lower than the 100% completion at max_handoffs>=30 found in the earlier single-seed runs, suggesting high variance in LLM-based delegation outcomes.

### Trust boundaries increase denials but not completion

| Setting | Completion | Mean denial rate |
|---------|-----------|-----------------|
| Trust=True | 56.2% (36/64) | 0.172 |
| Trust=False | 53.1% (34/64) | 0.008 |

Trust boundaries cause significantly higher denial rates (0.172 vs 0.008) but this does not translate into a meaningful completion difference (56.2% vs 53.1%, only 3pp). This partially weakens [[claim-trust-boundaries-modify-but-never-deny-handoffs]] — in the multi-seed replication, trust boundaries DO deny handoffs (denial_rate > 0), though the system-level impact on task completion is negligible.

### Handoff budget has no clear effect

| max_handoffs | Completion rate |
|-------------|----------------|
| 5 | 59.4% |
| 10 | 50.0% |
| 15 | 62.5% |
| 30 | 46.9% |

Contrary to [[claim-delegation-completion-requires-handoff-budget-above-15]], no monotonic relationship between handoff budget and completion exists in this replication. The pattern is essentially flat with high noise.

### Actual handoff utilization is very low

Mean actual handoffs across all runs is approximately 0.5, regardless of max_handoffs setting. Most runs either complete with 0 handoffs (coordinator handles alone) or fail regardless of handoff budget. This suggests the handoff mechanism is underutilized — the governance parameters being swept may not be the binding constraint on task completion.

## Claims affected

- **Weakens**: [[claim-trust-boundaries-modify-but-never-deny-handoffs]] — denials DO occur (mean denial_rate=0.172 with trust=True), but completion is unaffected
- **Weakens**: [[claim-delegation-completion-requires-handoff-budget-above-15]] — no handoff budget effect on completion in 128-run replication

## Artifacts

- CSV: `runs/20260222_183539_langgraph_governed/sweep_results.csv` (96 runs)
- CSV: `runs/20260224_083213_langgraph_governed/sweep_results.csv` (32 runs)

## Reproduction

```bash
python -m swarm sweep langgraph_governed --max-cycles 1,2,3,5 --max-handoffs 5,10,15,30 --trust-boundaries true,false --seeds 42-44
```

---

Topics:
- [[_index]]

<!-- topics: langgraph, delegation, trust-boundaries, handoffs, replication -->
