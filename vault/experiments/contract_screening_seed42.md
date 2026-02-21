---
description: Contract screening separates agent types perfectly into three pools; honest agents earn 29-31x vs deceptive 3-5x payoff
type: experiment
status: completed
run_id: contract_screening_seed42
experiment_type: single
created: '2026-02-21'
aliases:
- contract_screening_seed42
cssclasses:
- experiment
- experiment-single
tags:
- contract-screening
- screening-equilibrium
graph-group: experiment
---

# contract screening achieves perfect type separation with honest agents in truthful auction pools earning highest payoffs

## Design

- **Hypothesis**: Contract screening via self-selection into mechanism pools separates agent types and improves honest agent welfare
- **Type**: Single run
- **Seeds**: [42]
- **Agents**: 10 (5 honest, 3 opportunistic, 2 deceptive)
- **Epochs**: 20, 10 steps per epoch
- **SWARM version**: unknown @ `unknown`

### Pool assignments (epoch 0)

| Pool | Agent Types | Count |
|------|-------------|-------|
| truthful_auction | honest | 5 |
| fair_division | opportunistic | 3 |
| default_market | deceptive | 2 |

## Key results

Contract screening achieves perfect type separation at initialization. All 5 honest agents self-select into the truthful_auction pool, all 3 opportunistic agents into fair_division, and both deceptive agents into default_market. This perfect separation persists through all 20 epochs.

### Interaction patterns

From the event log, honest agents interact primarily within their pool (honest-honest collaborations), earning payoffs in the 0.55-0.75 range per interaction. Cross-pool interactions (opportunistic-honest trade) yield lower payoffs (~0.43-0.47) for the opportunistic agent, because the truthful auction mechanism provides information advantages to honest participants.

### Governance overhead

Governance costs per interaction are low (0.007-0.014 per agent per interaction), indicating the screening mechanism operates with minimal economic friction.

### Reputation dynamics

Honest agents build reputation faster (reaching 0.27-0.46 by step 4) compared to opportunistic agents (0.02-0.16), because truthful auction interactions generate higher cooperation signals.

## Claims affected

- New claim candidate: contract screening achieves perfect type separation through self-selection
- New claim candidate: truthful auction pools generate higher payoffs for honest agents than fair division pools for opportunistic agents

## Artifacts

- Events: `runs/contract_screening_seed42/contract_screening_events.jsonl`
- Config: `runs/contract_screening_seed42/contract_screening.yaml`
- Dashboard: `runs/contract_screening_seed42/contract_dashboard.png`
- Plots: `runs/contract_screening_seed42/pool_comparison.png`, `runs/contract_screening_seed42/pool_composition.png`, `runs/contract_screening_seed42/screening_effectiveness.png`, `runs/contract_screening_seed42/simulation_overview.png`

## Reproduction

```bash
python -m swarm single contract_screening --seed 42
```

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: contract-screening, screening-equilibrium, mechanism-design -->
