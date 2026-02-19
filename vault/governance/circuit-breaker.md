---
description: "Freezes agents exceeding toxicity or violation thresholds, the single most effective governance lever"
type: governance
status: active
mechanism: circuit-breaker

parameters:
  - name: freeze_threshold_toxicity
    type: float
    default: 0.6
    range: "0.0–1.0, lower = more aggressive"
  - name: freeze_threshold_violations
    type: int
    default: 3
    range: "1–10, lower = more aggressive"
  - name: freeze_duration_epochs
    type: int
    default: 3
    range: "1–10, longer = harsher"

created: 2026-02-11
updated: 2026-02-18
---

# circuit breakers alone outperform full governance stacks

## How it works

When an agent's toxicity score exceeds `freeze_threshold_toxicity` or their violation count exceeds `freeze_threshold_violations`, the circuit breaker freezes them for `freeze_duration_epochs`. During the freeze, the agent cannot initiate interactions, post, or vote — but they also stop accumulating penalties.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `freeze_threshold_toxicity` | float | 0.6 | toxicity score that triggers freeze |
| `freeze_threshold_violations` | int | 3 | violation count that triggers freeze |
| `freeze_duration_epochs` | int | 3 | how long the freeze lasts |

## Evidence

The kernel market governance comparison (70 runs, 7 regimes) established that circuit breakers alone produce +81% welfare and -11% toxicity vs. no governance, with effect size d=1.64 surviving Bonferroni correction.

- [[claim-circuit-breakers-dominate]] — the primary claim
- [[20260211-000149_kernel_market_governance_comparison]] — the definitive experiment

The freeze duration sweep (Feb 8) explored the `freeze_duration_epochs` parameter space, confirming that 3 epochs is near-optimal.

## Interactions

- **With transaction tax**: tax partially compensates at high rates, but circuit breaker alone outperforms the combination at low tax rates. See [[claim-tax-welfare-tradeoff]].
- **With staking**: staking *undermines* circuit breaker effectiveness because honest agents can't afford the stake. See [[claim-staking-backfires]].
- **With audits**: audits add marginal detection power but don't improve outcomes when circuit breaker is already active.

## Known failure modes

- **Threshold dancing**: adversaries learning to stay just below `freeze_threshold_toxicity`. Untested — this is the primary open question.
- **Freeze arbitrage**: in dynamic networks, frozen agents lose edges and may be permanently disadvantaged even after unfreezing.

---

Topics:
- [[_index]]
