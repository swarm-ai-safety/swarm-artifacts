---
description: "Levies a percentage tax on transactions, redistributed to the commons or agents"
type: governance
status: active
mechanism: transaction-tax

parameters:
  - name: transaction_tax_rate
    type: float
    default: 0.05
    range: "0.0–0.20, higher = more redistribution"
  - name: transaction_tax_split
    type: float
    default: 0.5
    range: "0.0–1.0, fraction going to commons vs. agents"

created: 2026-02-10
updated: 2026-02-18
---

# transaction tax above 5% significantly reduces welfare with large effect size

## How it works

Every accepted interaction incurs a tax of `transaction_tax_rate` on the payoff. The tax revenue is split between a commons pool and redistribution to agents based on `transaction_tax_split`.

## Parameters

| Parameter | Type | Default | Effect |
|-----------|------|---------|--------|
| `transaction_tax_rate` | float | 0.05 | percentage taxed per transaction |
| `transaction_tax_split` | float | 0.5 | fraction to commons (rest redistributed) |

## Evidence

The baseline governance v2 sweep (700 runs, 50 seeds, 7 tax levels) showed that tax rates above 0.05 significantly reduce welfare (d=1.18, p<1e-14, Bonferroni-corrected). The phase transition is around 5% — below this, the effect is negligible.

- [[claim-tax-welfare-tradeoff]] — the primary claim
- [[20260213-202050_baseline_governance_v2]] — the definitive sweep

## Interactions

- **With circuit breaker**: circuit breakers partially compensate for welfare loss at high tax rates. Enabling CB at tax >= 0.075 recovers some welfare.
- **With staking**: compound negative effect — both extract resources from honest agents.

## Known failure modes

- Tax evasion via off-graph interactions is not modeled.
- At very high rates (>15%), transaction volume collapses, distorting all downstream metrics.

---

Topics:
- [[_index]]
