---
description: Levies a percentage tax on transactions, redistributed to the commons or agents
type: governance
status: active
mechanism: transaction-tax
parameters:
- name: transaction_tax_rate
  type: float
  default: 0.05
  range: 0.0–0.20, higher = more redistribution
- name: transaction_tax_split
  type: float
  default: 0.5
  range: 0.0–1.0, fraction going to commons vs. agents
created: 2026-02-10
updated: 2026-02-18
aliases:
- transaction-tax
cssclasses:
- governance
graph-group: governance
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
- **With collusion penalty**: [[claim-tax-and-penalty-effects-are-orthogonal]] — tax and penalty effects are independent in marginal analysis. Tax dominates economics, penalty dominates toxicity. However, [[claim-tax-penalty-interaction-on-toxicity-uncharacterized]] suggests possible super-additive toxicity at extreme combinations.
- **Agent-type differential**: [[claim-tax-disproportionately-punishes-rlm-agents]] — tax reduces RLM agent payoff 2x more severely than honest agent payoff (d=6.02 vs d=2.87).
- **Toxicity side effect**: [[claim-high-tax-increases-toxicity]] — 10% tax increases toxicity by 0.6pp (d=-0.86), making tax a dual-cost mechanism.

## Agent-type sensitivity

- [[claim-tax-hurts-honest-more-than-opportunistic]] — honest agents lose more than opportunistic in absolute terms (d=0.80 vs d=0.43)
- [[claim-deceptive-payoff-weakly-declines-with-tax]] — deceptive agents lose the least (d=0.44, BH-sig only)
- Full spectrum: RLM > honest > opportunistic > deceptive in absolute tax sensitivity

## Welfare response curve

- [[claim-optimal-tax-range-0-to-5pct]] — safe range with negligible welfare impact
- [[claim-tax-phase-transition]] — steep decline 5-12.5%
- [[claim-welfare-plateaus-above-12pct-tax]] — floor reached above 12.5%

## CB interaction

- [[claim-tax-cb-interact-on-quality-gap]] — tax x CB interaction on quality gap (range=0.77) but not welfare
- [[claim-cb-null-may-reflect-design-limitation]] — CB null effect may be design artifact; recalibration is top priority

## Known failure modes

- Tax evasion via off-graph interactions is not modeled.
- At very high rates (>15%), transaction volume collapses, distorting all downstream metrics.

---

Topics:
- [[_index]]
