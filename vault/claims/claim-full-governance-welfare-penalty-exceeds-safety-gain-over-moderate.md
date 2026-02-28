---
description: Full governance reduces baseline welfare 20% vs moderate but provides no better regime protection up to 50% adversarial fraction
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260227_203024_composition_boundary_study
    metric: welfare
    detail: "Full governance welfare at 0% adversarial: 12.06 vs moderate 15.04 vs none 15.96. Full imposes 20% welfare penalty relative to moderate at baseline. At 50% adversarial: full 5.02 vs moderate 7.52 — still 33% lower welfare. 20 runs per cell (5 seeds x 4 pop sizes)"
  - run: 20260227_203024_composition_boundary_study
    metric: regime
    detail: "Full governance regime: cooperative through 37.5% (0-5% collapse), contested at 50% (5% collapse). Moderate governance: cooperative through 37.5% (5% collapse at 37.5%), cooperative at 50% (5% collapse). Regime protection is equivalent — full offers no improvement. 20 runs per cell"
  - run: 20260227_203024_composition_boundary_study
    metric: toxicity
    detail: "Full governance toxicity at 0% adv: 0.288 vs moderate 0.251 vs none 0.248. Full governance produces HIGHER baseline toxicity than moderate or none. At 50% adv: full 0.319 vs moderate 0.311 vs none 0.425 — moderate matches full toxicity suppression"
  weakening: []
  boundary_conditions:
  - "Composition boundary study only; full governance may provide superior redteam resilience (see related claims)"
  - "Binary honest/adversarial mixtures; mixed archetypes untested in the adversarial sweep"
  - "Full governance config: 12% tax, CB, audit(p=0.15, 2.5x), staking(min=5, slash=15%), collusion detection"
sensitivity:
  topology: untested
  agent_count: tested at 4-32 agents
  governance_interaction: "Incremental mechanisms in full stack: staking (min_stake=5, slash=15%), collusion detection, higher tax (12% vs 8%), more aggressive audit (p=0.15 vs 0.10, 2.5x vs 2.0x penalty)"
supersedes: []
superseded_by: []
related_claims:
- claim: claim-governance-cost-paradox
  relation: supports
- claim: claim-moderate-governance-extends-cooperative-regime-to-50pct-adversarial
  relation: supports
- claim: claim-full-governance-stack-prevents-most-attack-types
  relation: refines
- claim: claim-tax-welfare-tradeoff
  relation: supports
- claim: claim-staking-backfires
  relation: supports
created: 2026-02-28
aliases:
- full-governance-welfare-penalty-exceeds-safety-gain-over-moderate
cssclasses:
- claim
- claim-medium
tags:
- governance
- welfare
- cost-benefit
- composition
graph-group: claim
---

# Full governance welfare penalty exceeds its safety gain over moderate governance

## Evidence summary

The composition boundary study ([[20260227_203024_composition_boundary_study]]) provides the first controlled comparison of none, basic, moderate, and full governance stacks across a systematic adversarial fraction sweep (720 runs).

**Welfare cost of full governance.** At 0% adversarial (pure honest population), full governance produces mean welfare of 12.06 versus moderate's 15.04 — a 20% penalty. This penalty persists at every adversarial fraction tested: at 50% adversarial, full achieves welfare 5.02 vs moderate 7.52 (33% lower). The welfare-vs-adversarial plot shows full governance consistently running below moderate across the entire adversarial spectrum.

**Regime protection equivalence.** Despite this welfare cost, full governance provides no additional regime protection over moderate. Both maintain cooperative regime through 37.5% adversarial with marginal collapse rates (0-5%). Both show contested regime at 50% with 5% collapse. The regime heatmap shows identical color patterns for moderate and full columns.

**Toxicity paradox.** Full governance actually produces HIGHER baseline toxicity (0.288 at 0% adv) than moderate (0.251) or none (0.248). This is consistent with [[claim-high-tax-increases-toxicity]] — the 12% tax rate in full governance exceeds the safe operating range. At high adversarial fractions, moderate matches full on toxicity suppression (0.311 vs 0.319 at 50% adversarial).

This directly extends the [[claim-governance-cost-paradox|governance cost paradox]]: not only does full governance cost more welfare than it saves, it costs more welfare than a cheaper alternative (moderate) while providing identical safety benefits. The result also supports [[claim-staking-backfires]], since full governance is the only config with staking enabled.

**Confidence: medium.** Single study, 20 runs per cell. The welfare differences are consistent across all adversarial fractions but formal effect sizes not computed for governance pairwise comparisons. Replication in different scenarios needed.

## Mechanism

The full governance stack adds three incremental mechanisms over moderate: higher tax (12% vs 8%), staking requirements (min_stake=5), and collusion detection. Each imposes costs: the additional 4% tax directly reduces welfare per the established tax-welfare relationship; staking requirements create a participation barrier that may exclude agents who would otherwise cooperate (consistent with claim-staking-backfires); collusion detection adds false-positive behavioral penalties. These costs compound, but their incremental safety benefit is null because moderate governance's audit mechanism already achieves sufficient deterrence against the adversarial strategies tested.

## Open questions

- Would full governance show advantage at adversarial fractions above 50%?
- Does collusion detection provide value specifically against coordinated (multi-adversarial) attacks not tested in binary mixtures?
- Would reducing full governance tax to match moderate (8%) while keeping staking+collusion recover the welfare gap?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, welfare, cost-benefit, composition -->
