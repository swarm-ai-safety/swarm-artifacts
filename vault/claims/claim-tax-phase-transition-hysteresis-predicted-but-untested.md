---
description: "Catastrophe theory predicts irreversible welfare loss at the 5-10% tax transition — reducing tax may not restore welfare"
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: research-mechanism-design-screening-2026-02-22
    metric: hysteresis
    detail: 'Fold catastrophe model predicts hysteresis at phase transitions; Gualdi et al. (2015) observe first-order-like transitions with hysteresis in agent-based macro models. If SWARM tax transition is genuine, welfare loss at 5-10% may be irreversible upon tax reduction'
    source_type: research
  weakening: []
  boundary_conditions:
  - Requires SWARM experiment testing tax reduction after transition
  - Prediction assumes genuine phase transition rather than smooth nonlinearity
  - Gualdi et al. results are from agent-based macro models, not LLM agent markets
supersedes: []
superseded_by: []
related_claims:
- claim-tax-phase-transition
- claim-welfare-plateaus-above-12pct-tax
- claim-critical-slowing-down-would-confirm-tax-phase-transition
- claim-governance-cost-paradox
- claim-optimal-tax-range-0-to-5pct
created: 2026-02-22
cssclasses:
- claim
- claim-low
tags:
- governance
- transaction-tax
- phase-transition
- hysteresis
- catastrophe-theory
graph-group: claim
---

# catastrophe theory predicts hysteresis at the tax phase transition making welfare loss irreversible

If the [[claim-tax-phase-transition|welfare decline between 5-10% tax]] is a genuine phase transition rather than a smooth nonlinearity, catastrophe theory predicts that the transition should exhibit hysteresis — meaning that reducing the tax rate back below the transition point may not restore welfare to its pre-transition level.

## Evidence summary

Fold catastrophe models predict that first-order phase transitions exhibit hysteresis: the forward transition (increasing tax through the critical point) occurs at a different parameter value than the reverse transition (decreasing tax). Gualdi et al. (2015) observe precisely this pattern in agent-based macroeconomic models, where policy-induced transitions show irreversible welfare loss even after the policy is reversed.

Applied to SWARM's [[claim-tax-phase-transition|tax phase transition]], this predicts that raising the tax from 0% to 10% and then reducing it back to 0% would not restore welfare to its original level. The ecosystem contraction caused by the transition — agents withdrawing from participation, network connections atrophying — may persist even after the tax incentive is removed.

The [[claim-welfare-plateaus-above-12pct-tax|welfare plateau above 12.5% tax]] is consistent with this prediction: the flatness suggests the system has settled into a new basin of attraction from which it does not recover with marginal tax reduction.

Hysteresis would compound the [[claim-governance-cost-paradox|governance cost paradox]]: if welfare losses from taxation are irreversible, the cost-benefit calculus for transaction tax becomes asymmetrically negative. Even temporary tax increases above the critical point would permanently damage the ecosystem. This makes the [[claim-optimal-tax-range-0-to-5pct|0-5% safe operating range]] even more critical — exceeding it even briefly could cause permanent welfare loss if hysteresis is real. The companion prediction of [[claim-critical-slowing-down-would-confirm-tax-phase-transition|critical slowing down]] addresses a logically prior question: whether the transition is genuine at all. If critical slowing down is observed, the hysteresis prediction becomes substantially more credible.

## Boundary conditions

- Theoretical prediction only — no SWARM experiment has tested tax reduction after transition
- The prediction depends on the transition being genuinely first-order (discontinuous) rather than a steep but continuous curve
- Agent-based macro models (Gualdi et al.) differ substantially from SWARM's LLM agent markets
- SWARM's 8-agent, short-horizon experiments may not develop the persistent structural changes that produce hysteresis

## Mechanism

Hysteresis arises when a phase transition involves structural reorganization that is not easily reversed. In SWARM's context, the proposed mechanism is: high tax causes marginal interactions to become unprofitable, agents withdraw from participation, network connectivity decreases, and remaining agents adapt to the sparser environment. When tax is subsequently reduced, the adapted state persists because agents have no incentive to re-establish connections that were lost.

## Open questions

- What is the most efficient SWARM experiment to test hysteresis? (Ramp tax up through transition, then ramp down)
- Does the kernel v4 scenario, where [[claim-tax-welfare-direction-is-scenario-dependent|tax-welfare direction reverses]], also show hysteresis?
- How many rounds are needed for structural adaptation to produce measurable hysteresis?
- Would redistribution of tax revenue prevent hysteresis by maintaining participation incentives?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, transaction-tax, phase-transition, hysteresis, catastrophe-theory -->
