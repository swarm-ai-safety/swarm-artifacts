---
description: "Phase transition theory predicts convergence time peaks near 5-10% tax — measurable in existing SWARM data"
type: claim
status: active
confidence: low
domain: methodology
evidence:
  supporting:
  - run: research-mechanism-design-screening-2026-02-22
    metric: convergence_time
    detail: 'Statistical physics predicts critical slowing down near phase transitions; convergence time should peak at 5-10% tax if transition is genuine. Testable in SWARM by measuring round-by-round welfare convergence in existing run data'
    source_type: research
  weakening: []
  boundary_conditions:
  - Requires per-round welfare data from existing SWARM runs
  - Assumes sufficient rounds per run to measure convergence dynamics
supersedes: []
superseded_by: []
related_claims:
- claim-tax-phase-transition
- claim-tax-phase-transition-hysteresis-predicted-but-untested
- claim-welfare-plateaus-above-12pct-tax
- claim-optimal-tax-range-0-to-5pct
- claim-tax-welfare-direction-is-scenario-dependent
created: 2026-02-22
cssclasses:
- claim
- claim-low
tags:
- methodology
- phase-transition
- critical-phenomena
- convergence
graph-group: claim
---

# critical slowing down near 5-10% tax would confirm the tax phase transition is genuine

Statistical physics predicts that systems approaching a phase transition exhibit critical slowing down — the time required to reach equilibrium diverges near the critical point. If the [[claim-tax-phase-transition|SWARM tax phase transition at 5-10%]] is a genuine phase transition, convergence time should peak in this range and be measurable in existing SWARM data.

## Evidence summary

Critical slowing down is a universal signature of continuous phase transitions in statistical physics: near the critical point, the system's dominant relaxation time diverges, causing fluctuations to persist longer and equilibrium to be reached more slowly. This phenomenon has been observed in agent-based models, ecological systems, and financial markets approaching tipping points.

Applied to SWARM, the prediction is specific and testable: if welfare convergence time (measured as rounds to reach steady-state welfare) is plotted against tax rate, it should peak at or near the 5-10% transition band identified in [[claim-tax-phase-transition]]. Runs at 5% and 7.5% tax should converge more slowly than runs at 0% or 15%.

This test is particularly valuable because it can be performed on existing SWARM data without new experiments. The per-round welfare data in `history.json` files from the baseline governance sweeps contains the necessary time series.

If critical slowing down is confirmed, the companion prediction of [[claim-tax-phase-transition-hysteresis-predicted-but-untested|hysteresis at the tax phase transition]] becomes substantially more credible — both derive from the same physical theory but test different signatures. The [[claim-welfare-plateaus-above-12pct-tax|welfare plateau above 12.5%]] is consistent with the post-transition regime where critical slowing down should be absent: once the system has collapsed, convergence speeds up again. Critical slowing down would also validate the [[claim-optimal-tax-range-0-to-5pct|0-5% safe range]] from a physics perspective — the safe range corresponds to the pre-transition regime where the system is far from criticality. A key falsification test: [[claim-tax-welfare-direction-is-scenario-dependent|the kernel v4 scenario]] shows no phase transition (welfare monotonically increases with tax), so it should also show no critical slowing down — confirming that both signatures are genuine rather than measurement artifacts.

## Boundary conditions

- Requires per-round welfare data with sufficient temporal resolution
- SWARM runs may be too short (limited rounds) to observe convergence dynamics
- Critical slowing down is predicted for continuous (second-order) transitions; if the tax transition is first-order, the signature would be different (metastability rather than slowing)
- Agent-level stochasticity in LLM outputs may mask convergence dynamics

## Mechanism

Near a phase transition, the system's free energy landscape flattens — the barrier between the two phases (high-welfare and low-welfare states) becomes small, and the system fluctuates between them before committing to one. This manifests as slower convergence, increased variance, and autocorrelation in time series. In SWARM, this would appear as welfare oscillating between high and low values for more rounds before settling at tax rates near the critical point.

## Open questions

- Do existing SWARM runs have sufficient rounds to measure convergence dynamics?
- Is the tax transition continuous (predicting critical slowing down) or first-order (predicting metastability)?
- Can autocorrelation analysis of per-round welfare provide an independent estimate of the critical tax rate?
- Would this analysis work for the kernel v4 scenario where [[claim-tax-welfare-direction-is-scenario-dependent|tax effects reverse]]?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: methodology, phase-transition, critical-phenomena, convergence -->
