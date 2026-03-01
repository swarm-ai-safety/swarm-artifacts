---
description: Convergence time to steady-state welfare should peak in the 5-10% tax band if the phase transition is genuine
type: prediction
status: open
source_claim: "theory-tax-phase-transition"
hypothesis: "If per-round welfare is recorded at each tax level (0%, 2.5%, 5%, 7.5%, 10%, 12.5%, 15%), convergence time (rounds to reach ±5% of final welfare) will peak at 5-7.5% tax, 2-5x longer than at 0% or 15%"
test_protocol: "Run single-run baseline governance at 7 tax rates with per-round welfare logging. 30 seeds per rate, 8 agents, small-world topology, 50 epochs minimum. Measure convergence time as epochs to reach ±5% of terminal welfare. Also measure autocorrelation at lag 1 of per-epoch welfare. Both should peak at 5-7.5%."

resolution:
  run: ""
  outcome: ""
  detail: ""

created: 2026-02-28

_schema:
  required: [description, type, status, source_claim, hypothesis, created]
  optional: [test_protocol, resolution, updated]
  enums:
    type: [prediction]
    status: [open, confirmed, refuted, expired]
    outcome: [confirmed, refuted, inconclusive]
  constraints:
    description: "max 200 chars, no trailing period"
    hypothesis: "must be a precise if-then statement"
    source_claim: "must reference a valid claim or theory ID"
---

# Welfare convergence time peaks near 5-10% tax confirming genuine phase transition dynamics

## Source

Derived from [[theory-tax-phase-transition]] and [[claim-critical-slowing-down-would-confirm-tax-phase-transition]]. Critical slowing down is the universal signature of approaching a phase transition in statistical physics.

## Hypothesis

If the welfare decline between 5-10% tax is a genuine phase transition, the time to reach steady-state welfare should peak in this band. Systems near critical points exhibit diverging relaxation times — the "critical slowing down" phenomenon. Concretely:

- At 0% and 15% tax: fast convergence (system far from critical point)
- At 5-7.5% tax: convergence time 2-5x longer (near critical point)
- Autocorrelation of per-epoch welfare at lag 1 should also peak at 5-7.5%

## Test protocol

- **Scenario:** Baseline governance, small-world topology (k=4, p=0.15), 8 agents
- **Tax rates:** 0%, 2.5%, 5%, 7.5%, 10%, 12.5%, 15% (7 levels)
- **Seeds:** 30 per tax rate (210 total runs)
- **Epochs:** 50 minimum per run (sufficient for convergence measurement)
- **Data requirement:** Per-epoch welfare time series (requires single-run harness, not sweep runner)
- **Key metrics:**
  1. Convergence time: epochs until welfare stays within ±5% of final-10-epoch mean
  2. Autocorrelation at lag 1 of per-epoch welfare
  3. Variance of per-epoch welfare in the final 20 epochs
- **Statistical test:** One-way ANOVA across 7 tax levels for each metric, with Bonferroni-corrected pairwise comparisons
- **Negative control:** Kernel v4 scenario at same tax rates — should show NO convergence time peak (no phase transition)

## Resolution

_Fill this section when the prediction is tested._

| Field | Value |
|-------|-------|
| Run | `` |
| Outcome | |
| Detail | |

## Implications

**If confirmed:** Strongest evidence that the tax welfare response is a genuine phase transition, not a smooth curve. Validates the econophysics analogy (Khashanah & Simaan 2022). Makes the [[prediction-tax-hysteresis]] prediction substantially more credible. Establishes SWARM as a platform for studying critical phenomena in multi-agent economies.

**If refuted:** Convergence time is flat across tax rates, meaning the S-curve is a smooth nonlinearity. The system reaches equilibrium equally fast everywhere, which is inconsistent with critical dynamics. The phase transition label should be downgraded to "steep nonlinearity."

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: methodology, phase-transition, critical-phenomena, convergence, prediction -->
