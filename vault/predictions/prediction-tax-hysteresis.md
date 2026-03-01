---
description: Raising tax through 5-10% and lowering back should NOT restore welfare — irreversible loss from agent withdrawal cascade
type: prediction
status: open
source_claim: "theory-tax-phase-transition"
hypothesis: "If tax is raised from 0% to 15% and then reduced back to 0% within a single simulation, welfare at 5% during ramp-down will be significantly lower than welfare at 5% during ramp-up (d>=0.5, Bonferroni-corrected)"
test_protocol: "Run tax ramp-up/ramp-down experiment: 0%→5%→10%→15%→10%→5%→0%, holding each level for 10 epochs. 30 seeds, baseline governance scenario, 8 agents, small-world topology. Compare welfare at matched tax rates between ascending and descending phases. Key metric: welfare difference at 5% ascending vs 5% descending. Statistical test: paired t-test with Bonferroni correction across 7 comparison points."
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

# Tax ramp-up through the 5-10% transition followed by ramp-down will show irreversible welfare loss

## Source

Derived from [[theory-tax-phase-transition]] and [[claim-tax-phase-transition-hysteresis-predicted-but-untested]]. Catastrophe theory applied to the empirically observed S-curve welfare response.

## Hypothesis

If transaction tax is raised from 0% through the 5-10% critical band to 15%, and then reduced back to 0%, welfare at each matched tax rate during the descending phase will be significantly lower than during the ascending phase. The effect should be strongest at 5% (near the transition) and negligible at 0% and 15% (far from the transition).

Expected magnitude: d≥0.5 at 5% tax between ascending and descending welfare, based on the d=1.18 effect size of the forward transition itself. Hysteresis effects in econophysics ABMs (Gualdi et al. 2015) typically show 20-40% welfare loss retention.

## Test protocol

- **Scenario:** Baseline governance, small-world topology (k=4, p=0.15), 8 agents
- **Tax schedule:** 0%→5%→10%→15%→10%→5%→0%, each level held for 10 epochs (70 epochs total)
- **Seeds:** 30 (minimum for reliable paired testing)
- **Key metric:** Mean welfare per epoch at each tax level, paired ascending vs descending
- **Statistical test:** Paired t-test at each of 3 matched tax levels (5%, 10%, 0%), Bonferroni-corrected (k=3)
- **Control:** Run a flat 0% tax for 70 epochs to establish natural welfare drift baseline

## Resolution

_Fill this section when the prediction is tested._

| Field | Value |
|-------|-------|
| Run | `` |
| Outcome | |
| Detail | |

## Implications

**If confirmed:** Validates the phase transition interpretation and makes governance cost paradox ([[claim-governance-cost-paradox]]) even more severe — temporary tax excursions above 5% cause permanent damage. Strongly constrains governance design to the 0-5% safe range ([[claim-optimal-tax-range-0-to-5pct]]).

**If refuted:** The S-curve is a smooth nonlinearity, not a genuine phase transition. Welfare response is reversible and governance parameter adjustment is safe. The econophysics analogy breaks down.

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, transaction-tax, phase-transition, hysteresis, prediction -->
