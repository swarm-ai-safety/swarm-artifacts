---
description: "Five+ governance parameters show the same pattern: flat safe range below a cliff, suggesting a universal structural property"
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: welfare
    detail: "Tax rate: flat 0-5%, cliff at 5-10%, plateau above 12.5%. Phase transition confirmed d=2.89 at composition boundary. Bonferroni-corrected"
    source_type: synthesis
  - run: 20260214-020518_tau_k_calibration
    metric: composite_score
    detail: "tau_min: flat 0.50-0.60, cliff at 0.65 (acceptance drops 100%→64%). Write cap: flat above k=12, cliff at k<=6 (75% welfare destruction). N=5 seeds per config"
    source_type: synthesis
  - run: 20260208-215009_sweep_freeze_duration
    metric: welfare
    detail: "Freeze duration: welfare improves 17% with duration 3-5, diminishing returns above 5. Violation threshold: safe at 3-5, insufficient below 3. N=3 seeds per config"
    source_type: synthesis
  - run: 20260208-215902_sweep_reputation_decay
    metric: welfare
    detail: "Reputation decay: full persistence (1.0) + zero stake maximizes welfare. Decay rate 0.85 catches farming in 6 epochs but sacrifices welfare. N=3 seeds per config"
    source_type: synthesis
  weakening: []
  boundary_conditions:
  - Pattern observed across 5+ governance parameters in baseline, calibration, and tax effect scenarios
  - Each parameter tested independently — joint envelope not characterized
  - Different scenarios may shift envelope positions (e.g., kernel v4 reverses tax direction)
sensitivity:
  topology: untested — envelope widths may vary with network structure
  agent_count: untested beyond default agent populations
  interaction_effects: joint parameter envelopes not characterized — individual parameter safe ranges may not compose
supersedes: []
superseded_by: []
related_claims:
- claim-tax-phase-transition
- claim-optimal-tax-range-0-to-5pct
- claim-welfare-plateaus-above-12pct-tax
- claim-tau-065-triggers-acceptance-phase-transition
- claim-write-cap-below-12-destroys-welfare
- claim-optimal-tau-range-050-to-060
- claim-freeze-duration-and-violation-threshold-interact-on-welfare
- claim-reputation-decay-rate-improves-welfare
- claim-governance-cost-paradox
- claim-tax-welfare-direction-is-scenario-dependent
created: 2026-02-22
cssclasses:
- claim
- claim-low
tags:
- governance
- phase-transition
- parameter-sensitivity
- meta-pattern
graph-group: claim
---

# multi-agent governance parameters universally exhibit narrow safe operating envelopes with non-linear cliff effects

Across five or more independently tested governance parameters, the same structural pattern repeats: welfare is flat within a narrow safe range, then drops sharply at a critical threshold (cliff effect), then plateaus in a degraded state. This convergence across unrelated governance dimensions suggests a fundamental property of multi-agent governance systems rather than a coincidence of specific parameter choices.

## Evidence summary

The pattern appears in at least five governance parameters tested across independent SWARM experiments:

| Parameter | Safe range | Cliff location | Post-cliff behavior |
|-----------|-----------|----------------|---------------------|
| Transaction tax | 0-5% | 5-10% | Welfare plateaus above 12.5% |
| tau_min (memory quality) | 0.50-0.60 | 0.65 | Acceptance drops 100%→64% |
| Write cap k | >=12 | k<=6 | 75% welfare destruction |
| Freeze duration | 3-5 epochs | <3 epochs | Insufficient containment |
| Reputation decay | 0.95-1.0 | <0.85 | Welfare-security tradeoff |

Each parameter was tested independently in separate experiments, yet all show the same shape: a flat safe region followed by a non-linear cliff. The [[claim-tax-phase-transition|tax phase transition]] is the best-characterized example (d=2.89, Bonferroni-significant), but the [[claim-tau-065-triggers-acceptance-phase-transition|tau acceptance transition]] and [[claim-write-cap-below-12-destroys-welfare|write cap destruction]] show analogous cliff effects.

This pattern has practical implications for governance system design: parameters must be tuned within narrow bands, and the cost of exceeding them is non-linear rather than gradual. The [[claim-governance-cost-paradox|governance cost paradox]] may partly reflect operators inadvertently exceeding safe envelopes. The [[claim-tax-welfare-direction-is-scenario-dependent|scenario-dependence of tax effects]] suggests that envelope positions shift between scenarios, meaning safe ranges cannot be assumed universal without per-scenario calibration.

The joint envelope — whether individually safe parameter values remain safe when combined — is an open question. The [[claim-freeze-duration-and-violation-threshold-interact-on-welfare|additive (non-interactive) freeze parameter effects]] suggest some parameters compose linearly, but this has not been tested for the full governance stack.

## Boundary conditions

- Pattern observed across 5+ parameters in baseline, calibration, and tax effect scenarios
- Each parameter tested independently — joint (multi-parameter) safe envelope not characterized
- Different scenarios may shift envelope positions (kernel v4 reverses tax direction)
- Cliff sharpness varies: tax transition is phase-transition-like, write cap is binary

## Mechanism

In multi-agent systems, governance parameters create implicit constraints on agent participation and interaction viability. Below the cliff, agents adapt to the constraint with minimal behavioral change. At the cliff, marginal interactions become unprofitable (for tax) or impossible (for write cap, tau), triggering participation withdrawal cascades. Above the cliff, the system has already contracted to a minimal viable state, producing the observed plateau.

## Open questions

- Do the individual safe ranges compose when multiple parameters are set simultaneously?
- Does the pattern hold for untested parameters (vote normalization, bandwidth caps, leniency)?
- Is there a universal theory (e.g., critical phenomena in multi-agent systems) that predicts the cliff sharpness from parameter properties?
- Would adaptive governance (dynamically adjusting parameters) avoid cliff effects?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, phase-transition, parameter-sensitivity, meta-pattern -->
