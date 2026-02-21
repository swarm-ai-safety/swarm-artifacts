---
description: Combined effect of high tax + high penalty on toxicity may be super-additive but interaction term is untested
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
  - run: 20260213-221500_collusion_tax_effect
    metric: toxicity_rate
    detail: "Raw data shows tax=0.1/penalty=2.0 cells have toxicity >0.35, above marginal predictions. Interaction term not formally tested"
  weakening: []
  boundary_conditions:
  - 4x4 factorial design provides data for interaction analysis but only marginal effects tested
  - 10 seeds per cell may be underpowered for interaction detection
sensitivity:
  topology: untested
  agent_count: untested
  governance_interaction: this IS the interaction question
supersedes: []
superseded_by: []
related_claims:
- claim-tax-and-penalty-effects-are-orthogonal
- claim-high-tax-increases-toxicity
- claim-collusion-penalty-destabilizes
created: 2026-02-20
updated: 2026-02-20
aliases:
- tax-penalty-interaction-on-toxicity-uncharacterized
cssclasses:
- claim
- claim-low
tags:
- governance
- transaction-tax
- collusion
- interaction
- open-question
graph-group: claim
---

# tax and penalty interaction effect on toxicity is uncharacterized

## Evidence summary

The [[20260213-221500_collusion_tax_effect]] sweep varies tax rate and penalty multiplier simultaneously in a 4x4 factorial design (160 runs). The analysis reports only marginal effects — tax on economics, penalty on toxicity — but the raw data (sweep_results.csv) contains the full 16-cell grid needed for interaction analysis.

Inspection of the extreme cell (tax=0.1, penalty=2.0) shows mean toxicity >0.35, which is higher than either marginal prediction alone would suggest. If the interaction is super-additive, governance configurations combining high tax and high penalty would be worse than either alone — a critical finding for governance design.

## Open questions

- Run 2-way ANOVA with interaction term on the existing data to test formally
- If super-additive, is the mechanism resource scarcity (from tax) amplifying behavioral distortion (from penalty)?
- Does the interaction extend to welfare, or is it toxicity-specific?
- What is the minimum sample size needed to detect the interaction at 80% power?

---

Topics:
- [[_index]]

<!-- topics: governance, transaction-tax, collusion, interaction, open-question -->
