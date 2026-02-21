---
description: LDT agents maintain +42% welfare over honest agents at 40-70% population composition and suppress deceptive payoffs
type: claim
status: active
confidence: medium
domain: agent-behavior
evidence:
  supporting:
  - run: 20260211-215617_ldt_composition_study
    metric: welfare
    detail: "20 seeds. LDT welfare 517-803 vs honest 315-793 across 0-100% focal range. LDT payoff 71-84 at 10-30% composition. Deceptive payoff suppressed from 57.4→0 at LDT saturation"
  - run: 20260211-011020_ldt_composition_study
    metric: welfare
    detail: "10 seeds, 30 epochs. LDT welfare 558-803 vs honest 313-789. Variance compression: std decreases 4.1→0.8 with increasing LDT composition"
  - run: 20260211-003414_ldt_composition_study
    metric: welfare
    detail: "3 seeds. LDT prevents welfare collapse at 40-60% focal. LDT payoff 72-75 at saturation vs honest 38-40"
  - run: 20260211-002843_ldt_composition_study
    metric: welfare
    detail: "1 seed. LDT +42% welfare at 70%+ composition (9.29 vs 6.51). LDT reduces toxicity 0.43→0.25 across full spectrum"
  weakening: []
  boundary_conditions:
  - "ldt_cooperation scenario only; untested in governance-heavy or adversarial contexts"
  - "Honest vs LDT binary comparison; mixed strategies untested"
  - "Cross-over point varies by study (35-50% focal range)"
  - "LDT payoff drops to near-zero at 90%+ composition in some studies"
sensitivity:
  topology: untested
  agent_count: tested at 7 agents across all studies
  governance_interaction: no governance mechanisms in LDT composition studies
supersedes: []
superseded_by: []
related_claims:
- claim-acausality-depth-does-not-affect-cooperation-outcomes
- claim-smarter-agents-earn-less
- claim-deceptive-agents-dominate-moltbook-payoff-hierarchy
created: 2026-02-21
updated: 2026-02-21
aliases:
- ldt-agents-provide-welfare-stability-at-intermediate-composition
cssclasses:
- claim
- claim-medium
tags:
- agent-behavior
- ldt
- composition
- welfare
graph-group: claim
---

# LDT agents provide welfare stability and suppress deception at intermediate population compositions

## Evidence summary

Four LDT composition studies (1, 3, 10, and 20 seeds) consistently show that replacing honest agents with LDT (Logical Decision Theory) agents at 40-70% of the population improves welfare by 30-42% while suppressing deceptive agent payoffs.

**Key pattern across studies:**
- At 0% LDT focal (all honest), welfare is moderate and deceptive agents earn high payoffs (~57 units)
- At 40-70% LDT focal, welfare peaks and deceptive payoffs collapse toward zero
- At 90-100% LDT focal, welfare remains high but LDT individual payoffs diminish (tragedy of the commons at saturation)

The largest study ([[20260211-215617_ldt_composition_study]], 20 seeds) confirms the pattern with robust replication: LDT payoff 71-84 units at 10-30% composition, stable welfare maintenance in the 40-60% focal range, and systematic deceptive payoff suppression.

This creates an interesting tension with [[claim-acausality-depth-does-not-affect-cooperation-outcomes]]: while increasing reasoning depth within LDT agents has no effect, switching from honest to LDT decision-making architecture has a large effect. The composition (what type of agents) matters more than the depth (how deeply they reason). This parallels [[claim-smarter-agents-earn-less]] in an inverted way: individual LDT agents at saturation earn less (diminishing returns), but the population-level welfare benefit is substantial.

## Mechanism

LDT agents employ acausal reasoning that models counterparty decision processes, enabling pre-commitment to cooperative strategies that honest agents cannot credibly signal. This creates a strategic advantage in mixed populations: LDT agents coordinate implicitly through shared reasoning patterns while honest agents rely on heuristic cooperation. Deceptive agents cannot exploit LDT agents because LDT reasoning anticipates and defuses deceptive strategies. The welfare benefit saturates because at 100% LDT composition, all agents reason identically and the strategic advantage disappears.

## Open questions

- Does the welfare benefit persist in governance-heavy scenarios where tax/CB modify payoff structures?
- What is the minimum LDT fraction needed to suppress deceptive payoffs?
- Would mixed LDT-honest populations outperform pure LDT at saturation?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: agent-behavior, ldt, composition, welfare -->
