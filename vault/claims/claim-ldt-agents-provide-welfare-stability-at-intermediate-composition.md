---
description: LDT agents maintain +48% welfare over honest agents at 40-70% composition (d=2.89, p<1e-40, Bonferroni-corrected, replicated)
type: claim
status: active
confidence: high
domain: agent-behavior
evidence:
  supporting:
  - run: 20260211-215617_ldt_composition_study
    metric: welfare
    detail: "20 seeds. LDT vs Honest at 40-70% composition: pooled d=2.89, t(158)=18.28, p=7.9e-41. Per-level Bonferroni-corrected (k=4): 40% d=1.57 p_bonf=6.0e-05, 50% d=2.82 p_bonf=3.1e-10, 60% d=4.25 p_bonf=2.1e-15, 70% d=11.66 p_bonf=9.2e-31. All significant at alpha=0.05. LDT mean welfare 557 vs Honest 375 (+48.4%). Variance compression: CV from 16.4% at 0% LDT to 4.0% at 70% LDT"
  - run: 20260211-011020_ldt_composition_study
    metric: welfare
    detail: "10 seeds. Replication: LDT vs Honest at 40-70% composition d=3.25, t(78)=14.53, p=6.7e-24. LDT mean welfare 560 vs Honest 367 (+52.6%). Confirms primary finding independently"
  - run: 20260211-003414_ldt_composition_study
    metric: welfare
    detail: "3 seeds. LDT prevents welfare collapse at 40-60% focal. LDT payoff 72-75 at saturation vs honest 38-40"
  - run: 20260211-002843_ldt_composition_study
    metric: welfare
    detail: "1 seed. LDT +42% welfare at 70%+ composition (9.29 vs 6.51). LDT reduces toxicity 0.43→0.25 across full spectrum"
  - run: research-decision-theory-multiagent-2026-02-22
    source_type: research
    detail: "Decision theory literature grounding: Hofstadter's superrationality predicts cooperation among similar reasoners. Evolutionary game theory predicts cooperative strategies require critical mass for evolutionary stability — consistent with SWARM's 40-70% sweet spot. Oesterheld & Conitzer (2020) show FDT evolutionary stability depends on population mix. SWARM's result is among the first large-scale empirical validations of decision theory predictions in multi-agent simulations"
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
updated: 2026-02-22
aliases:
- ldt-agents-provide-welfare-stability-at-intermediate-composition
cssclasses:
- claim
- claim-high
tags:
- agent-behavior
- ldt
- composition
- welfare
graph-group: claim
---

# LDT agents provide welfare stability and suppress deception at intermediate population compositions

## Evidence summary

Four LDT composition studies (1, 3, 10, and 20 seeds) consistently show that replacing honest agents with LDT (Logical Decision Theory) agents at 40-70% of the population improves welfare by 48% while suppressing deceptive agent payoffs. Formal statistical testing confirms this with very large effect sizes replicated across independent studies.

**Formal statistics (20-seed primary study, [[20260211-215617_ldt_composition_study]]):**
- Pooled LDT vs Honest welfare at 40-70% composition: Cohen's d = 2.89, t(158) = 18.28, p = 7.9e-41
- Per-composition Bonferroni-corrected tests (k = 4, alpha = 0.05): all four levels significant
  - 40% LDT: d = 1.57, p_bonf = 6.0e-05 (welfare +31%)
  - 50% LDT: d = 2.82, p_bonf = 3.1e-10 (welfare +46%)
  - 60% LDT: d = 4.25, p_bonf = 2.1e-15 (welfare +45%)
  - 70% LDT: d = 11.66, p_bonf = 9.2e-31 (welfare +77%)
- N = 80 per group (20 seeds x 4 composition levels), 30 epochs per seed

**Replication (10-seed study, [[20260211-011020_ldt_composition_study]]):**
- LDT vs Honest at 40-70%: d = 3.25, t(78) = 14.53, p = 6.7e-24 (+53% welfare)
- Independently confirms the primary finding

**Key pattern across studies:**
- At 0% LDT focal (all honest), welfare is moderate and deceptive agents earn high payoffs (~57 units)
- At 40-70% LDT focal, welfare is significantly higher than honest baseline with monotonically increasing effect size
- At 90-100% LDT focal, welfare remains high but LDT individual payoffs diminish (tragedy of the commons at saturation)
- Variance compression accompanies the welfare gain: coefficient of variation drops from 16.4% at 0% LDT to 4.0% at 70% LDT, indicating welfare stabilization

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
