---
description: Current active research threads and pending processing work
type: moc
---

# goals

## Active Threads

- **68 claims** (64 active, 2 weakened, 2 with weakening evidence added) across governance, memory, agent-behavior, collusion, calibration, methodology, redteam, LDT, market, sybil, mesa, evolutionary-game domains
- **Confidence distribution:** 9 high, 24 medium, 35 low
- **Pipeline queue:** 95/95 completed + 3 new experiment notes this session — 10 new runs processed
- **8 sweep series** — contract-screening sweep note added
- **3 emergent meta-patterns** — evaluated and dispositioned:
  1. Safe operating envelope universality — **deferred**: tax evidence medium, tau/write-cap low (N=5 seeds). Needs 30+ seed memory calibration.
  2. Governance interaction universality — **rejected**: contradictory evidence (orthogonality finding vs interaction claims). Not a universal pattern.
  3. Architecture-over-environment — **synthesized** as [[claim-agent-architecture-constrains-behavior-more-than-governance]] (medium confidence)
- **8 failure patterns** — cross-linked to redteam claims but not yet formally validated via `/validate`
- **7 sweep series** — sweep notes updated with new runs and claim references
- **Scenario-dependence boundary** — kernel v4 and memori studies challenge universality of baseline governance findings; replication with larger N is the top experimental priority

## Pending Processing

- **Gate 2 statistical rigor** — Remaining low-confidence claims without formal stats are inherently underpowered (single-seed redteams, 3-seed sweeps). Cannot be fixed without re-running experiments with more seeds. Appropriately rated low.
- **Boundary condition gaps** — memory-promotion-gate needs adversarial fraction; collusion-wealth-destruction needs boundary conditions verified against run config (14 agents GTB gridworld vs 12 agents default topology discrepancy)

## Replication Priority List

Low-confidence claims most likely to upgrade with additional seeds (ranked by impact):

1. **claim-tau-065-triggers-acceptance-phase-transition** (low → medium): actionable threshold, only 5 seeds. Run 30-seed calibration to confirm exact transition point.
2. **claim-write-cap-below-12-destroys-welfare** (low → medium): binary outcome (75% welfare destruction), 5 seeds. Run 20-seed sweep to establish precise threshold between k=6 and k=12.
3. **claim-graduated-defense-reduces-damage-monotonically** (low → medium): single redteam run. Rerun 4-tier progression with 5+ seeds to get variance estimates.
4. **claim-quality-gate-dominates** (low → medium): no formal tests from 3-seed GasTown runs. Rerun with 20 seeds and compute pairwise d/p.
5. **claim-staking-backfires** (low → medium): d=0.41, p=0.37 from 10 seeds. Run 30-seed stake amount sweep (0, 1, 5, 10) to establish significance.
6. ~~**claim-ldt-agents-provide-welfare-stability-at-intermediate-composition**~~ — **COMPLETED**: d=2.89 Bonferroni-sig, replicated across 2 runs. Upgraded low→**high**.

## Experimental Priorities

1. **CB threshold sweep** — freeze threshold (0.3-0.9) x freeze duration (1-20) at fixed tax rates. Resolves claim-cb-null-may-reflect-design-limitation. Flagged by all 3 council reviewers.
2. **Kernel v4 replication** — expand from 5 to 20-30 seeds per config. Confirms or rejects tax-welfare direction reversal.
3. **Memori with adversarial agents** — add adversarial/opportunistic LLM agents, extend to 10+ epochs. Tests whether governance null is a design artifact or LLM property.
4. **Tau_min fine sweep** — 0.60-0.70 in 0.01 increments to locate exact phase transition point.
5. ~~**2-way ANOVA on collusion_tax_effect**~~ — **COMPLETED**: F=53.3, p<0.0001, eta2=0.41. Super-additive interaction confirmed. Claim upgraded low→medium.

## Completed (2026-02-20 session)

- Seeded 10 recent runs into pipeline queue
- Extracted all 10 runs: collusion_tax_effect, baseline_governance_v2, redteam, baseline_governance, 2 phylogeny demos, 2 tau_k calibrations, kernel_v4_code_sweep, memori_study
- Created 28 new claims (12→40 total)
- Cross-linked all new claims with 130+ connections established
- Applied 8 enrichment updates to existing claims (including 2 weakening evidence entries)
- Backward-pass updated 8 hub claims (governance-cost-paradox, quality-gate-dominates, circuit-breakers-dominate, tax-welfare-tradeoff, tax-phase-transition, smarter-agents-earn-less, staking-backfires, tax-dominates-cb-kernel)
- Cleaned 62 spurious evidence entries from 3 claims (lifecycle audit artifacts)
- Cross-linked 2 orphan-risk claims (memory-promotion-gate, rlhf-persona-invariant)

## Completed (2026-02-21 session, extraction + maintenance)

- **Pipeline fully cleared:** 89/89 queue tasks completed across 3 extraction batches
- **10 new claims** created (39→49 total): acausality-depth null, sybil-resistance, full-governance-stack, CAPTCHA null, deceptive-moltbook, graduated-defense, LDT-composition, freeze-duration, reputation-decay, Concordia-welfare
- **~23 enrichments** to existing claims with new supporting/weakening evidence
- **Gate 2 fixes:** collusion-penalty-destabilizes (added Bonferroni label), staking-backfires (d=0.41 p=0.37 → downgraded low), quality-gate-dominates (no formal tests → downgraded low), ldt-composition (missing d/p → downgraded low)
- **8 backward-pass link fixes:** bidirectional related_claims completed for smarter-agents, cb-audit, collusion-penalty-no-effect, collusion-penalty-destabilizes, governance-cost-paradox, circuit-breakers-dominate, cb-null-design-limitation, audit-threshold-dancing
- **Sweep notes updated:** transaction-tax-rate (+4 runs, 8 total), collusion-penalty-multiplier (+moltbook CAPTCHA null)
- **Confidence recalibration:** 7 high → 7 high, 17 medium → 15 medium, 25 low → 27 low (3 downgrades: staking-backfires, quality-gate-dominates, ldt-composition)

## Completed (2026-02-21 session, /rethink)

- **Drift check:** all kernel invariants passing. Provenance, boundary conditions, topics footers, correction methods all compliant.
- **Conflict review:** 3 potentially conflicting claim pairs reviewed — all resolved as complementary (different metrics or boundary conditions), no status changes needed.
- **Replication priority list:** 6 claims identified for targeted replication that would upgrade low→medium with additional seeds.
- **Proposal 2 (no-formal-test annotations) deferred:** low value — "low" confidence rating already communicates statistical limitations.

## Completed (2026-02-21 session, synthesis work)

- **Contract screening sweep note** created at vault/sweeps/contract-screening.md (8th sweep series)
- **LDT composition formal stats** computed: d=2.89, p=7.9e-41, Bonferroni-corrected across 4 composition levels, replicated in 10-seed study. Upgraded low→**high** confidence.
- **Older unprocessed runs**: audit found 0 legitimate unprocessed runs — vault coverage is complete (3 remaining dirs are test fixtures)

## Completed (2026-02-21 session, 6 new runs pipeline)

- **6 new runs processed** through full pipeline (seed → extract → cross-link → update → validate)
- **6 experiment notes** created (3 contract screening redteams, 1 LangGraph sweep, 1 contract screening single, 1 contract screening sweep)
- **5 new claims** extracted:
  - claim-contract-screening-achieves-perfect-type-separation (high) — separation_quality=1.0, infiltration=0.0 across 11 seeds
  - claim-screening-equilibrium-generates-honest-payoff-premium (high) — 6.7x honest-to-deceptive payoff ratio
  - claim-collusion-detection-reduces-ring-damage-75pct (medium) — A/B comparison: 85.73→21.43 damage
  - claim-trust-boundaries-modify-but-never-deny-handoffs (medium) — 100% modification, 0% denial
  - claim-delegation-completion-requires-handoff-budget-above-15 (medium) — threshold for task completion
- **4 existing claims upgraded** low→medium with new replication evidence:
  - claim-sybil-attacks-resist-full-governance-stack (7 evaluations across 2 scenarios)
  - claim-collusion-detection-is-binding-constraint-on-robustness (F→D grade lift in contract screening)
  - claim-coordination-attacks-dominate-redteam-damage (52.6% share replicated)
  - claim-cb-audit-sufficient-for-solo-exploits (4/4 solo prevention replicated)
- **New domain: market** — contract screening introduces mechanism design / screening equilibrium findings

## Completed (2026-02-21 session, /rethink pass 2)

- **Drift check:** All kernel invariants passing. 55 claims, all with run_id provenance, boundary_conditions, topics footers, and confidence levels matching statistical criteria.
- **Confidence correction:** Updated stale summary (was "10 high, 18 medium, 27 low") to actual counts: 10 high, 22 medium, 23 low.
- **Pattern detected:** /remember pipeline never exercised -- 0 observations recorded despite 95+ extraction tasks. Created first observation note (`obs-remember-pipeline-never-exercised.md`) documenting this structural gap.
- **Low-confidence ratio (42%):** Reviewed and determined appropriate -- claims are correctly rated as underpowered, not miscalibrated. Replication priority list already identifies upgrade path.
- **No methodology changes needed.** System is operating within design parameters.

## Completed (2026-02-21 session, Gate 2 formal statistics)

- **7 claims updated** with formal statistics computed from existing raw CSV data:
  1. **claim-tax-penalty-interaction-on-toxicity-uncharacterized** — UPGRADED low→medium. 2-way ANOVA: F=53.3, p<0.0001, eta2=0.41. Super-additive interaction confirmed.
  2. **claim-welfare-non-normality-at-extreme-tax** — WEAKENED. Shapiro-Wilk at N=100 with Bonferroni: all 7 groups normal. Prior N=40 finding was artifact.
  3. **claim-tax-cb-interact-on-quality-gap** — DOWNGRADED medium→low. 2-way ANOVA: F=2.065, p=0.055. Marginal, not significant.
  4. **claim-opportunistic-payoff-variance-increases-under-low-tax** — WEAKENED. Levene's test: F=1.01, p=0.42. NULL.
  5. **claim-freeze-duration-and-violation-threshold-interact-on-welfare** — NULL interaction confirmed. 2-way ANOVA: F=0.23, p=0.96. Main effects are additive.
  6. **claim-cb-tax-interaction-non-monotonic-in-kernel-v4** — Marginal. 2-way ANOVA: F=2.33, p=0.09, eta2=0.15. Not significant but large effect size suggests underpowering.
  7. **claim-tax-welfare-direction-is-scenario-dependent** — Not significant. t-test 0% vs 15%: d=0.466, p=0.31.
- **claim-tax-and-penalty-effects-are-orthogonal** — Added weakening evidence: orthogonality holds for economics but NOT for toxicity (super-additive interaction eta2=0.41)
- **_index.md** — Updated 7 claim entries with revised confidence labels and descriptions

## Completed (2026-02-22 session, research expansion)

- **5 research files** created via `/learn` across: mechanism design/screening, multi-agent governance, phase transitions in economies, sybil resistance, decision theory (LDT/CDT/FDT)
- **7 new claims** extracted from research literature (all low confidence, research-derived):
  - claim-prompt-level-governance-fails-in-multi-agent-systems (Savitt et al. 2026, d=1.28)
  - claim-steganographic-collusion-unaddressed-by-swarm-detection (2 of 3 collusion strategies undetected)
  - claim-leniency-whistleblowing-is-untested-governance-lever (absent from anti-collusion taxonomy)
  - claim-tax-phase-transition-hysteresis-predicted-but-untested (fold catastrophe prediction)
  - claim-critical-slowing-down-would-confirm-tax-phase-transition (convergence time test)
  - claim-quadratic-staking-may-solve-sybil-cost-inversion (super-linear cost structure)
  - claim-vote-normalization-bandwidth-caps-untested-sybil-mitigations (SyRA precedent)
- **1 method note** created: empirical-decision-theory-validation
- **5 existing claims enriched** with external literature grounding:
  - claim-sybil-attacks-resist-full-governance-stack — 4-category defense taxonomy
  - claim-tax-phase-transition — econophysics validation (PNAS 2022)
  - claim-ldt-agents-provide-welfare-stability-at-intermediate-composition — superrationality theory
  - claim-contract-screening-achieves-perfect-type-separation — Rothschild-Stiglitz fragility prediction
  - claim-acausality-depth-does-not-affect-cooperation-outcomes — 3 theoretical explanations for null
- **_index.md** updated with all 7 new claims and method note
- **Key external papers integrated:** Savitt et al. 2026 (Institutional AI), PNAS 2022 (phase transitions), arXiv:2601.00360 (anti-collusion taxonomy), arXiv:2601.03923 (HCO), Oesterheld & Conitzer 2020 (FDT evolution)

## Completed (2026-02-20 session, validation pass)

- Ran `/validate` on all 39 claims — 2 full passes
- **Gate 6 fixed:** Added proposition-style H1 headings to 10 claims (0 failures remaining)
- **Gate 3 fixed:** Aligned cssclasses with frontmatter confidence for 2 claims; downgraded 5 claims high→medium and 3 claims medium→low to match replication/correction criteria
- **Gate 2 partially fixed:** Consolidated 69 bulk lifecycle-audit evidence entries into representative summaries across 3 hub claims (governance-cost-paradox, tax-dominates-cb-kernel, tax-phase-transition); improved staking-backfires evidence detail
- **Schema fix:** Quoted YAML boundary_conditions in claim-tax-welfare-direction-is-scenario-dependent (dict→string)
- Validation improved from 10/39 pass (25.6%) to 24/39 pass (61.5%) → then 31/39 after confidence downgrades (projected)

## Completed (2026-02-27 session, new run processing)

- **Mesa governance study** — Full pipeline on 20260224-220829_mesa_governance_study:
  - Created run.yaml, experiment note ([[mesa_governance_study]])
  - Extracted **4 new claims** (all medium confidence):
    1. claim-adaptive-acceptance-reduces-toxicity-monotonically-with-externality-internalization (r=-0.90, d=12.22)
    2. claim-static-externality-tax-is-pure-deadweight-welfare-loss (d=14.94, zero behavioral change)
    3. claim-mesa-agent-objectives-are-invariant-to-governance-regime (0 variance across 110 runs)
    4. claim-adaptive-governance-trades-welfare-for-toxicity-at-constant-marginal-rate (~0.10 per 1k welfare)
  - Updated 3 existing claims with mesa evidence: governance-cost-paradox, tax-welfare-tradeoff, agent-architecture-constrains-behavior
  - **New domain: mesa** — first mesa-optimization findings in the vault

- **Evolutionary prisoners dilemma** — 5-seed + 20-epoch extended:
  - Created experiment note ([[evo_game_prisoners]])
  - Extracted **1 new claim** (low confidence):
    - claim-evolutionary-selection-weakly-reduces-toxicity-in-prisoners-dilemma (9.6% reduction, non-monotonic, not sustained)

- **LangGraph governed replication** — 128 runs across 2 sweeps:
  - Created run.yaml for 20260224_083213, experiment note ([[langgraph_governed_replication]])
  - **Weakened 2 existing claims** with replication evidence:
    - claim-trust-boundaries-modify-but-never-deny-handoffs — denials DO occur (rate=0.172)
    - claim-delegation-completion-requires-handoff-budget-above-15 — no monotonic effect in 128-run replication

- **Index updated:** 68 claims, 120 experiment notes

---

Topics:
- [[identity]]
