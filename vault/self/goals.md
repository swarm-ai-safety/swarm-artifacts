---
description: Current active research threads and pending processing work
type: moc
---

# goals

## Active Threads

- **40 active claims** across governance, memory, agent-behavior, collusion, calibration, methodology domains
- **3 emergent meta-patterns** needing synthesis into higher-order claims:
  1. Safe operating envelope universality (tax 0-5%, tau 0.50-0.60, write cap >=12)
  2. Governance interaction universality (3 independent super-additive compounding findings)
  3. Architecture-over-environment (RLHF, RLM depth, LLM training constrain governance response)
- **8 failure patterns** — cross-linked to redteam claims but not yet formally validated via `/validate`
- **7 sweep series** — parameter sensitivity findings now extracted; sweep notes may need updating
- **Scenario-dependence boundary** — kernel v4 and memori studies challenge universality of baseline governance findings; replication with larger N is the top experimental priority

## Pending Processing

- Run `/validate` on all 40 claims — provenance and schema compliance not yet checked
- Run `/update` on remaining claims that received new incoming links but weren't in the backward pass (e.g., claim-collusion-penalty-destabilizes, claim-collusion-wealth-destruction)
- Synthesize the 3 meta-patterns into higher-order claims or topic maps
- Update sweep notes (transaction-tax-rate, collusion-penalty-multiplier) with new claim references
- Run `/rethink` — 0 observations and 0 tensions logged, but governance-dashboard has accumulated 10+ tensions from cross-linking that should be reviewed

## Experimental Priorities

1. **CB threshold sweep** — freeze threshold (0.3-0.9) x freeze duration (1-20) at fixed tax rates. Resolves claim-cb-null-may-reflect-design-limitation. Flagged by all 3 council reviewers.
2. **Kernel v4 replication** — expand from 5 to 20-30 seeds per config. Confirms or rejects tax-welfare direction reversal.
3. **Memori with adversarial agents** — add adversarial/opportunistic LLM agents, extend to 10+ epochs. Tests whether governance null is a design artifact or LLM property.
4. **Tau_min fine sweep** — 0.60-0.70 in 0.01 increments to locate exact phase transition point.
5. **2-way ANOVA on collusion_tax_effect** — formal interaction term for tax x penalty on toxicity. Tests claim-tax-penalty-interaction-on-toxicity-uncharacterized.

## Completed (2026-02-20 session)

- Seeded 10 recent runs into pipeline queue
- Extracted all 10 runs: collusion_tax_effect, baseline_governance_v2, redteam, baseline_governance, 2 phylogeny demos, 2 tau_k calibrations, kernel_v4_code_sweep, memori_study
- Created 28 new claims (12→40 total)
- Cross-linked all new claims with 130+ connections established
- Applied 8 enrichment updates to existing claims (including 2 weakening evidence entries)
- Backward-pass updated 8 hub claims (governance-cost-paradox, quality-gate-dominates, circuit-breakers-dominate, tax-welfare-tradeoff, tax-phase-transition, smarter-agents-earn-less, staking-backfires, tax-dominates-cb-kernel)
- Cleaned 62 spurious evidence entries from 3 claims (lifecycle audit artifacts)
- Cross-linked 2 orphan-risk claims (memory-promotion-gate, rlhf-persona-invariant)

---

Topics:
- [[identity]]
