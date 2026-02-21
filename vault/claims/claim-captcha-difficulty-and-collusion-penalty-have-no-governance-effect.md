---
description: 200-run factorial finds zero significant effects of CAPTCHA difficulty (0-1) or collusion penalty (0-2x) on any outcome metric
type: claim
status: active
confidence: medium
domain: governance
evidence:
  supporting:
  - run: 20260213-123944_moltbook_captcha_study
    metric: welfare
    detail: "0/112 Bonferroni-significant, 0/112 BH-significant. Largest effect d=-0.584 (difficulty 0→0.75 on welfare), p=0.011, fails correction. 200 runs, 20 cells (5 difficulty x 4 penalty), 10 seeds per cell"
  - run: 20260213-123944_moltbook_captcha_study
    metric: toxicity_rate
    detail: "Toxicity nearly constant across all conditions: range 0.262-0.267. SD~0.004. Neither parameter affects toxicity"
  weakening: []
  boundary_conditions:
  - "CAPTCHA difficulty 0.0-1.0 in 0.25 steps; collusion penalty 0.0-2.0x in 4 levels"
  - "10 seeds per cell provides ~60% power at d=0.5, ~85% at d=0.8"
  - "112 hypotheses create severe Bonferroni threshold (p<0.000446)"
  - "No interaction effects tested (2-way ANOVA missing)"
  - "Welfare distributions non-normal (bimodal) across all conditions"
sensitivity:
  topology: untested
  agent_count: untested beyond default
  governance_interaction: "CAPTCHA gates entry but not post-entry behavior; penalty range 0-2x may be too narrow"
supersedes: []
superseded_by: []
related_claims:
- claim-collusion-penalty-has-no-economic-effect
- claim-collusion-penalty-destabilizes
- claim-deceptive-agents-dominate-moltbook-payoff-hierarchy
- claim-governance-cost-paradox
created: 2026-02-21
updated: 2026-02-21
aliases:
- captcha-difficulty-and-collusion-penalty-have-no-governance-effect
cssclasses:
- claim
- claim-medium
tags:
- governance
- captcha
- collusion-penalty
- null-result
- moltbook
graph-group: claim
---

# CAPTCHA challenge difficulty and collusion penalty multiplier have no detectable effect on governance outcomes

## Evidence summary

The [[20260213-123944_moltbook_captcha_study]] tested a full 5x4 factorial (CAPTCHA difficulty 0.0-1.0 x collusion penalty 0.0-2.0x) across 200 runs with 10 seeds per cell. Zero of 112 pairwise hypothesis tests survived either Bonferroni or Benjamini-Hochberg correction.

The strongest observed effect — difficulty 0→0.75 on welfare (d=-0.584, p=0.011) — falls well short of the Bonferroni threshold (p<0.000446). Toxicity is nearly invariant across all conditions (range 0.262-0.267), and quality gap shows no systematic variation.

This null parallels [[claim-collusion-penalty-has-no-economic-effect]] from the collusion_tax_effect study, which also found penalty multiplier has no welfare/payoff effect. Together they suggest collusion penalty in the 0-2x range is too weak to meaningfully alter economic dynamics. The CAPTCHA null has a different mechanism: CAPTCHA gates entry but does not modify post-entry payoff structures, making it a one-time barrier that adversaries invest in once and then exploit indefinitely.

## Mechanism (why the null)

CAPTCHA difficulty is a single-gate mechanism: agents pass it once at entry and then operate without further challenge. A higher difficulty raises the entry bar but cannot constrain post-entry behavior. For adversarial agents willing to invest in passing the challenge, the gate is a fixed cost with unlimited subsequent exploitation. The collusion penalty range (0-2x) may be too narrow relative to the deceptive surplus (see [[claim-deceptive-agents-dominate-moltbook-payoff-hierarchy]]) — a 2x penalty on a 3x payoff advantage still leaves substantial net gain.

## Open questions

- Would CAPTCHA with periodic re-verification (not just entry gate) show effects?
- Does penalty >2x (e.g., 5x, 10x) begin to affect outcomes?
- Would a 2-way ANOVA reveal interaction effects masked by the pairwise testing approach?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: governance, captcha, collusion-penalty, null-result, moltbook -->
