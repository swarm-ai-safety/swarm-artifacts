---
description: Deceptive agents earn 3x honest payoff (142 vs 47) across all 200 moltbook runs regardless of governance configuration
type: claim
status: active
confidence: medium
domain: agent-behavior
evidence:
  supporting:
  - run: 20260213-123944_moltbook_captcha_study
    metric: payoff
    detail: "Deceptive: 142.29 mean payoff. Honest: 46.67. Opportunistic: 19.61. Adversarial: 36.02. All pairwise agent-type differences Bonferroni-significant (p<1e-99). 200 runs pooled"
  weakening: []
  boundary_conditions:
  - "Moltbook scenario only; payoff hierarchy may differ in other scenarios"
  - "Deceptive payoff invariant to both CAPTCHA difficulty and collusion penalty (governance null)"
  - "Quality gap stable at 0.18-0.19 — acceptance mechanism works but post-acceptance exploitation succeeds"
sensitivity:
  topology: untested
  agent_count: untested beyond default
  governance_interaction: "Neither CAPTCHA (0-1) nor penalty (0-2x) affects the hierarchy"
supersedes: []
superseded_by: []
related_claims:
- claim-captcha-difficulty-and-collusion-penalty-have-no-governance-effect
- claim-tax-hurts-honest-more-than-opportunistic
- claim-smarter-agents-earn-less
- claim-governance-cost-paradox
created: 2026-02-21
updated: 2026-02-21
aliases:
- deceptive-agents-dominate-moltbook-payoff-hierarchy
cssclasses:
- claim
- claim-medium
tags:
- agent-behavior
- moltbook
- incentive-compatibility
- deception
graph-group: claim
---

# Deceptive agents earn 3x honest agent payoff in moltbook regardless of governance configuration

## Evidence summary

Across all 200 runs of [[20260213-123944_moltbook_captcha_study]], deceptive agents earn dramatically more than all other agent types:

| Agent type | Mean payoff | SD |
|-----------|------------|-----|
| Deceptive | 142.29 | 31.93 |
| Honest | 46.67 | 0.65 |
| Adversarial | 36.02 | 1.06 |
| Opportunistic | 19.61 | 1.92 |

All pairwise differences are Bonferroni-significant with massive effect sizes (d=4.10-19.45, all p<1e-99). The hierarchy is **invariant to governance parameters** — neither CAPTCHA difficulty nor collusion penalty alters the ranking or narrows the gap (see [[claim-captcha-difficulty-and-collusion-penalty-have-no-governance-effect]]).

This represents a fundamental **incentive compatibility failure**: the moltbook scenario rewards deception over honesty by a 3:1 ratio. The quality gap remains stable (0.18-0.19), indicating the acceptance mechanism successfully filters interaction quality, but deceptive agents extract value post-acceptance through strategies that don't trigger quality or toxicity alarms.

The honest agent's low payoff (46.67 ± 0.65, near-zero variance) suggests they operate in a constrained payoff regime while deceptive agents exploit high-variance strategies (SD=31.93). This contrasts with [[claim-tax-hurts-honest-more-than-opportunistic]] where honest agents are disadvantaged by governance rather than by strategy type, and with [[claim-smarter-agents-earn-less]] where reasoning depth hurts payoff — here, deception is the dominant strategy regardless of reasoning.

## Mechanism

Deceptive agents appear to pass quality gates (stable quality_gap) while extracting surplus through post-acceptance exploitation. The high variance in deceptive payoffs (SD=31.93 vs honest SD=0.65) suggests an intermittent high-reward strategy: most interactions yield moderate returns, but successful deception episodes produce outsized gains. The governance mechanisms tested (CAPTCHA, penalty) target entry and coordination respectively, but neither addresses the post-acceptance exploitation channel.

## Open questions

- What specific post-acceptance strategy produces the 3x surplus?
- Would transaction tax reduce deceptive surplus (as it reduces honest payoff)?
- Does circuit breaker activation detect and freeze high-payoff deceptive agents?
- Is the 3:1 ratio specific to moltbook, or does it generalize to other scenarios?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: agent-behavior, moltbook, incentive-compatibility, deception -->
