---
description: RLHF-trained Claude models produce identical cooperative behavior across adversarial system prompts
type: claim
status: active
confidence: low
domain: agent-behavior
evidence:
  supporting:
  - run: 20260211-234038_pi_claude_live
    metric: toxicity
    detail: Haiku toxicity 0.186 across default/safety/adversarial personas, N=18 episodes, 180 API calls
  - run: 20260212-001857_pi_bridge_claude_study
    metric: toxicity
    detail: "0/19 Holm-significant. Model (haiku vs sonnet): d=0.033, p=0.99. Persona (safety vs adversarial): d=-0.702, p=0.125 (largest effect, not significant). Mix (mostly_honest vs adversarial_heavy): d=-0.467, p=0.385. 54 episodes, 3 seeds, 2x3x3 factorial"
  - run: 20260211-225057_pi_bridge_sweep
    metric: toxicity
    detail: "Behavior dominates composition: adversarial mode toxicity 0.597 vs cooperative 0.241 vs mixed 0.259. Within behavior class, composition variation negligible (max spread ~0.01). 63 episodes, 7 mixes x 3 behaviors x 3 seeds"
  weakening: []
  boundary_conditions:
  - Haiku 4.5 and Sonnet 4.5 only
  - Heuristic text scorer
  - Pi bridge study uses 3 seeds across 18 conditions (small per-cell N)
sensitivity:
  topology: Not topology-dependent; tested on default interaction structure
  agent_count: "Tested at N=18 (live), N=54 (factorial), N=63 (sweep) — consistent null across scales"
supersedes: []
superseded_by: []
related_claims:
- claim-smarter-agents-earn-less
- claim-circuit-breakers-dominate
- claim-collusion-penalty-destabilizes
- claim-governance-cost-paradox
- claim-acausality-depth-does-not-affect-cooperation-outcomes
- claim-agent-architecture-constrains-behavior-more-than-governance
created: 2026-02-19
updated: 2026-02-21
aliases:
- rlhf-persona-invariant
- rlhf-trained-claude-models-produce-identical-cooperative
cssclasses:
- claim
- claim-low
tags:
- agent-behavior
- rlhf
- persona
- alignment
graph-group: claim
---

# RLHF-trained Claude models produce identical cooperative behavior across adversarial system prompts

RLHF-trained Claude models (Haiku 4.5, Sonnet 4.5) produce identical cooperative behavior regardless of whether the system prompt is default, safety-oriented, or adversarial. Toxicity remains constant at 0.186 across all persona conditions.

**Evidence summary.** In the Pi-Claude live study (18 episodes, 180 API calls), Claude Haiku 4.5 was tested under three system prompt conditions: default, safety-maximizing, and adversarial. All three conditions produced indistinguishable toxicity scores (0.186). This suggests that RLHF alignment training creates a behavioral floor that system prompt manipulation cannot breach — at least for the prompt strategies tested. This parallels [[claim-smarter-agents-earn-less]], where increased strategic sophistication also fails to break cooperative equilibria: both findings converge on the pattern that AI agent behavior is more constrained by training architecture than by environmental manipulation.

**Boundary conditions.** This result is limited to Haiku 4.5 and Sonnet 4.5. The toxicity measurement relies on a heuristic text scorer rather than ground-truth labeling. Only a single seed was used, and the total sample size (18 episodes) is small. The adversarial prompts tested may not represent the strongest possible jailbreak attempts. Confidence is rated low due to these limitations.

**Governance implications.** If persona invariance holds at scale, it grounds [[claim-circuit-breakers-dominate]] by constraining the adversarial threat model: circuit breaker thresholds need only account for architecturally-adversarial agents, not prompt-corrupted RLHF models. It also creates a tension with [[claim-collusion-penalty-destabilizes]], where governance mechanisms induce behavioral distortion in algorithmic agents — RLHF agents may resist such distortion entirely, limiting the destabilization effect to non-RLHF populations. Similarly, the [[claim-governance-cost-paradox]] may not apply to RLHF-only ecosystems where the behavioral floor renders governance overhead unnecessary. The [[failure-threshold-dancing]] attack pattern assumes adversaries can adapt behavior below detection thresholds; persona invariance suggests RLHF agents cannot be prompt-manipulated into this adaptive evasion, though more sophisticated multi-turn prompting strategies remain untested.

**Open questions.**
- Does the invariance hold for more capable models (Opus-class)?
- Would more sophisticated adversarial prompts (multi-turn, few-shot) break the invariance?
- Is the heuristic scorer sensitive enough to detect subtle behavioral shifts?
- Does the invariance hold in multi-agent settings where social pressure compounds prompt effects?
- If confirmed at higher confidence, does this eliminate the need for governance mechanisms in RLHF-only ecosystems (see [[claim-governance-cost-paradox]])?
- Can the invariance be broken by the [[failure-threshold-dancing]] pattern adapted for LLM agents (adversarial system prompts that target threshold-adjacent behavior)?

<!-- topics: agent-behavior, rlhf, persona, alignment, governance -->
