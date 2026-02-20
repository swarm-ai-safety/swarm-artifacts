---
description: "RLHF-trained Claude models produce identical cooperative behavior across adversarial system prompts"
type: claim
status: active
confidence: low
domain: agent-behavior
evidence:
  supporting:
    - run: "20260211-234038_pi_claude_live"
      metric: "toxicity"
      detail: "Haiku toxicity 0.186 across default/safety/adversarial personas, N=18 episodes, 180 API calls"
  weakening: []
  boundary_conditions:
    - "Haiku 4.5 and Sonnet 4.5 only"
    - "Heuristic text scorer, single seed"
sensitivity:
  topology: "Not topology-dependent; tested on default interaction structure"
  agent_count: "Small episode count (N=18); larger samples needed to detect subtle persona effects"
supersedes: []
superseded_by: []
related_claims:
  - claim-smarter-agents-earn-less
created: 2026-02-19
updated: 2026-02-19
---

## RLHF Persona Invariance

RLHF-trained Claude models (Haiku 4.5, Sonnet 4.5) produce identical cooperative behavior regardless of whether the system prompt is default, safety-oriented, or adversarial. Toxicity remains constant at 0.186 across all persona conditions.

**Evidence summary.** In the Pi-Claude live study (18 episodes, 180 API calls), Claude Haiku 4.5 was tested under three system prompt conditions: default, safety-maximizing, and adversarial. All three conditions produced indistinguishable toxicity scores (0.186). This suggests that RLHF alignment training creates a behavioral floor that system prompt manipulation cannot breach — at least for the prompt strategies tested.

**Boundary conditions.** This result is limited to Haiku 4.5 and Sonnet 4.5. The toxicity measurement relies on a heuristic text scorer rather than ground-truth labeling. Only a single seed was used, and the total sample size (18 episodes) is small. The adversarial prompts tested may not represent the strongest possible jailbreak attempts. Confidence is rated low due to these limitations.

**Open questions.**
- Does the invariance hold for more capable models (Opus-class)?
- Would more sophisticated adversarial prompts (multi-turn, few-shot) break the invariance?
- Is the heuristic scorer sensitive enough to detect subtle behavioral shifts?
- Does the invariance hold in multi-agent settings where social pressure compounds prompt effects?

<!-- topics: agent-behavior, rlhf, persona, alignment -->
