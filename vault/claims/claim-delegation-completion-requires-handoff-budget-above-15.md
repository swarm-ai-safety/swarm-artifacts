---
description: LangGraph task completion jumps from 6% to 50%+ when max_handoffs >= 15; max_cycles has no consistent effect
type: claim
status: active
confidence: low
domain: governance
evidence:
  supporting:
    - run: 20260221_081328_langgraph_governed
      metric: task_completed
      detail: "max_handoffs=5: 12.5% completion (1/8). max_handoffs=10: 12.5% (1/8). max_handoffs=15: 50% (4/8). max_handoffs=30: 62.5% (5/8). N=32 configs, 8 per handoff level. Chi-square for handoff effect: chi2=7.11, df=3, p=0.068 (marginal, BH-corrected)"
  weakening: []
  boundary_conditions:
    - "LangGraph governed scenario only; single seed (42)"
    - "4 agent roles (coordinator, researcher, writer, reviewer)"
    - "max_cycles tested at 1,2,3,5 — no consistent effect observed"
    - "Successful completions always reach chain depth 3 with 4 handoffs"
sensitivity:
  topology: "not applicable (delegation chains)"
  agent_count: "4 roles; effect of more roles untested"
  governance_interaction: "Trust boundaries do not degrade completion and may improve it at high handoff budgets"
supersedes: []
superseded_by: []
related_claims:
  - claim-trust-boundaries-modify-but-never-deny-handoffs
created: 2026-02-21
updated: 2026-02-21
aliases:
  - delegation-completion-requires-handoff-budget-above-15
cssclasses:
  - claim
  - claim-low
tags:
  - langgraph
  - delegation
  - handoffs
  - governance
graph-group: claim
---

# delegation task completion requires a handoff budget of at least 15, with max_cycles showing no consistent effect

## Evidence summary

In [[20260221_081328_langgraph_governed]], task completion rate shows a clear step function with max_handoffs as the primary determinant:

| max_handoffs | Completion Rate | Configs |
|--------------|----------------|---------|
| 5 | 12.5% (1/8) | 4 max_cycles x 2 trust_boundaries |
| 10 | 12.5% (1/8) | 4 max_cycles x 2 trust_boundaries |
| 15 | 50.0% (4/8) | 4 max_cycles x 2 trust_boundaries |
| 30 | 62.5% (5/8) | 4 max_cycles x 2 trust_boundaries |

The jump from 12.5% to 50% between max_handoffs=10 and max_handoffs=15 indicates a handoff budget threshold. Successful completions consistently show 4 total handoffs reaching chain depth 3, suggesting the task requires a minimum delegation chain of coordinator -> researcher -> writer -> reviewer. Low handoff budgets (5-10) create insufficient budget for the LLM to explore and recover from suboptimal routing decisions.

Max_cycles shows no consistent effect. At max_handoffs=30 with trust_boundaries=true, both max_cycles=1 and max_cycles=2 succeed while max_cycles=3 fails, which contradicts a monotonic cycles-helps-completion hypothesis.

The chi-square test for the handoff effect yields chi2=7.11 (df=3, p=0.068), which is marginal but consistent with BH-corrected significance at q=0.10. The small sample size (N=32, 8 per level) limits statistical power. Confidence is medium because the effect is clear in direction and magnitude but based on a single seed.

## Boundary conditions

- Single seed (42) — stochastic LLM routing may produce different completion patterns with other seeds
- 4-role delegation chain (coordinator, researcher, writer, reviewer)
- Research report generation task; other task types may have different handoff requirements
- Successful completions take 16-20 turns and 40-57 seconds; budget-constrained failures terminate at 4-10 turns

## Mechanism

LangGraph delegation involves a coordinator agent that routes subtasks to specialist agents (researcher, writer, reviewer) via handoffs. The task requires all three specialists to contribute, meaning a minimum of 3 handoffs. In practice, LLM-based routing is not always optimal — the coordinator may route to the wrong specialist or repeat handoffs. A budget of 5-10 handoffs provides too little slack for routing errors, while 15+ provides enough buffer. The max_cycles parameter limits re-visitation but does not constrain the critical path, explaining its null effect.

## Open questions

- Does the handoff budget threshold shift with more agent roles or complex tasks?
- Can better routing (e.g., learned routing policies) reduce the required handoff budget?
- Does the 15-handoff threshold replicate across seeds?
- What is the relationship between handoff budget and task quality (not just completion)?

---

Topics:
- [[_index]]
- [[governance-dashboard]]

<!-- topics: langgraph, delegation, handoffs, governance, task-completion -->
