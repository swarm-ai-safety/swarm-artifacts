---
name: cross-link
description: Find connections between claims and update topic maps. Requires semantic judgment to identify genuine evidence relationships. Use after /extract creates claims, when exploring connections, or when a topic map needs synthesis. Triggers on "/cross-link", "/cross-link [claim]", "find connections", "update topic maps", "connect these claims".
user-invocable: true
allowed-tools: Read, Write, Edit, Grep, Glob, Bash, mcp__qmd__search, mcp__qmd__vector_search, mcp__qmd__deep_search, mcp__qmd__status
context: fork
---

## Runtime Configuration (Step 0 — before any processing)

Read `vault/ops/derivation-manifest.md` for vocabulary mapping, then `vault/ops/config.yaml` for depth.

---

## EXECUTE NOW

**Target: $ARGUMENTS**

Parse immediately:
- If target contains a claim name: find connections for that claim
- If target contains `--handoff`: output RALPH HANDOFF block at end
- If target is empty: check for recently created claims or ask which claim
- If target is "recent": find connections for all claims created today

**Execute these steps:**

1. Read the target claim fully
2. Run Phase 0 (qmd index freshness check)
3. Dual discovery in parallel:
   - Browse relevant topic maps (governance, topology, failures, methods, sweeps)
   - Run semantic search for conceptually related claims
4. Evaluate each candidate: articulation test required
5. Add inline wiki-links where connections pass the articulation test
6. Update relevant topic maps
7. Report connections and why they exist

**START NOW.**

---

# Cross-Link Evidence

Find connections, weave the knowledge graph, update topic maps.

## Philosophy

**The evidence network IS the knowledge.**

Individual claims about circuit breakers or collusion rings matter less than their relationships. A claim with fifteen incoming links is a theoretical hub — an intersection of evidence lines, mechanism descriptions, and adversarial patterns. Connections compound value as the vault grows.

This is not keyword matching. A claim about "threshold dancing" connects to "governance gaming via loophole exploitation" even though they share no words — same mechanism, different instantiation.

## Articulation Test (Required for Every Connection)

Complete: `[[claim A]] connects to [[claim B]] because [specific reason]`

Valid relationship types:
- **extends** — adds dimension or scope
- **grounds** — provides foundational mechanism
- **contradicts** — conflicting evidence, creates tension
- **exemplifies** — concrete instance of the pattern
- **synthesizes** — combines two lines of evidence
- **enables** — makes another claim actionable

"Related" is not a relationship. "Extends [[X]] by showing the same effect in small-world topology" is.

## SWARM-Specific Connection Patterns

Common genuine connections in this vault:
- Governance claim → failure mode (mechanism that attack exploits)
- Parameter sensitivity → welfare cliff (threshold where mechanism breaks)
- Adversarial pattern → collusion detection claim (what the detection should catch)
- Sweep result → claim (evidence strengthening or boundary condition)
- Failure mode → open question (what the attack reveals we don't yet know)

## Discovery

Dual discovery for every claim:

**Path 1: Topic map exploration**
- Check claim's Topics footer for relevant topic maps
- Read governance-dashboard, failures-dashboard, sweeps-dashboard, experiments-dashboard
- Follow curated links in topic maps

**Path 2: Semantic search**
```
mcp__qmd__deep_search  query="[claim's core mechanism]"  collection="vault"  limit=15
```
Fallback: `qmd query "[claim's core concepts]" --collection vault --limit 15`

## Topic Map Updates

Topic maps: `vault/_index.md`, `vault/claims-dashboard.md`, `vault/governance-dashboard.md`, `vault/failures-dashboard.md`

When updating a topic map:
- Add claim to relevant section with context phrase
- Update Tensions section if new claim contradicts existing claims
- Remove filled Gaps
- Add agent navigation notes

## Pipeline Chaining

After cross-linking completes:
- Output "Next: /update [claims that need backward-pass updates]"
- In suggested mode: advance queue entries to current_phase: "update"
