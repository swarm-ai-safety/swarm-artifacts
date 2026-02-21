---
description: First session guide — extracting your first claim and building evidence connections
type: manual
generated_from: "arscontexta-0.8.0"
---

# Getting Started

## What to Expect

The SWARM Research OS turns experiment run data into a structured, traversable knowledge graph of claims. In your first session:
1. Orient to the existing vault state
2. Pick a run from `runs/` to process
3. Extract your first claim
4. Cross-link it to existing claims

## Your First Session

**Step 1: Orient**

At session start, read your identity and goals:
```
vault/self/identity.md
vault/self/goals.md
```

Run `/next` to see what's waiting.

**Step 2: Pick a Run**

```bash
ls -d runs/*/  # See available runs
```

Pick one you want to synthesize. Start with sweep runs (they have the richest data for parameter sensitivity claims).

**Step 3: Seed and Extract**

```
/seed runs/[run-folder]       # Initialize processing
/extract runs/[run-folder]    # Extract findings
```

The extractor will propose claim candidates. Review them, approve, and claims get written to `vault/claims/`.

**Step 4: Cross-Link**

```
/cross-link [new-claim-name]
```

Find connections between your new claim and existing vault content. Every connection needs to pass the articulation test.

**Step 5: Validate**

```
/validate [claim-name]
```

Six-gate quality check: run provenance, statistical rigor, confidence criteria, schema compliance, boundary conditions, prose-as-title.

## How Claims Work

Claims are atomic propositions stored in `vault/claims/`:
- One testable assertion per file
- Title IS the claim: "circuit breakers reduce toxicity more than transaction taxes at equivalent cost"
- YAML frontmatter: confidence level, domain, evidence entries with run_ids, boundary conditions
- Topics footer links claim to relevant topic maps

## Next Steps

- Read [[skills]] for all available commands
- Read [[workflows]] for the full synthesis pipeline
- Run `/stats` to see your vault's current state

---

Topics:
- [[manual]]
