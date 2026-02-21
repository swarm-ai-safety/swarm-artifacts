---
description: Complete reference for every available command in the SWARM Research OS
type: manual
generated_from: "arscontexta-0.8.0"
---

# Skills

## Processing Pipeline

| Command | When to Use | Example |
|---------|-------------|---------|
| `/seed [run]` | Initialize a run for pipeline processing | `/seed runs/20260218-baseline-seed42` |
| `/extract [run]` | Extract claims from an experiment run | `/extract runs/20260218-baseline-seed42` |
| `/cross-link [claim]` | Find connections, update topic maps | `/cross-link vault/claims/claim-circuit-breakers-dominate.md` |
| `/update [claim]` | Backward pass, update prior claims | `/update vault/claims/claim-transaction-tax.md` |
| `/validate [claim]` | 6-gate quality check | `/validate vault/claims/claim-collusion-wealth-destruction.md` |
| `/pipeline [run]` | Full pipeline in sequence | `/pipeline runs/20260218-baseline-seed42` |

## Navigation & Analysis

| Command | When to Use | Example |
|---------|-------------|---------|
| `/next` | What to work on next | `/next` |
| `/stats` | Vault metrics | `/stats` |
| `/graph` | Knowledge graph analysis | `/graph orphans` |
| `/graph trace [claim]` | Trace evidence chains | `/graph trace circuit-breakers-dominate` |

## Research Growth

| Command | When to Use | Example |
|---------|-------------|---------|
| `/learn [topic]` | Research a topic, grow the vault | `/learn "collusion detection algorithms"` |

## System Evolution

| Command | When to Use | Example |
|---------|-------------|---------|
| `/rethink` | Review accumulated observations/tensions | `/rethink` |
| `/rethink drift` | Check for methodology drift | `/rethink drift` |
| `/remember` | Capture operational friction | `/remember "extractor missed failure mode category"` |

## Plugin Commands (no restart needed)

| Command | When to Use |
|---------|-------------|
| `/arscontexta:ask [question]` | Query methodology KB + local ops/methodology/ |
| `/arscontexta:health` | Vault diagnostics |
| `/arscontexta:architect` | Research-backed evolution advice |
| `/arscontexta:help` | Full command reference |

## Existing Commands (pre-Ars Contexta)

| Command | Description |
|---------|-------------|
| `/vault-init` | Initialize vault structure (legacy) |
| `/synthesize` | Synthesize experiment notes (legacy) |
| `/claim` | Create claim (legacy — prefer /extract) |
| `/verify` | Verify claim (legacy — prefer /validate) |

---

See [[workflows]] for how these chain together.

Topics:
- [[manual]]
