---
description: The vault's self-knowledge — derivation rationale, configuration state, and operational evolution history
type: moc
---

# methodology

This folder records what the SWARM Research OS knows about its own operation — why it was configured this way, what the current state is, and how it has evolved. Meta-skills (/rethink, /arscontexta:architect) read from and write to this folder. /remember captures operational corrections here.

## Derivation Rationale

- [[derivation-rationale]] — Why each configuration dimension was set the way it was

## Configuration State

(Populated by /rethink, /arscontexta:architect)

## Evolution History

(Populated by /rethink, /arscontexta:architect, /arscontexta:reseed)

## How to Use This Folder

```bash
# Browse notes
ls vault/ops/methodology/

# Find active directives
rg '^status: active' vault/ops/methodology/

# Find by category
rg '^category:' vault/ops/methodology/
```

Meta-skills (/rethink, /arscontexta:architect) read from and write to this folder.
/remember captures operational corrections here.
/arscontexta:ask queries the bundled methodology knowledge base (249 research claims) + local notes here.

Topics:
- [[_index]]
