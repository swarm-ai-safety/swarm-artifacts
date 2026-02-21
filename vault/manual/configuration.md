---
description: How to adjust SWARM Research OS settings via config.yaml and /arscontexta:architect
type: manual
generated_from: "arscontexta-0.8.0"
---

# Configuration

## Main Config File

`vault/ops/config.yaml` — edit this to adjust behavior.

Key settings:

```yaml
processing:
  depth: standard       # deep | standard | quick
  chaining: suggested   # manual | suggested | automatic
  extraction:
    selectivity: moderate  # strict | moderate | permissive

self_evolution:
  observation_threshold: 10  # /rethink triggered at this count
  tension_threshold: 5        # /rethink triggered at this count
```

**Processing depth:**
- `deep` — fresh context per phase, maximum quality (use for high-stakes claims)
- `standard` — full pipeline, balanced (default)
- `quick` — compressed pipeline (use for backlog catch-up)

**Pipeline chaining:**
- `manual` — each phase outputs next command; you run it
- `suggested` — each phase outputs next command AND queues it (default)
- `automatic` — phases chain without pauses (use for batch processing)

## Extraction Categories

Add custom SWARM extraction categories in config:

```yaml
processing:
  extraction:
    categories:
      - governance-claims
      - adversarial-patterns
      - parameter-sensitivity
      - mechanism-interactions
      - open-questions
      - method-validations
      - failure-modes
      - [your-new-category]
```

## Derivation Config

`vault/ops/derivation.md` — WHY each choice was made (historical record, read-only)
`vault/ops/derivation-manifest.md` — machine-readable config for runtime skills

Do not edit these manually. `/arscontexta:architect` updates them when implementing approved changes.

## Adjusting Thresholds

If observations accumulate too fast:
```yaml
self_evolution:
  observation_threshold: 20  # increase if /rethink fires too frequently
```

If you want more aggressive drift detection:
```yaml
self_evolution:
  observation_threshold: 5
  tension_threshold: 3
```

## Getting Architecture Advice

For significant changes, use `/arscontexta:architect` rather than editing config directly. It provides research-backed reasoning for why a change will or won't help, and shows the interaction constraints with other configuration choices.

---

See [[meta-skills]] for /arscontexta:architect details.

Topics:
- [[manual]]
