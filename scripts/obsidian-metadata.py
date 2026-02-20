#!/usr/bin/env python3
"""Add Obsidian-compatible metadata to vault notes for better graph rendering.

Enriches YAML frontmatter with aliases, cssclasses, tags, and graph-group
fields without replacing existing content.

Usage:
    python scripts/obsidian-metadata.py              # enrich all vault notes
    python scripts/obsidian-metadata.py --dry-run    # preview changes
    python scripts/obsidian-metadata.py --dir vault/claims  # one directory
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Any

import yaml

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parent.parent
VAULT_DIR = ROOT / "vault"

# Directories to process and their note-type classification
NOTE_DIRS: dict[str, str] = {
    "claims": "claim",
    "experiments": "experiment",
    "sweeps": "sweep",
    "governance": "governance",
    "topologies": "topology",
    "failures": "failure",
    "methods": "method",
}

# Directories and files to skip
SKIP_DIRS = {"templates"}
SKIP_FILES = {"_index.md"}

# ---------------------------------------------------------------------------
# Frontmatter parsing
# ---------------------------------------------------------------------------

_FM_RE = re.compile(r"\A---\r?\n(.*?\r?\n)---\r?\n?", re.DOTALL)
_TOPICS_RE = re.compile(r"<!--\s*topics:\s*(.*?)\s*-->")


def parse_note(text: str) -> tuple[dict[str, Any] | None, str]:
    """Split a note into (frontmatter_dict, body).

    Returns (None, full_text) when frontmatter is missing or malformed.
    """
    m = _FM_RE.match(text)
    if not m:
        return None, text
    try:
        fm = yaml.safe_load(m.group(1))
        if not isinstance(fm, dict):
            return None, text
    except yaml.YAMLError:
        return None, text
    body = text[m.end():]
    return fm, body


def reassemble(fm: dict[str, Any], body: str) -> str:
    """Serialize frontmatter + body back into a markdown note."""
    dumped = yaml.dump(
        fm,
        default_flow_style=False,
        allow_unicode=True,
        sort_keys=False,
        width=120,
    )
    return f"---\n{dumped}---\n{body}"


# ---------------------------------------------------------------------------
# Topics extraction
# ---------------------------------------------------------------------------


def extract_topics(body: str) -> list[str]:
    """Extract tags from ``<!-- topics: a, b, c -->`` comments in the body."""
    tags: list[str] = []
    for m in _TOPICS_RE.finditer(body):
        for raw in m.group(1).split(","):
            tag = raw.strip()
            if tag:
                tags.append(tag)
    return tags


# ---------------------------------------------------------------------------
# Alias generation
# ---------------------------------------------------------------------------


def _slug_from_filename(path: Path) -> str:
    """Return the filename stem (without extension)."""
    return path.stem


def _short_description(desc: str, max_words: int = 6) -> str:
    """Return first *max_words* words of a description, kebab-cased."""
    words = re.sub(r"[^a-zA-Z0-9\s-]", "", desc).split()
    return "-".join(words[:max_words]).lower()


def generate_aliases(
    note_type: str,
    fm: dict[str, Any],
    path: Path,
) -> list[str]:
    """Build a list of alias strings based on note type."""
    aliases: list[str] = []

    if note_type == "claim":
        # kebab-case filename without 'claim-' prefix
        stem = path.stem
        if stem.startswith("claim-"):
            aliases.append(stem[len("claim-"):])
        # short form of description
        desc = fm.get("description", "")
        if desc:
            short = _short_description(desc)
            if short and short not in aliases:
                aliases.append(short)

    elif note_type == "experiment":
        run_id = fm.get("run_id", "")
        if run_id:
            aliases.append(run_id)
        # slug: filename stem (which often equals run_id but may differ)
        slug = _slug_from_filename(path)
        if slug and slug != run_id:
            aliases.append(slug)

    elif note_type == "sweep":
        param = fm.get("parameter", "")
        if param:
            aliases.append(param)
        # also add the filename stem as a fallback alias
        slug = _slug_from_filename(path)
        if slug and slug != param:
            aliases.append(slug)

    else:
        # governance / topology / failure / method
        aliases.append(_slug_from_filename(path))

    return aliases


# ---------------------------------------------------------------------------
# CSS classes generation
# ---------------------------------------------------------------------------


def generate_cssclasses(note_type: str, fm: dict[str, Any]) -> list[str]:
    """Build cssclasses list based on note type and frontmatter fields."""
    if note_type == "claim":
        confidence = fm.get("confidence", "unknown")
        return ["claim", f"claim-{confidence}"]

    if note_type == "experiment":
        exp_type = fm.get("experiment_type", "unknown")
        return ["experiment", f"experiment-{exp_type}"]

    if note_type == "sweep":
        return ["sweep-summary"]

    # governance, topology, failure, method
    return [note_type]


# ---------------------------------------------------------------------------
# Core enrichment
# ---------------------------------------------------------------------------


def enrich_frontmatter(
    fm: dict[str, Any],
    body: str,
    note_type: str,
    path: Path,
) -> dict[str, Any]:
    """Add Obsidian metadata fields to *fm* (in-place) and return it.

    Only adds fields that do not already exist, or merges into existing lists.
    """
    # --- aliases ---
    new_aliases = generate_aliases(note_type, fm, path)
    existing_aliases: list[str] = fm.get("aliases", [])
    if not isinstance(existing_aliases, list):
        existing_aliases = [existing_aliases] if existing_aliases else []
    merged_aliases = list(existing_aliases)
    for a in new_aliases:
        if a not in merged_aliases:
            merged_aliases.append(a)
    if merged_aliases:
        fm["aliases"] = merged_aliases

    # --- cssclasses ---
    if "cssclasses" not in fm:
        fm["cssclasses"] = generate_cssclasses(note_type, fm)

    # --- tags (merge from <!-- topics: ... -->) ---
    topic_tags = extract_topics(body)
    existing_tags: list[str] = fm.get("tags", [])
    if not isinstance(existing_tags, list):
        existing_tags = [existing_tags] if existing_tags else []
    merged_tags = list(existing_tags)
    for t in topic_tags:
        if t not in merged_tags:
            merged_tags.append(t)
    if merged_tags:
        fm["tags"] = merged_tags

    # --- graph-group ---
    if "graph-group" not in fm:
        fm["graph-group"] = note_type

    return fm


# ---------------------------------------------------------------------------
# File processing
# ---------------------------------------------------------------------------


def classify_note(path: Path) -> str | None:
    """Determine the note type from its vault subdirectory.

    Returns None if the file should be skipped.
    """
    try:
        rel = path.relative_to(VAULT_DIR)
    except ValueError:
        return None

    parts = rel.parts
    if not parts:
        return None

    top_dir = parts[0]

    if top_dir in SKIP_DIRS:
        return None

    return NOTE_DIRS.get(top_dir)


def should_skip(path: Path) -> bool:
    """Return True for files that must not be processed."""
    if path.name in SKIP_FILES:
        return True
    try:
        rel = path.relative_to(VAULT_DIR)
    except ValueError:
        return True
    if rel.parts and rel.parts[0] in SKIP_DIRS:
        return True
    return False


def process_file(path: Path, *, dry_run: bool = False) -> bool:
    """Enrich a single vault note. Returns True if the file was modified."""
    if should_skip(path):
        return False

    note_type = classify_note(path)
    if note_type is None:
        return False

    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        print(f"  WARN: cannot read {path}: {exc}", file=sys.stderr)
        return False

    fm, body = parse_note(text)
    if fm is None:
        print(f"  SKIP (no valid frontmatter): {path}")
        return False

    # Snapshot original keys to detect changes
    original_keys = set(fm.keys())
    original_aliases = list(fm.get("aliases", []))
    original_tags = list(fm.get("tags", []))

    enrich_frontmatter(fm, body, note_type, path)

    # Detect whether anything actually changed
    new_keys = set(fm.keys())
    changed = (
        new_keys != original_keys
        or fm.get("aliases", []) != original_aliases
        or fm.get("tags", []) != original_tags
    )

    if not changed:
        return False

    new_text = reassemble(fm, body)

    if dry_run:
        added = new_keys - original_keys
        alias_diff = set(fm.get("aliases", [])) - set(original_aliases)
        tag_diff = set(fm.get("tags", [])) - set(original_tags)
        parts: list[str] = []
        if added:
            parts.append(f"add fields: {', '.join(sorted(added))}")
        if alias_diff:
            parts.append(f"add aliases: {', '.join(sorted(alias_diff))}")
        if tag_diff:
            parts.append(f"add tags: {', '.join(sorted(tag_diff))}")
        detail = "; ".join(parts) if parts else "no changes"
        print(f"  DRY-RUN {path.relative_to(ROOT)}  [{detail}]")
    else:
        path.write_text(new_text, encoding="utf-8")
        print(f"  ENRICHED {path.relative_to(ROOT)}")

    return True


# ---------------------------------------------------------------------------
# Directory collection
# ---------------------------------------------------------------------------


def collect_notes(base: Path) -> list[Path]:
    """Recursively collect .md files under *base*, sorted for determinism."""
    if not base.is_dir():
        print(f"ERROR: {base} is not a directory", file=sys.stderr)
        sys.exit(1)
    return sorted(base.rglob("*.md"))


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Add Obsidian-compatible metadata to vault notes.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Preview changes without writing files.",
    )
    parser.add_argument(
        "--dir",
        type=Path,
        default=None,
        metavar="DIR",
        help="Process only notes in DIR (e.g. vault/claims).",
    )
    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()

    if args.dir is not None:
        target = args.dir if args.dir.is_absolute() else ROOT / args.dir
    else:
        target = VAULT_DIR

    if not target.exists():
        print(f"ERROR: path does not exist: {target}", file=sys.stderr)
        sys.exit(1)

    notes = collect_notes(target)
    if not notes:
        print("No .md files found.")
        return

    mode = "DRY-RUN" if args.dry_run else "ENRICH"
    print(f"[{mode}] Scanning {len(notes)} note(s) under {target.relative_to(ROOT)}\n")

    modified = 0
    skipped = 0
    for note in notes:
        try:
            if process_file(note, dry_run=args.dry_run):
                modified += 1
            else:
                skipped += 1
        except Exception as exc:
            print(f"  ERROR processing {note}: {exc}", file=sys.stderr)
            skipped += 1

    print(f"\nDone. {modified} enriched, {skipped} skipped/unchanged.")


if __name__ == "__main__":
    main()
