#!/usr/bin/env python3
"""
Validate vault notes against Research OS conventions.

Usage:
    python scripts/validate-vault.py --claims        # validate claim cards
    python scripts/validate-vault.py --experiments   # validate experiment notes
    python scripts/validate-vault.py --index         # check index consistency
    python scripts/validate-vault.py --all           # validate everything
"""

import argparse
import re
import sys
from pathlib import Path

import yaml

try:
    import jsonschema
except ImportError:
    print("Install jsonschema: pip install jsonschema")
    sys.exit(1)

ROOT = Path(__file__).parent.parent
VAULT_DIR = ROOT / "vault"
SCHEMAS_DIR = ROOT / "schemas"
RUNS_DIR = ROOT / "runs"


def load_schema(name: str) -> dict:
    path = SCHEMAS_DIR / name
    if not path.exists():
        return {}
    with open(path) as f:
        return yaml.safe_load(f)


def parse_frontmatter(path: Path) -> dict | None:
    """Extract YAML frontmatter from a markdown file."""
    text = path.read_text(encoding="utf-8")
    match = re.match(r"^---\n(.+?)\n---", text, re.DOTALL)
    if not match:
        return None
    data = yaml.safe_load(match.group(1))
    if data is None:
        return None
    # YAML parses bare dates (2026-02-18) as datetime.date objects.
    # Convert to strings so they pass JSON Schema validation.
    from datetime import date, datetime
    for key in ("created", "updated"):
        if key in data and isinstance(data[key], (date, datetime)):
            data[key] = data[key].isoformat()
    return data


def validate_claims() -> list[str]:
    """Validate all claim cards in vault/claims/."""
    errors = []
    claims_dir = VAULT_DIR / "claims"
    if not claims_dir.exists():
        return ["vault/claims/ directory does not exist"]

    claim_schema = load_schema("claim.schema.yaml")
    claim_files = sorted(claims_dir.glob("*.md"))

    if not claim_files:
        errors.append("No claim cards found in vault/claims/")
        return errors

    for path in claim_files:
        fm = parse_frontmatter(path)
        if fm is None:
            errors.append(f"{path.name}: missing YAML frontmatter")
            continue

        # Schema validation
        if claim_schema:
            try:
                jsonschema.validate(fm, claim_schema)
            except jsonschema.ValidationError as e:
                errors.append(f"{path.name}: {e.message}")

        # Kernel invariants
        desc = fm.get("description", "")
        if len(desc) > 200:
            errors.append(f"{path.name}: description exceeds 200 chars ({len(desc)})")
        if desc.endswith("."):
            errors.append(f"{path.name}: description has trailing period")

        if fm.get("type") != "claim":
            errors.append(f"{path.name}: type must be 'claim', got '{fm.get('type')}'")

        # Confidence must be valid
        valid_confidence = {"high", "medium", "low", "contested"}
        if fm.get("confidence") not in valid_confidence:
            errors.append(f"{path.name}: invalid confidence '{fm.get('confidence')}'")

        # Status must be valid
        valid_status = {"active", "weakened", "superseded", "retracted"}
        if fm.get("status") not in valid_status:
            errors.append(f"{path.name}: invalid status '{fm.get('status')}'")

        # Evidence provenance
        evidence = fm.get("evidence", {})
        for entry in evidence.get("supporting", []):
            run_id = entry.get("run")
            if run_id and not (RUNS_DIR / run_id).exists():
                errors.append(f"{path.name}: supporting evidence references non-existent run '{run_id}'")

        for entry in evidence.get("weakening", []):
            run_id = entry.get("run")
            if run_id and not (RUNS_DIR / run_id).exists():
                errors.append(f"{path.name}: weakening evidence references non-existent run '{run_id}'")

        # Topics footer — accept both HTML comment and visible format
        text = path.read_text(encoding="utf-8")
        if "<!-- topics:" not in text and "Topics:" not in text:
            errors.append(f"{path.name}: missing topics footer")

    print(f"Validated {len(claim_files)} claim cards, {len(errors)} errors")
    return errors


def validate_experiments() -> list[str]:
    """Validate experiment notes in vault/experiments/."""
    errors = []
    exp_dir = VAULT_DIR / "experiments"
    if not exp_dir.exists():
        return []  # not an error if no experiments yet

    exp_files = sorted(exp_dir.glob("*.md"))
    for path in exp_files:
        fm = parse_frontmatter(path)
        if fm is None:
            errors.append(f"{path.name}: missing YAML frontmatter")
            continue

        # Required fields
        for field in ["description", "type", "status", "run_id"]:
            if field not in fm:
                errors.append(f"{path.name}: missing required field '{field}'")

        # Description invariant
        desc = fm.get("description", "")
        if len(desc) > 200:
            errors.append(f"{path.name}: description exceeds 200 chars ({len(desc)})")
        if desc.endswith("."):
            errors.append(f"{path.name}: description has trailing period")

        # Run reference
        run_id = fm.get("run_id")
        if run_id and not (RUNS_DIR / run_id).exists():
            errors.append(f"{path.name}: references non-existent run '{run_id}'")

        # Topics footer — accept both HTML comment and visible format
        text = path.read_text(encoding="utf-8")
        if "<!-- topics:" not in text and "Topics:" not in text:
            errors.append(f"{path.name}: missing topics footer")

    print(f"Validated {len(exp_files)} experiment notes, {len(errors)} errors")
    return errors


def validate_index() -> list[str]:
    """Check index consistency."""
    errors = []
    index_path = VAULT_DIR / "_index.md"

    if not index_path.exists():
        return ["vault/_index.md does not exist"]

    index_text = index_path.read_text(encoding="utf-8")

    # Check that all claim files are referenced in the index
    # Claims are curated and must be individually listed
    claims_dir = VAULT_DIR / "claims"
    if claims_dir.exists():
        for claim_path in sorted(claims_dir.glob("*.md")):
            claim_name = claim_path.stem
            if claim_name not in index_text:
                errors.append(f"Claim '{claim_name}' not referenced in _index.md")

    # For experiments, a directory-level reference is sufficient
    # (listing 100+ auto-generated notes individually is not useful)
    exp_dir = VAULT_DIR / "experiments"
    if exp_dir.exists() and list(exp_dir.glob("*.md")):
        if "vault/experiments/" not in index_text and "experiments/" not in index_text:
            errors.append("Experiments directory not referenced in _index.md")

    # Check governance, topology, and other curated directories
    for subdir in ["governance", "topologies"]:
        dir_path = VAULT_DIR / subdir
        if not dir_path.exists():
            continue
        for md in sorted(dir_path.glob("*.md")):
            if md.stem not in index_text:
                errors.append(f"Note '{md.stem}' ({subdir}) not referenced in _index.md")

    print(f"Index consistency: {len(errors)} errors")
    return errors


def main():
    parser = argparse.ArgumentParser(description="Validate vault notes")
    parser.add_argument("--claims", action="store_true", help="Validate claim cards")
    parser.add_argument("--experiments", action="store_true", help="Validate experiment notes")
    parser.add_argument("--index", action="store_true", help="Check index consistency")
    parser.add_argument("--all", action="store_true", help="Validate everything")
    args = parser.parse_args()

    if not any([args.claims, args.experiments, args.index, args.all]):
        parser.print_help()
        return

    all_errors = []

    if args.claims or args.all:
        all_errors.extend(validate_claims())

    if args.experiments or args.all:
        all_errors.extend(validate_experiments())

    if args.index or args.all:
        all_errors.extend(validate_index())

    if all_errors:
        print(f"\n{'=' * 40}")
        print(f"Total: {len(all_errors)} error(s)")
        for e in all_errors:
            print(f"  - {e}")
        sys.exit(1)
    else:
        print(f"\n{'=' * 40}")
        print("All vault validations passed")


if __name__ == "__main__":
    main()
