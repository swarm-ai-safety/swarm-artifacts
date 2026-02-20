#!/usr/bin/env bash
#
# SWARM Research OS — Pre-commit hook
#
# Validates vault notes and checks index freshness before each commit.
# Install: cp scripts/pre-commit-hook.sh .git/hooks/pre-commit && chmod +x .git/hooks/pre-commit
# Or:      ln -sf ../../scripts/pre-commit-hook.sh .git/hooks/pre-commit

set -e

ROOT="$(git rev-parse --show-toplevel)"

# Only run checks if vault/ or runs/ files are staged
VAULT_CHANGED=$(git diff --cached --name-only -- 'vault/' 'runs/' 'run-index.yaml' 2>/dev/null | head -1)
if [ -z "$VAULT_CHANGED" ]; then
    exit 0
fi

echo "Running SWARM Research OS pre-commit checks..."

# 1. Validate vault notes
if git diff --cached --name-only -- 'vault/' | grep -q '.'; then
    echo "  Validating vault notes..."
    python "$ROOT/scripts/validate-vault.py" --all
fi

# 2. Check run schemas (only if runs/ changed)
if git diff --cached --name-only -- 'runs/' | grep -q 'run.yaml'; then
    echo "  Validating run schemas..."
    # Only validate changed runs
    for f in $(git diff --cached --name-only -- 'runs/*/run.yaml'); do
        RUN_DIR="$ROOT/$(dirname "$f")"
        python "$ROOT/scripts/validate-run.py" "$RUN_DIR"
    done
fi

# 3. Check index freshness (only if runs/ changed)
if git diff --cached --name-only -- 'runs/' | grep -q '.'; then
    echo "  Checking run index freshness..."
    cp "$ROOT/run-index.yaml" "$ROOT/run-index.yaml.pre-commit-bak"
    python "$ROOT/scripts/index-runs.py" > /dev/null 2>&1
    if ! diff -q "$ROOT/run-index.yaml.pre-commit-bak" "$ROOT/run-index.yaml" > /dev/null 2>&1; then
        echo "  WARNING: run-index.yaml is stale. Staging updated index."
        git add "$ROOT/run-index.yaml"
    fi
    rm -f "$ROOT/run-index.yaml.pre-commit-bak"
fi

echo "Pre-commit checks passed."
