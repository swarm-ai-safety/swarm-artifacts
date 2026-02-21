#!/usr/bin/env bash
# auto-commit.sh — Auto-commit vault changes after writes
# Fires on PostToolUse(Write) hook event, async

if [ ! -f "vault/.arscontexta" ] && [ ! -f ".arscontexta" ]; then
  exit 0
fi

# Only commit vault and ops changes
if ! git diff --name-only 2>/dev/null | grep -q '^vault/'; then
  exit 0
fi

# Auto-commit with timestamp
TIMESTAMP=$(date +%Y-%m-%dT%H:%M:%S)
git add vault/ 2>/dev/null && \
  git commit -m "vault: auto-commit ${TIMESTAMP}" --quiet 2>/dev/null || true
