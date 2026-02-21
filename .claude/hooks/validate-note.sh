#!/usr/bin/env bash
# validate-note.sh — Validate newly written vault notes against schema
# Fires on PostToolUse(Write) hook event

if [ ! -f "vault/.arscontexta" ] && [ ! -f ".arscontexta" ]; then
  exit 0
fi

# Get the file that was just written (passed as env or argument)
FILE="${CLAUDE_TOOL_OUTPUT_FILE:-$1}"

if [ -z "$FILE" ]; then
  exit 0
fi

# Only validate vault notes
if [[ "$FILE" != vault/claims/*.md ]] && \
   [[ "$FILE" != vault/failures/*.md ]] && \
   [[ "$FILE" != vault/governance/*.md ]]; then
  exit 0
fi

echo "Validating: $FILE"

# Check required fields
MISSING=""

if ! grep -q '^description:' "$FILE" 2>/dev/null; then
  MISSING="${MISSING} description"
fi

if ! grep -q '^type:' "$FILE" 2>/dev/null; then
  MISSING="${MISSING} type"
fi

if [ "$FILE" == vault/claims/*.md ]; then
  if ! grep -q '^confidence:' "$FILE" 2>/dev/null; then
    MISSING="${MISSING} confidence"
  fi
  if ! grep -q '^domain:' "$FILE" 2>/dev/null; then
    MISSING="${MISSING} domain"
  fi
fi

if ! grep -q 'Topics:' "$FILE" 2>/dev/null; then
  MISSING="${MISSING} Topics-footer"
fi

if [ -n "$MISSING" ]; then
  echo "WARN: $FILE missing:$MISSING"
  echo "Run /validate $FILE to check all gates."
fi

# Check description length
DESC=$(grep '^description:' "$FILE" 2>/dev/null | head -1 | sed 's/^description: //' | tr -d '"')
if [ ${#DESC} -gt 200 ]; then
  echo "WARN: description exceeds 200 chars (${#DESC} chars) in $FILE"
fi
