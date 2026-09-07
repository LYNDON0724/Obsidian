#!/bin/bash
# Sync Obsidian notes from the iCloud vault into Quartz's content/ directory.
# Usage: ./sync-content.sh
set -e
VAULT="/Users/jiamingzhang/Library/Mobile Documents/iCloud~md~obsidian/Documents/Default/Set Theory/Radin Forcing"
QUARTZ_DIR="$(cd "$(dirname "$0")" && pwd)"

rsync -a --delete --delete-excluded \
  --include='*/' \
  --include='Chapter*.md' \
  --include='index.md' \
  --exclude='*' \
  --prune-empty-dirs \
  "$VAULT/" "$QUARTZ_DIR/content/"

echo "Synced. To preview locally:  npx quartz build --serve"
