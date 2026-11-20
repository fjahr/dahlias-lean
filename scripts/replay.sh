#!/bin/sh
# Replay in the kernel, without the elaborator, every project module and every
# module of taproot-lean that the project imports.
#
# `lake env leanchecker Dahlias` replays all modules in parallel, and each one
# loads Mathlib (about 5 GB). This script runs one process per module instead.
# The root module `Dahlias` only has imports, and its name is a prefix of every
# other module, so it is skipped.
set -eu
cd "$(dirname "$0")/.."
# The taproot-lean modules in the import closure of the project.
taproot() {
  todo=$(grep -rhoE '^import Taproot\.[A-Za-z0-9_.]+' Dahlias | sed 's/^import //' | sort -u)
  seen=""
  while [ -n "$todo" ]; do
    next=""
    for m in $todo; do
      case " $seen " in *" $m "*) continue ;; esac
      seen="$seen $m"
      f=".lake/packages/TaprootLean/$(echo "$m" | tr . /).lean"
      next="$next $(grep -oE '^import Taproot\.[A-Za-z0-9_.]+' "$f" | sed 's/^import //' | tr '\n' ' ')"
    done
    todo=$next
  done
  echo "$seen" | tr ' ' '\n' | sort -u | sed '/^$/d'
}
mods="$(taproot) $(find Dahlias -name '*.lean' | sort | sed 's/\.lean$//' | tr / .)"
# `scripts/replay.sh --list` prints the modules and replays nothing.
if [ "${1:-}" = "--list" ]; then
  echo "$mods" | tr ' ' '\n'
  exit 0
fi
for mod in $mods; do
  echo "replay $mod"
  lake env leanchecker "$mod"
done
