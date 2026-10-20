#!/usr/bin/env bash
# Clones each repo in SOURCES.toml into third_party/<repo basename> at its pinned
# rev (a shallow fetch of exactly that commit). Idempotent: a checkout already at
# the rev is left alone.
#
#   scripts/fetch-sources.sh            # every source
#   scripts/fetch-sources.sh circuits   # only the named [sections]
#
# RAND_SOURCES_LOCAL_<SECTION>=/path/to/repo (e.g. RAND_SOURCES_LOCAL_CIRCUITS)
# fetches from a local clone instead of the URL; the rev is still checked.
set -euo pipefail
cd "$(dirname "$0")/.."

# section repo rev, one line per [section]
entries=$(awk '
  /^\[/ { if (name != "") print name, repo, rev; gsub(/[][]/, ""); name = $0; repo = ""; rev = ""; next }
  /^repo[[:space:]]*=/ { sub(/^[^"]*"/, ""); sub(/".*$/, ""); repo = $0 }
  /^rev[[:space:]]*=/  { sub(/^[^"]*"/, ""); sub(/".*$/, ""); rev = $0 }
  END { if (name != "") print name, repo, rev }
' SOURCES.toml)

mkdir -p third_party
while read -r name repo rev; do
  [ -n "$name" ] || continue
  if [ "$#" -gt 0 ]; then
    want=0
    for a in "$@"; do [ "$a" = "$name" ] && want=1; done
    [ "$want" = 1 ] || continue
  fi
  case "$rev" in
    *[!0-9a-f]*|"") echo "fetch-sources: $name: rev '$rev' is not a full commit hash" >&2; exit 1 ;;
  esac
  [ "${#rev}" = 40 ] || { echo "fetch-sources: $name: rev must be 40 hex digits" >&2; exit 1; }
  dir="third_party/$(basename "$repo" .git)"
  var="RAND_SOURCES_LOCAL_$(echo "$name" | tr '[:lower:]-' '[:upper:]_')"
  url="${!var:-$repo}"
  if [ -d "$url" ]; then url="file://$(cd "$url" && pwd)"; fi

  if [ -d "$dir/.git" ] && [ "$(git -C "$dir" rev-parse HEAD 2>/dev/null)" = "$rev" ]; then
    echo "fetch-sources: $name already at $rev ($dir)"
    continue
  fi
  echo "fetch-sources: $name $rev from $url -> $dir"
  [ -d "$dir/.git" ] || git init -q "$dir"
  git -C "$dir" fetch -q --depth 1 "$url" "$rev"
  git -C "$dir" -c advice.detachedHead=false checkout -q --force "$rev"
  got=$(git -C "$dir" rev-parse HEAD)
  [ "$got" = "$rev" ] || { echo "fetch-sources: $name: checked out $got, wanted $rev" >&2; exit 1; }
done <<< "$entries"
