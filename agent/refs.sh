#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p refs
while read -r name url sha; do
    [ "$(cat "refs/$name.sha" 2>/dev/null)" = "$sha" ] && continue
    tmp=$(mktemp -d refs/.tmp.XXXXXX)
    git -C "$tmp" init -q
    git -C "$tmp" fetch -q --depth 1 "$url" "$sha"
    git -C "$tmp" checkout -q FETCH_HEAD
    rm -rf "$tmp/.git" "refs/$name"
    mv "$tmp" "refs/$name"
    echo "$sha" > "refs/$name.sha"
done < refs.txt
