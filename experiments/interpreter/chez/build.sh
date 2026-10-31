#!/bin/sh
# Run from repository root. Public downloads; no sibling mutation or install.
set -eu
SOURCE=${1:-../ChezScheme}
WORK=${2:-/tmp/klara-chez-reproduce}
mkdir -p "$WORK/source"
git -C "$SOURCE" archive fae51c278e4cb43d89bce43172c5c74ac6b23343 | tar -x -C "$WORK/source"
while read -r name repo rev; do
  curl -fLsS "https://codeload.github.com/$repo/tar.gz/$rev" -o "$WORK/$name.tar.gz"
  tar -xzf "$WORK/$name.tar.gz" --strip-components=1 -C "$WORK/source/$name"
done <<'DEPS'
zuo racket/zuo a288cbfe350403899311ca7d8267d570e781ed2c
nanopass nanopass/nanopass-framework-scheme bb47b5695a5bffdfd4d99ec9b349f0864b08e0d4
zlib madler/zlib da607da739fa6047df13e66a2af6b8bec7c2a498
lz4 lz4/lz4 ebb370ca83af193212df4dcbadcc5d87bc0de2f0
stex dybvig/stex afa607564a5662ffd748e824801277a6b5a3d11c
DEPS
cd "$WORK/source"
./configure --disable-curses --disable-x11 --installprefix="$WORK/install"
make -j2
