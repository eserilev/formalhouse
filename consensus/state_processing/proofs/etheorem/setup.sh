#!/usr/bin/env bash
# Prepares the Etheorem dependency for `lake build`.
#
# 1. Fetch the Lake packages. The Etheorem fork at the pinned commit already builds on our
#    Lean version (see README.md).
# 2. Vendor the C libraries that the Etheorem FFI packages link. The revisions are the
#    pins in Etheorem's Justfile. ISA-L needs `nasm`.
set -euo pipefail

cd "$(dirname "$0")/.."
lake env true

pkg=.lake/packages/EthCLSpecs
vendor() {
  local dir="$pkg/packages/hazmat/$1" url=$2 tag=$3 rev=$4
  if [ "$(git -C "$dir" rev-parse HEAD 2>/dev/null || true)" != "$rev" ]; then
    rm -rf "$dir"
    git -c advice.detachedHead=false clone -q --depth 1 --branch "$tag" "$url" "$dir"
  fi
  if [ "$(git -C "$dir" rev-parse HEAD)" != "$rev" ]; then
    echo "$url $tag is not at $rev" >&2
    exit 1
  fi
  printf '%s\n' "$rev" > "$dir/.pin"
}

vendor LeanHazmatBls/vendor/blst https://github.com/supranational/blst \
  v0.3.16 e7f90de551e8df682f3cc99067d204d8b90d27ad
vendor LeanHazmatKzg/vendor/c-kzg-4844 https://github.com/ethereum/c-kzg-4844 \
  v2.1.7 9f4bcc83cbb17b3dbc3432de7320790968143ab9
vendor LeanHazmatSha256/vendor/isa-l_crypto https://github.com/intel/isa-l_crypto \
  v2.26.1 c353c2d021c03cfc6180ddf9e28a24b3b61e9760
