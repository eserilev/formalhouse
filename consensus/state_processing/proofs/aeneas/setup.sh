#!/usr/bin/env bash
# Applies `discriminant-instance-name.patch` to the Aeneas Lean library.
#
# The `discriminant` attribute makes an anonymous instance at the root namespace, so its name
# comes from the short type name only. `CacheProofs.Generated` and `EpochProofs.Generated` both
# translate `safe_arith::ArithError`, and both get `instDiscriminantArithErrorIsize`. Lean then
# refuses to load the two files together. The patch names the instance after the full type
# name. It changes no definition and no proof.
set -euo pipefail

cd "$(dirname "$0")/.."
lake env true

pkg=.lake/packages/aeneas
patch="$PWD/aeneas/discriminant-instance-name.patch"

if git -C "$pkg" apply --reverse --check "$patch" 2>/dev/null; then
  echo "Aeneas patch already applied"
else
  git -C "$pkg" apply "$patch"
  echo "Aeneas patch applied"
fi
