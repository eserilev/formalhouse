#!/usr/bin/env bash
# Prepares the Lake dependencies for `lake build`. CI runs this through `.github/proofs.json`.
set -euo pipefail

cd "$(dirname "$0")"
./etheorem/setup.sh
./aeneas/setup.sh
