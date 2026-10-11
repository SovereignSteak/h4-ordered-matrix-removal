#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v lake >/dev/null 2>&1 || ! command -v lean >/dev/null 2>&1; then
  echo 'Install the pinned lean-toolchain with elan first.' >&2
  exit 3
fi
echo '[1/5] Fetching pinned mathlib cache'
lake exe cache get
echo '[2/5] Building the primary H4Formal library'
lake build H4Formal
echo '[3/5] Checking the main theorem and axiom audit'
lake env lean Audit.lean
lake env lean ProofAudit.lean
echo '[4/5] Rebuilding the three structural extension modules'
python3 companion/reviewed_extension_core/scripts/build_and_audit.py --clean \
  --dependency-root "$PWD/.lake/packages" --lean "$(command -v lean)"
echo '[5/5] Rebuilding the exact-transversal supplement'
python3 supplements/exact_transversal/scripts/build_and_audit.py \
  --primary-root "$PWD" --lean "$(command -v lean)"
echo 'The specified Lean build and audits have completed successfully.'
