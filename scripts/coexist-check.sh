#!/usr/bin/env bash
# Acceptance test: OrdinalAnalysis and goodstein-independence's compat shim can be imported together.
# Compiles scripts/CoexistShim.lean to an olean, then elaborates scripts/CoexistCheck.lean importing both.
set -euo pipefail
cd "$(dirname "$0")/.."
out="$(mktemp -d)"
lake env lean -o "$out/CoexistShim.olean" scripts/CoexistShim.lean
lake env bash -c "LEAN_PATH=\"\$LEAN_PATH:$out\" lean scripts/CoexistCheck.lean"
echo "coexist-check: OK"
