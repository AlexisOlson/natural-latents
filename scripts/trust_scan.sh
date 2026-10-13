#!/usr/bin/env bash
# Scan the library and audit with the same trust boundary locally and in CI.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

status=0
grep -rn -E '\b(sorry|admit|native_decide|unsafe|bv_decide|implemented_by|extern|skipKernelTC)\b|decide \+native|^\s*(local |scoped )?(syntax|macro|macro_rules|elab|elab_rules|notation|infix|infixl|infixr|prefix|postfix)\b|^\s*(@\[[^]]*\]\s*)?(private |protected |noncomputable )*axiom\b' \
  --include='*.lean' NaturalLatents NaturalLatents.lean Verify.lean || status=$?
case "$status" in
  1) echo "trust scan: clean" ;;
  0) echo "::error::trust shortcut found above"; exit 1 ;;
  *) echo "::error::grep failed with status $status"; exit 1 ;;
esac
