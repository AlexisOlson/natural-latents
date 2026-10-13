#!/usr/bin/env bash
# Exercise the source gates in a disposable copy; no Lean build is needed.
set -euo pipefail
repo="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
if command -v python3 >/dev/null 2>&1; then
  python=python3
else
  python=python
fi
tmp="$(mktemp -d "${TMPDIR:-/tmp}/natural-latents-mutations.XXXXXX")"
tmp="$(cd -- "$tmp" && pwd -P)"
cleanup() {
  # Only remove the absolute temporary directory returned by mktemp.
  case "$tmp" in
    /*/natural-latents-mutations.*) rm -rf -- "$tmp" ;;
    *) echo "Refusing to clean unexpected path: $tmp" >&2; return 1 ;;
  esac
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# Copy tracked working files, including any unstaged changes being checked.
git -C "$repo" ls-files -z > "$tmp/tracked-files"
while IFS= read -r -d '' file; do
  mkdir -p -- "$tmp/$(dirname -- "$file")"
  cp -- "$repo/$file" "$tmp/$file"
done < "$tmp/tracked-files"
# Include the source gates even before their first commit.
cp -- "$repo/scripts/trust_scan.sh" "$tmp/scripts/trust_scan.sh"
cp -- "$repo/scripts/check_statement.py" "$tmp/scripts/check_statement.py"
cd -- "$tmp"

# A broken baseline is an infrastructure error, not a caught mutation.
"$python" scripts/check_statement.py
bash scripts/trust_scan.sh > baseline.log 2>&1 || {
  cat baseline.log >&2
  exit 1
}

missed=0
expect_failure() {
  local label="$1" expected="$2" status=0
  shift 2
  "$@" > gate.log 2>&1 || status=$?
  if [[ "$status" -ne 0 ]] && grep -Fq -- "$expected" gate.log; then
    printf 'CAUGHT %s\n' "$label"
  else
    printf 'MISSED %s\n' "$label"
    cat gate.log >&2
    missed=1
  fi
}

statement=NaturalLatents/Statement.lean
cp -- "$statement" statement.original
"$python" - "$statement" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1])
data = p.read_bytes()
assert data.startswith(b"import")
p.write_bytes(b"I" + data[1:])
PY
expect_failure 'statement byte change' 'Statement.lean changed:' \
  "$python" scripts/check_statement.py
cp -- statement.original "$statement"

"$python" - "$statement" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1])
data = p.read_bytes()
assert b"c < 7" in data
p.write_bytes(data.replace(b"c < 7", b"c < 8"))
PY
expect_failure 'weaken c < 7 to c < 8' 'Statement.lean changed:' \
  "$python" scripts/check_statement.py
cp -- statement.original "$statement"

leaf=NaturalLatents/General/Setup.lean
cp -- "$leaf" leaf.original
printf '\naxiom bogus : False\n' >> "$leaf"
expect_failure 'bogus axiom' 'axiom bogus : False' bash scripts/trust_scan.sh
cp -- leaf.original "$leaf"

"$python" - "$leaf" <<'PY'
from pathlib import Path
import sys
p = Path(sys.argv[1])
data = p.read_bytes()
assert b":= by" in data
p.write_bytes(data.replace(b":= by", b":= by sorry;", 1))
PY
expect_failure 'sorry in a proof' ':= by sorry;' bash scripts/trust_scan.sh
cp -- leaf.original "$leaf"

exit "$missed"
