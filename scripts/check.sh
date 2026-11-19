#!/bin/sh
# Source checks that complement the axiom checks in Dahlias/Summary.lean:
# no `sorry`, no new axioms or unsafe code, `native_decide` only in the test
# vector checks, and the statements printed in REVIEW.md match the sources.
set -eu
cd "$(dirname "$0")/.."
fail=0
if grep -rnwE 'sorry|admit' Dahlias --include='*.lean' | grep -v '^Dahlias/Summary.lean:'; then
  echo 'error: sorry or admit found'; fail=1
fi
if grep -rnwE 'axiom|unsafe|implemented_by|extern|skipKernelTC' Dahlias --include='*.lean' |
    grep -v '^Dahlias/Summary.lean:'; then
  echo 'error: axiom, unsafe code or kernel bypass found'; fail=1
fi
if grep -rlw 'native_decide' Dahlias --include='*.lean' |
    grep -vE '^Dahlias/(Vectors|Summary)\.lean$'; then
  echo 'error: native_decide outside the test vector checks'; fail=1
fi
# Every Lean code block in REVIEW.md must be in the sources word for word, and
# the section must be what scripts/gen_review.py prints.
python3 - <<'EOF' || fail=1
import pathlib, re, sys
sources = [p.read_text() for p in pathlib.Path('Dahlias').rglob('*.lean')]
bad = 0
for block in re.findall(r'```lean\n(.*?)\n```', pathlib.Path('REVIEW.md').read_text(), re.S):
    if not any(block in s for s in sources):
        print('error: REVIEW.md block not found in the sources:\n' + block)
        bad = 1
sys.exit(bad)
EOF
python3 scripts/gen_review.py --check || fail=1
exit $fail
