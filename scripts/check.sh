#!/bin/sh
# Source checks that complement the axiom checks in Dahlias/Summary.lean:
# no `sorry`, no new axioms or unsafe code, compiled evaluation
# (`native_decide`, `decide +native`) only in the test vector checks, the
# statements printed in REVIEW.md match the sources, and Dahlias/Summary.lean
# checks the axioms of every result that REVIEW.md prints or the README lists.
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
if grep -rlE 'native|ofReduceBool|reduceBool|trustCompiler' Dahlias --include='*.lean' |
    grep -vE '^Dahlias/(Vectors|Summary)\.lean$'; then
  echo 'error: compiled evaluation outside the test vector checks'; fail=1
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
# Dahlias/Summary.lean must check the axioms of every theorem printed in
# REVIEW.md and of every result in the README's table.
python3 - <<'EOF' || fail=1
import pathlib, re, sys
summary = pathlib.Path('Dahlias/Summary.lean').read_text()
checked = {m.split('.')[-1] for m in re.findall(r'^#print axioms (\S+)', summary, re.M)}
names = []
for block in re.findall(r'```lean\n(.*?)\n```', pathlib.Path('REVIEW.md').read_text(), re.S):
    names += re.findall(r'^(?:theorem|lemma)\s+(\S+)', block, re.M)
table = pathlib.Path('README.md').read_text().split('## Results')[1].split('\n## ')[0]
for line in table.split('\n'):
    if line.startswith('| `'):
        names += re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)`", line.split('|')[1])
missing = sorted({x for x in names if x.split('.')[-1] not in checked})
if missing:
    print('error: Dahlias/Summary.lean does not check the axioms of: ' + ', '.join(missing))
sys.exit(bool(missing))
EOF
exit $fail
