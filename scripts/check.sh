#!/bin/sh
# Source checks that complement the axiom checks in Dahlias/Summary.lean:
# no `sorry`, no new axioms or unsafe code, and `native_decide` only in the
# test vector checks.
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
exit $fail
