#!/bin/sh
# Check that scripts/check.sh fails when it should. Each case changes a copy of
# the sources in one way that the checks are there to catch.
set -eu
cd "$(dirname "$0")/.."
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fresh() {
  rm -rf "$tmp/work"
  mkdir "$tmp/work"
  cp -R Dahlias.lean Dahlias scripts README.md REVIEW.md "$tmp/work/"
}
fail=0
expect_fail() {
  if "$tmp/work/scripts/check.sh" > "$tmp/out" 2>&1; then
    echo "error: scripts/check.sh passes with $1"; fail=1
  else
    echo "caught: $1"
  fi
}
fresh
"$tmp/work/scripts/check.sh" || { echo 'error: scripts/check.sh fails on the unchanged sources'; exit 1; }

fresh
echo 'axiom audit_backdoor : False' >> "$tmp/work/Dahlias.lean"
expect_fail 'an axiom in the root module'

fresh
echo 'axiom audit_backdoor : False' >> "$tmp/work/Dahlias/Summary.lean"
expect_fail 'an axiom in the generated summary'

fresh
echo 'axiom audit_backdoor : False' >> "$tmp/work/scripts/Fuzz.lean"
expect_fail 'an axiom in a script'

fresh
echo 'theorem audit_backdoor : False := by sorry' >> "$tmp/work/Dahlias/Basic.lean"
expect_fail 'a sorry'

fresh
echo 'theorem audit_backdoor : 1 = 1 := by native_decide' >> "$tmp/work/Dahlias/Basic.lean"
expect_fail 'compiled evaluation outside the test vector checks'

fresh
echo '#print axioms Nat.add_comm' >> "$tmp/work/Dahlias/Summary.lean"
expect_fail 'a command without a guard in the generated summary'

fresh
sed 's/^theorem unforgeable_sqrt /theorem unforgeable_sqrt_changed /' "$tmp/work/REVIEW.md" > "$tmp/review"
cp "$tmp/review" "$tmp/work/REVIEW.md"
expect_fail 'a printed statement that is not in the sources'

fresh
grep -v '^#print axioms Dahlias.Security.unforgeable_sqrt$' "$tmp/work/Dahlias/Summary.lean" > "$tmp/summary"
cp "$tmp/summary" "$tmp/work/Dahlias/Summary.lean"
expect_fail 'a printed theorem whose axioms the summary does not check'

fresh
printf '\nnamespace Other\ntheorem unforgeable_sqrt : True := trivial\nend Other\n' >> "$tmp/work/Dahlias/Tightness.lean"
sed 's/^#print axioms Dahlias.Security.unforgeable_sqrt$/#print axioms Other.unforgeable_sqrt/' "$tmp/work/Dahlias/Summary.lean" > "$tmp/summary"
cp "$tmp/summary" "$tmp/work/Dahlias/Summary.lean"
expect_fail 'a summary that checks another theorem with the same last name'

fresh
echo 'theorem audit_backdoor : False := by sorry' > "$tmp/work/Dahlias/Back door.lean"
expect_fail 'a sorry in a file with a space in its name'

fresh
sed 's/\(Dahlias: \)\([0-9]* definitions, \)/\10\2/' "$tmp/work/Dahlias/Summary.lean" > "$tmp/summary"
cp "$tmp/summary" "$tmp/work/Dahlias/Summary.lean"
expect_fail 'a table of the main results in REVIEW.md that is not the one of the summary'

fresh
python3 - "$tmp/work/REVIEW.md" <<'EOF'
import re, sys
text = open(sys.argv[1]).read()
blocks = [b for b in re.findall(r'```lean\n.*?\n```\n', text, re.S)
          if '\ntheorem strongly_binding ' in b]
assert len(blocks) == 1
open(sys.argv[1], 'w').write(text.replace(blocks[0], ''))
EOF
expect_fail 'a main result whose statement REVIEW.md does not print'

exit $fail
