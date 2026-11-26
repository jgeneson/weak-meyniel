#!/bin/sh
# Run from any directory. The two compared solutions are compiled apart from Challenge.
set -eu

case "${1:-}" in
    '') replay=no ;;
    --replay) replay=yes ;;
    *) echo 'Usage: sh verify.sh [--replay]' >&2; exit 2 ;;
esac
if [ "$#" -gt 1 ]; then
    echo 'Usage: sh verify.sh [--replay]' >&2
    exit 2
fi

script_dir=$(dirname "$0")
CDPATH= cd "$script_dir"
if ! command -v lake >/dev/null 2>&1; then
    echo 'Lake is missing. Install Lean with elan and reopen the terminal.' >&2
    exit 1
fi

echo 'Checking the two Challenge placeholders and scanning all other Lean sources...'
awk '
    /^theorem / { name = $2 }
    /(^|[^[:alnum:]_])(sorry|admit|sorryAx)([^[:alnum:]_]|$)/ {
        if ($0 !~ /^[[:space:]]*sorry[[:space:]]*$/ || (name != "twoThirds" && name != "soft")) {
            print FILENAME ":" FNR ": unexpected placeholder: " $0
            bad = 1
        }
        count[name]++
    }
    END {
        if (count["twoThirds"] != 1 || count["soft"] != 1) {
            print "Expected one statement placeholder per advertised Challenge theorem."
            bad = 1
        }
        exit bad
    }
' Challenge.lean
find . \( -name .git -o -name .lake \) -prune -o -type f -name '*.lean' ! -path './Challenge.lean' -exec awk '
    /(^|[^[:alnum:]_])(sorry|admit|sorryAx)([^[:alnum:]_]|$)/ {
        print FILENAME ":" FNR ": proof placeholder: " $0
        bad = 1
    }
    END { exit bad }
' {} +

if [ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]; then
    echo 'Fetching the pinned mathlib cache...'
    LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-3} lake exe cache get
fi
echo 'Building the proof library, Challenge, and Solution...'
LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-3} lake build Meyniel Challenge Solution

check_dir=$(mktemp -d "${TMPDIR:-/tmp}/meyniel-verify.XXXXXXXX")
trap 'rm -rf "$check_dir"' 0
trap 'exit 1' HUP INT TERM

# Preserve Checks.lean's imports, elaboration checks, and diagnostic output.
# Import Solution in this temporary module, independently of the Challenge.
awk '/^module$/ { print; print "import Lean"; print "import Solution"; next } { print }' Checks.lean > "$check_dir/Audit.lean"
cat >> "$check_dir/Audit.lean" <<'LEAN'

open Lean Elab Command in
run_cmd do
  let config ← IO.ofExcept (Json.parse (← IO.FS.readFile "comparator.json"))
  let names ← IO.ofExcept (config.getObjValAs? (List String) "theorem_names")
  let permitted ← IO.ofExcept (config.getObjValAs? (List String) "permitted_axioms")
  let expected := ["PalomarMeyniel.twoThirds", "PalomarMeyniel.soft"]
  unless names.length == expected.length && expected.all names.contains do
    throwError "Unexpected Comparator theorem list: {names}"
  let standard := ["propext", "Classical.choice", "Quot.sound"]
  unless permitted.length == standard.length && standard.all permitted.contains do
    throwError "Unexpected Comparator axiom list: {permitted}"
  let previous : List Name := [
LEAN
awk '
    $1 == "#print" && $2 == "axioms" {
        if (NF != 3 || seen[$3]++) bad = 1
        print "    ``" $3 ","
        count++
    }
    END { exit (bad || count != 12) }
' Checks.lean >> "$check_dir/Audit.lean" || {
    echo 'FAIL: expected 12 distinct axiom queries in Checks.lean.' >&2
    exit 1
}
cat >> "$check_dir/Audit.lean" <<'LEAN'
  ]
  for name in previous ++ names.map String.toName do
    unless wasOriginallyTheorem (← getEnv) name do
      throwError "Expected a proved theorem named {name}"
    let used ← collectAxioms name
    let unexpected := used.filter (fun ax => !permitted.contains ax.toString)
    unless unexpected.isEmpty do
      throwError "Forbidden axioms in {name}: {unexpected}"
    logInfo m!"{name} uses {used}"
LEAN

echo 'Checking the 12 project declarations and both advertised Solution proofs...'
lake env lean --stdin < "$check_dir/Audit.lean"

if [ "$replay" = yes ]; then
    echo 'Replaying the compiled Meyniel and Solution declarations through the Lean kernel...'
    LEAN_NUM_THREADS=1 lake env leanchecker -v Meyniel Solution
fi
echo 'PASS: the library and both statement modules built; all 14 proved declarations satisfy the axiom allowlist.'
