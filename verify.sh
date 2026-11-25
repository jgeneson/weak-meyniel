#!/bin/sh
# Verify both Meyniel proofs using the project's pinned Lean toolchain.
set -eu

case $# in
    0) replay=no ;;
    1) case $1 in
           --replay) replay=yes ;;
           *) echo 'Usage: sh verify.sh [--replay]' >&2; exit 2 ;;
       esac ;;
    *) echo 'Usage: sh verify.sh [--replay]' >&2; exit 2 ;;
esac

script_dir=$(dirname "$0")
CDPATH= cd "$script_dir"
if ! command -v lake >/dev/null 2>&1; then
    echo 'Lake is missing. Install Lean with elan, reopen Terminal, and run this command again.' >&2
    exit 1
fi

echo 'Checking Lean sources for proof placeholders...'
if grep -nE '(^|[^[:alnum:]_])(sorry|admit|sorryAx)([^[:alnum:]_]|$)' Checks.lean Meyniel.lean Meyniel/*.lean; then
    echo 'FAIL: proof placeholder found in the Lean sources.' >&2
    exit 1
else
    scan_status=$?
    if [ "$scan_status" -ne 1 ]; then
        echo 'FAIL: could not scan every Lean source.' >&2
        exit "$scan_status"
    fi
fi

if [ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]; then
    echo 'Fetching the pinned mathlib cache...'
    LEAN_NUM_THREADS=3 lake exe cache get
fi
echo 'Building both proofs...'
LEAN_NUM_THREADS=3 lake build

check_dir=$(mktemp -d "${TMPDIR:-/tmp}/meyniel-verify.XXXXXXXX")
trap 'rm -rf "$check_dir"' 0
trap 'exit 1' HUP INT TERM

echo 'Checking the theorem statements and their axioms...'
if lake env lean Checks.lean > "$check_dir/lean.log" 2>&1; then
    cat "$check_dir/lean.log"
else
    cat "$check_dir/lean.log" >&2
    echo 'FAIL: Lean could not check Checks.lean.' >&2
    exit 1
fi

awk -v quote="'" '
    $1 == "#print" && $2 == "axioms" {
        if (seen[$3]++ || NF != 3) bad = 1
        print quote $3 quote " depends on axioms: [propext, Classical.choice, Quot.sound]"
        count++
    }
    END { exit (bad || count != 12) }
' Checks.lean > "$check_dir/expected" || {
    echo 'FAIL: expected 12 distinct axiom queries in Checks.lean.' >&2
    exit 1
}
awk 'index($0, " depends on axioms:") { print }' "$check_dir/lean.log" > "$check_dir/actual"
if ! diff -u "$check_dir/expected" "$check_dir/actual"; then
    echo 'FAIL: the reported axioms differ from the expected axioms.' >&2
    exit 1
fi

if [ "$replay" = yes ]; then
    echo 'Replaying the compiled project modules through the Lean kernel. This can take several minutes...'
    lake env env LEAN_NUM_THREADS=1 leanchecker -v Meyniel
    echo 'PASS: both proofs built, all 12 axiom checks passed, and kernel replay succeeded.'
else
    echo 'PASS: both proofs built and all 12 axiom checks passed.'
fi
