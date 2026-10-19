#!/usr/bin/env bash
# The fast checks around the parser -> OCaml producer -> Lean pipeline:
# front-end types, JSON field names, assertions, documents and the rule
# inventory. The pipeline cases and controls are pipeline/test.mts.
# Usage: test-all.sh
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO" || exit 1

if [ $# -gt 0 ]; then
  echo "Unknown argument: $1"
  exit 2
fi

WORK="$(mktemp -d)"
passed=0
failed=0
completed=0
started_at=$SECONDS

# Match the example report; preserve readable plain text in logs and NO_COLOR.
status_line() {
  local color="$1"
  shift
  if [ -t 1 ] && [ "${TERM:-}" != dumb ] && [ -z "${NO_COLOR:-}" ]; then
    printf '\033[%sm%s\033[0m\n' "$color" "$*"
  else
    printf '%s\n' "$*"
  fi
}

# Count test executables, not their differently formatted internal assertions.
# An early setup/build failure must still produce a failed, incomplete summary.
finish() {
  local status=$?
  echo
  if [ "$status" -eq 0 ]; then
    status_line 32 "✓ Fast checks: PASS"
  else
    status_line 31 "✗ Fast checks: FAIL"
  fi
  echo "  Test suites: $passed passed, $failed failed"
  if [ "$completed" -eq 0 ]; then
    status_line 33 "  ⚠ Run stopped early; remaining suites were not run."
  fi
  echo "  Elapsed: $((SECONDS - started_at))s"
  rm -rf "$WORK"
}
trap finish EXIT

# Suites are independent, so they start together and are reported in the order
# they were written. Output is buffered per suite rather than interleaved, and
# every suite runs: a failure is counted and reported with the rest instead of
# ending the run, which is what the summary is for.
suite_names=()
suite_pids=()
suite_logs=()
run_test() {
  local name="$1"
  shift
  local index=${#suite_names[@]}
  local log="$WORK/suite-$index.out"
  ( "$@" ) > "$log" 2>&1 &
  suite_names[index]="$name"
  suite_pids[index]=$!
  suite_logs[index]="$log"
}

report_tests() {
  local index status
  for ((index = 0; index < ${#suite_names[@]}; index++)); do
    printf '\n%s\n' "${suite_names[$index]}"
    wait "${suite_pids[$index]}"
    status=$?
    cat "${suite_logs[$index]}"
    if [ "$status" -eq 0 ]; then
      passed=$((passed + 1))
      status_line 32 "✓ ${suite_names[$index]}"
    else
      failed=$((failed + 1))
      status_line 31 "✗ ${suite_names[$index]}"
    fi
  done
}

# The front end is TypeScript and is checked as such: `tsc` over the trusted
# tools, under full strictness.
# A silently-renamed compiler API reads as `undefined` at runtime and as an
# error here.
typecheck() {
  (cd tools && npx tsc -p tsconfig.json)
}

run_test "Front-end types" typecheck
run_test "JSON field names agree (TS, Lean, OCaml)" node tests/json-field-names.mts
# tools/unchecked.mts enforces the node side's typing conventions: every unit boundary annotated, no value typed `any`,
# and every `as` and `!` carrying its reason.
run_test "Boundaries annotated, no any, assertions with reasons" node tools/unchecked.mts
# tests/unchecked-project/ holds the counterexamples each of unchecked.mts's reports exists for.
run_test "unchecked.mts reports its counterexamples" node tools/unchecked.mts --project tests/unchecked-project --expect
# tests/unchecked-broken/ has an external declaration that does not check: the command refuses the project.
refuses_broken_external() {
  local out
  if out="$(node tools/unchecked.mts --project tests/unchecked-broken --expect 2>&1)"; then
    echo "unchecked.mts accepted a project whose external declaration does not check"
    return 1
  fi
  grep -q "does not check: Cannot find name 'MissingType'" <<<"$out" || { echo "$out"; return 1; }
  echo "an external declaration that does not check: refused"
}
run_test "unchecked.mts refuses a broken external declaration" refuses_broken_external
# tests/docs.mts checks every document's links, anchors and math.
run_test "Documents: links, math" node tests/docs.mts
# tests/node-runs.mts runs examples and native-contract counterexamples under Node.
run_test "Examples run under Node" node tests/node-runs.mts
# tests/trusted-inputs.mts checks the front end's trusted inputs: pinned declarations, resolved files, imports, the array overlay.
run_test "Trusted inputs" node tests/trusted-inputs.mts
# tests/compiler-api.mts binds the compiler-API contract to the installed package: C1, its enums.
run_test "Compiler-API contract" node tests/compiler-api.mts
# tests/host-families.mts checks the family interpreter on declarations no audited package has: generic arms, residual members, refinements.
run_test "Host family interpreter" node tests/host-families.mts
# tests/regexp-shapes.mts checks the capture-shape reading of regex literals against the host.
run_test "RegExp shapes" node tests/regexp-shapes.mts
# tests/rule-inventory.mts checks that the rules REQUEST-PROTOCOL documents are the rules Lean declares.
run_test "Rule inventory" node tests/rule-inventory.mts

report_tests

completed=1
[ "$failed" -eq 0 ]
