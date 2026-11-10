#!/usr/bin/env bash
# The checks of `make test-checks`, after its build: the suites below, each a
# `run_test` line with a comment naming what it checks, running no stage, and
# the controls no pipeline case can make (pipeline/test.mts). The pipeline
# cases are pipeline/run-cases.mts (`make test-cases`).
# Usage: test-all.sh
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# The checks test the search: no stage reuses another verifier's evidence
# (docs/STAGE-STORE.md, "Evidence proposals").
export TSCERT_EVIDENCE_REUSE=0
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
# unchecked.mts --list prints every site of the counterexamples, and --contracts the external `any` inputs read at a contract.
unchecked_reports() {
  local list sites total contracts
  list="$(node tools/unchecked.mts --project tests/unchecked-project --list 2>&1)" && { echo "--list passed a project with errors"; return 1; }
  sites=$(grep -c '^tests/unchecked-project/.*  \[' <<<"$list")
  total=$(tail -n 1 <<<"$list" | grep -oE '^[0-9]+ `[^`]*`(, [0-9]+ `[^`]*`)*' | grep -oE '[0-9]+ `' | tr -d ' `' | paste -sd+ - | bc)
  [ "$sites" -gt 0 ] && [ "$sites" -eq "$total" ] || { echo "$list"; echo "--list printed $sites sites; its summary counts ${total:-none}"; return 1; }
  contracts="$(node tools/unchecked.mts --project tests/unchecked-project --contracts 2>&1)" || { echo "$contracts"; return 1; }
  grep -q 'TScertParsedJson: parse(text: string' <<<"$contracts" || { echo "$contracts"; echo "--contracts omits JSON.parse's overlay entry"; return 1; }
  if grep -v '  ([^()]*\.d\.ts)$' <<<"$contracts"; then echo "--contracts printed a line naming no declaration file"; return 1; fi
  echo "--list: $sites sites, as its summary counts; --contracts: $(wc -l <<<"$contracts" | tr -d ' ') contract inputs"
}
run_test "unchecked.mts lists sites and contract inputs" unchecked_reports
# The commit-msg hook (bin/git_hooks/commit_record.sh) accepts a commit record and refuses each kind of malformed one.
commit_records() {
  local dir="$WORK/commit-records" out
  mkdir -p "$dir"
  record() { printf '%s\n\nWhy:\n    a reason\n\n%s\n\n%s\n' "$1" "$2" "$3"; }
  record "Subject" "Docs modified (a document):" $'Outcome: no-behaviour-change\nParts: docs' > "$dir/valid"
  record "Subject" "Rule added (a rule):" $'Outcome: verified\nParts: lean-rules\nTrust: none' > "$dir/valid-behaviour"
  bin/git_hooks/commit_record.sh "$dir/valid" --check || return 1
  bin/git_hooks/commit_record.sh "$dir/valid-behaviour" --check || return 1
  refused() {
    local name="$1" expected="$2"
    if out="$(bin/git_hooks/commit_record.sh "$dir/$name" --check 2>&1)"; then echo "accepted: $name"; return 1; fi
    grep -qF -- "$expected" <<<"$out" || { echo "$name: $out"; return 1; }
  }
  printf 'Subject\n\nOutcome: no-behaviour-change\nParts: docs\n' > "$dir/no-why"
  refused no-why "no 'Why:' section" || return 1
  record "Subject" "Docs modified (a document):" 'Parts: docs' > "$dir/no-outcome"
  refused no-outcome "no 'Outcome:' trailer" || return 1
  record "Subject" "Docs modified (a document):" $'Outcome: maybe\nParts: docs' > "$dir/bad-outcome"
  refused bad-outcome "Outcome 'maybe' is not one of" || return 1
  record "Subject" "Docs modified (a document):" 'Outcome: no-behaviour-change' > "$dir/no-parts"
  refused no-parts "no 'Parts:' trailer" || return 1
  record "Subject" "Rule added (a rule):" $'Outcome: verified\nParts: lean-rules' > "$dir/no-trust"
  refused no-trust "no 'Trust:' trailer" || return 1
  record "Subject" "Docs modified (a document):" $'Outcome: verified\nParts: docs\nTrust: none' > "$dir/no-change"
  refused no-change "no change block" || return 1
  record "$(printf 'x%.0s' {1..101})" "Docs modified (a document):" $'Outcome: no-behaviour-change\nParts: docs' > "$dir/long-subject"
  refused long-subject "the subject line has 101 characters" || return 1
  record "Subject" $'Docs modified (a document,\n  another):' $'Outcome: no-behaviour-change\nParts: docs' > "$dir/wrapped-heading"
  refused wrapped-heading "a change heading must close on its own line" || return 1
  record "Subject" "Docs modified (a document):" $'Outcome: no-behaviour-change\nParts: docs\nReviewed: yes' > "$dir/unknown-trailer"
  refused unknown-trailer "unknown trailer 'Reviewed:'" || return 1
  record "Subject" "Docs modified (a document):" $'Outcome: no-behaviour-change\nParts: docs\nUnits: none' > "$dir/units-none"
  refused units-none "'Units: none'" || return 1
  echo "two records accepted, ten malformed messages refused"
}
run_test "Commit records: the commit-msg hook" commit_records
# tests/docs.mts checks every document's links, anchors and math.
run_test "Documents: links, math" node tests/docs.mts
# tests/caught-errors.mts checks the makers and handlers of caught errors on real failures.
run_test "Caught error helpers" node tests/caught-errors.mts
# tests/node-runs.mts runs examples and native-contract counterexamples under Node.
run_test "Examples run under Node" node tests/node-runs.mts
# tests/trusted-inputs.mts checks the front end's trusted inputs: the Node version, pinned declarations, resolved files, imports, the array overlay.
run_test "Trusted inputs" node tests/trusted-inputs.mts
# tests/tool-failures.mts forces a failure of the compiler's API at each kind of catching site: each is reported as a tool failure.
run_test "Tool failures stay tool failures" node tests/tool-failures.mts
# tests/stage-store.mts checks the stage store with stand-in stages: invalidation, concurrent writers, interrupted writers, timeouts, isolation.
run_test "Stage store" node tests/stage-store.mts
# The keyed closures are identified and hold no policy, store or orchestration module, and the stages' code reads the file system only through tools/files.mts; the observed stages' replay controls run beside the controls.
run_test "Keyed closures; observed stages read through files.mts" node tests/observed-stages.mts --reads
# tests/shared-work.mts checks the work shared within a process: an attempt's answers, query answers and every compiler's ledger.
run_test "Shared work" node tests/shared-work.mts
# tests/compiler-api.mts binds the compiler-API contract to the installed package: C0, C1, C4, C5, C6 and C7.
run_test "Compiler-API contract" node tests/compiler-api.mts
# tests/compiler-api-guards.mts compares each family's guard table, the compiler API's and the stand-in's, with its generator and runs every entry under Node (C2).
run_test "Family guard tables" node tests/compiler-api-guards.mts
# tests/host-families.mts checks the family interpreter on declarations no audited package has: generic arms, residual members, refinements; and tampered tag enum objects.
run_test "Host family interpreter" node tests/host-families.mts
# tests/regexp-shapes.mts checks the capture-shape reading of regex literals against the host.
run_test "RegExp shapes" node tests/regexp-shapes.mts
# tests/diagnostic.mts checks the decoder of diagnostic records, apart from proof acceptance.
run_test "Diagnostic decoder" node tests/diagnostic.mts
# tests/claim-text.mts checks the claim printer on malformed producer output.
run_test "Claim text of malformed input" node tests/claim-text.mts
# tests/rule-inventory.mts checks that the rules REQUEST-PROTOCOL documents are the rules Lean declares.
run_test "Rule inventory" node tests/rule-inventory.mts
# pipeline/test.mts runs the controls no case can make, their operations replayed from the stage store, and the observed stages' replay controls.
run_test "Controls" node pipeline/test.mts

report_tests

completed=1
[ "$failed" -eq 0 ]
