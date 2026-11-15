#!/usr/bin/env bash
# The checks of `make test-checks`, after its build: the suites below, each a
# `run_test` line with a comment naming what it checks, running no stage, and
# the controls no pipeline case can make (tests/single-pass-controls.mts). The pipeline
# cases are pipeline/run-cases.mts (`make test-cases`). With --infra, the tests
# of the test infrastructure instead (`make test-infra`): the stage store, the
# runner, replay, observed stages and retained declaration sessions.
# Usage: test-all.sh [--infra]
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO" || exit 1

tier="Fast checks"
if [ "${1:-}" = --infra ]; then
  tier="Infrastructure tests"
  shift
fi
if [ $# -gt 0 ]; then
  echo "Unknown argument: $1"
  exit 2
fi

# A timeout this run reports is one of its own: a timeout an earlier run
# recorded is executed again at its limit (`retryingTimeouts`, pipeline/stages.mts).
export TSCERT_RETRY_TIMEOUTS="${TSCERT_RETRY_TIMEOUTS:-1}"

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
    status_line 32 "✓ $tier: PASS"
  else
    status_line 31 "✗ $tier: FAIL"
  fi
  echo "  Test suites: $passed passed, $failed failed"
  if [ "$completed" -eq 0 ]; then
    status_line 33 "  ⚠ Run stopped early; remaining suites were not run."
  fi
  echo "  Elapsed: $((SECONDS - started_at))s"
  local pid
  for pid in ${suite_pids[@]+"${suite_pids[@]}"} ${suite_watchers[@]+"${suite_watchers[@]}"}; do kill -KILL -- "-$pid" 2>/dev/null; done
  rm -rf "$WORK"
}
trap finish EXIT

# Suites are independent, so they start together and are reported in the order
# they were written. Output is buffered per suite rather than interleaved, and
# every suite runs: a failure is counted and reported with the rest instead of
# ending the run, which is what the summary is for.
#
# Each suite has a time budget, `run_test <seconds> "Name" command…`: about
# three times its healthy duration on a 12-core machine, at least 30 s, scaled
# by 12 / cores on a smaller one. A suite over its budget is stopped (its
# process group, SIGTERM, then SIGKILL 5 s later) and reported as a failure
# naming its budget and the last lines it wrote.
set -m
cores=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 12)
budget_scale=$(( (12 + cores - 1) / cores ))
[ "$budget_scale" -ge 1 ] || budget_scale=1
suite_names=()
suite_pids=()
suite_logs=()
suite_budgets=()
suite_watchers=()
run_test() {
  local budget=$(( $1 * budget_scale )) name="$2"
  shift 2
  local index=${#suite_names[@]}
  local log="$WORK/suite-$index.out"
  ( "$@"; status=$?; echo "$SECONDS" > "$log.end"; exit "$status" ) > "$log" 2>&1 &
  local pid=$!
  ( sleep "$budget"; [ -e "$log.end" ] && exit; : > "$log.over"; kill -TERM -- "-$pid" 2>/dev/null; sleep 5; kill -KILL -- "-$pid" 2>/dev/null ) \
    > /dev/null 2>&1 &
  suite_watchers[index]=$!
  suite_names[index]="$name"
  suite_pids[index]=$pid
  suite_logs[index]="$log"
  suite_budgets[index]=$budget
}

report_tests() {
  local index status log took
  for ((index = 0; index < ${#suite_names[@]}; index++)); do
    log="${suite_logs[$index]}"
    printf '\n%s\n' "${suite_names[$index]}"
    wait "${suite_pids[$index]}" 2>/dev/null
    status=$?
    kill -- "-${suite_watchers[$index]}" 2>/dev/null
    cat "$log"
    took=$(( $(cat "$log.end" 2>/dev/null || echo "$SECONDS") - started_at ))
    if [ -e "$log.over" ]; then
      failed=$((failed + 1))
      status_line 31 "✗ ${suite_names[$index]}: stopped over its budget of ${suite_budgets[$index]} s; its output stopped at:"
      tail -n 3 "$log" | sed 's/^/    /'
    elif [ "$status" -eq 0 ]; then
      passed=$((passed + 1))
      status_line 32 "✓ ${suite_names[$index]} (${took} s)"
    else
      failed=$((failed + 1))
      status_line 31 "✗ ${suite_names[$index]} (${took} s)"
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

if [ "$tier" = "Infrastructure tests" ]; then
# tests/stage-store.mts checks the stage store and the stage runner with stand-in stages: invalidation, concurrent writers,
# interrupted writers, timeouts, isolation, eviction, a runner's lost wakes and a worker's lost runner.
run_test 180 "Stage store" node tests/stage-store.mts
# The controls of the infrastructure: the interface stages' store boundary, cold and warm runs, replay and run retention, each
# in a fresh store; beside them the observed stages' replay controls and the declaration sessions' controls.
run_test 300 "Infrastructure controls" node tests/single-pass-controls.mts --infra
else
run_test 30 "Front-end types" typecheck
run_test 30 "JSON field names agree (TS, Lean)" node tests/json-field-names.mts
# tools/unchecked.mts enforces the node side's typing conventions: every unit boundary annotated, no value typed `any`,
# and every `as` and `!` carrying its reason.
run_test 60 "Boundaries annotated, no any, assertions with reasons" node tools/unchecked.mts
# tests/unchecked-project/ holds the counterexamples each of unchecked.mts's reports exists for.
run_test 30 "unchecked.mts reports its counterexamples" node tools/unchecked.mts --project tests/unchecked-project --expect
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
run_test 30 "unchecked.mts refuses a broken external declaration" refuses_broken_external
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
run_test 30 "unchecked.mts lists sites and contract inputs" unchecked_reports
# The commit-msg hook (bin/git_hooks/commit_record.sh) refuses each kind of malformed commit record. Its acceptance of
# well-formed ones is CI's `render` job, which runs it on every commit of a pull request.
commit_records() {
  local dir="$WORK/commit-records" out
  mkdir -p "$dir"
  record() { printf '%s\n\nWhy:\n    a reason\n\n%s\n\n%s\n' "$1" "$2" "$3"; }
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
  record "Subject" "Function modified (Synthesis.lean):" $'Outcome: no-behaviour-change\nParts: docs' > "$dir/unknown-kind"
  refused unknown-kind "the change heading 'Function modified (Synthesis.lean):' names the kind 'Function', which is not one of" || return 1
  record "Subject" $'Control modified (forged slot claims,\n  labels):' $'Outcome: no-behaviour-change\nParts: tools' > "$dir/wrapped-control"
  refused wrapped-control "a change heading must close on its own line" || return 1
  echo "twelve malformed messages refused"
}
run_test 30 "Commit records: the commit-msg hook refuses malformed ones" commit_records
# tests/docs.mts checks every document's links, anchors and math.
run_test 30 "Documents: links, math" node tests/docs.mts
# tests/caught-errors.mts checks the makers and handlers of caught errors on real failures.
run_test 30 "Caught error helpers" node tests/caught-errors.mts
# tests/node-runs.mts runs examples and native-contract counterexamples under Node.
run_test 240 "Examples run under Node" node tests/node-runs.mts
# tests/trusted-inputs.mts checks the front end's trusted inputs: the Node version, pinned declarations, resolved files, imports, the array overlay.
run_test 80 "Trusted inputs" node tests/trusted-inputs.mts
# tests/tool-failures.mts forces a failure of the compiler's API at each kind of catching site: each is reported as a tool failure.
run_test 75 "Tool failures stay tool failures" node tests/tool-failures.mts
# The keyed closures are identified and hold no policy, store or orchestration module, and the stages' code reads the file system only through tools/files.mts; the observed stages' replay controls run beside the controls.
run_test 30 "Keyed closures; observed stages read through files.mts" node tests/observed-stages.mts --reads
# tests/shared-work.mts checks the work shared within a process: an attempt's answers, query answers and every compiler's ledger.
run_test 30 "Shared work" node tests/shared-work.mts
# tests/compiler-api.mts binds the compiler-API contract to the installed package: C0, C1, C4, C5, C6 and C7.
run_test 30 "Compiler-API contract" node tests/compiler-api.mts
# tests/compiler-api-guards.mts compares each family's guard table, the compiler API's and the stand-in's, with its generator and runs every entry under Node (C2).
run_test 150 "Family guard tables" node tests/compiler-api-guards.mts
# tests/host-families.mts checks the family interpreter on declarations no audited package has: generic arms, residual members, refinements; and tampered tag enum objects.
run_test 30 "Host family interpreter" node tests/host-families.mts
# tests/regexp-shapes.mts checks the capture-shape reading of regex literals against the host.
run_test 30 "RegExp shapes" node tests/regexp-shapes.mts
# tests/diagnostic.mts checks the decoder of diagnostic records, apart from proof acceptance.
run_test 30 "Diagnostic decoder" node tests/diagnostic.mts
# tests/claim-text.mts checks the claim printer on malformed input.
run_test 30 "Claim text of malformed input" node tests/claim-text.mts
# tests/rule-inventory.mts checks that the rules REQUEST-PROTOCOL documents are the rules Lean declares.
run_test 30 "Rule inventory" node tests/rule-inventory.mts
# tests/single-pass-controls.mts runs the controls no case can make, their operations replayed from the stage store: forced proposals, forged fragments,
# forged declarations, mutations of the pass, the file worker and the family boundary.
run_test 360 "Controls" node tests/single-pass-controls.mts
fi

report_tests

completed=1
[ "$failed" -eq 0 ]
