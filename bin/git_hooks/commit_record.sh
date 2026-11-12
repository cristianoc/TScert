#!/bin/bash

# commit-msg hook: every commit carries a commit
# record (.claude/skills/review/SKILL.md): a Why: section, a change block when
# behaviour changes, change headings of the closed list of kinds, each on one
# line, and trailers git can parse, with Outcome and Parts, and
# Trust unless the outcome is no-behaviour-change. A merge commit is checked
# as every other: its record states Why:, Outcome and Parts.
#
# commit_record.sh <message file> --check: the same rules on a message alone,
# for CI to check a pull request's commits.

exec 1>&2

message_file=$1
if [[ "${2:-}" != "--check" ]]; then
    # a reword changes no files and keeps its record
    if git diff --cached --quiet; then
        exit 0
    fi
fi

trailers=$(grep -v '^#' "$message_file" | git interpret-trailers --parse)
value () {
    printf '%s\n' "$trailers" | sed -n "s/^$1: //p" | head -n 1
}

outcome=$(value Outcome)
problems=()
case "$outcome" in
    verified|refused|gap|no-behaviour-change) ;;
    "") problems+=("no 'Outcome:' trailer") ;;
    *) problems+=("Outcome '$outcome' is not one of verified, refused, gap, no-behaviour-change") ;;
esac
if [[ -z "$(value Parts)" ]]; then
    problems+=("no 'Parts:' trailer")
fi
if [[ "$outcome" != "no-behaviour-change" && -z "$(value Trust)" ]]; then
    problems+=("no 'Trust:' trailer (write 'Trust: none' when nothing new is trusted)")
fi

known='^(Units|Outcome|Parts|Lean|Wire|Trust|Depends|Measured|Tests|Co-Authored-By)$'
while IFS= read -r key; do
    [[ -z "$key" ]] && continue
    if ! [[ "$key" =~ $known ]]; then
        problems+=("unknown trailer '$key:' (the trailers are Units, Outcome, Parts, Lean, Wire, Trust, Depends, Measured, Tests, Co-Authored-By)")
    fi
done < <(printf '%s\n' "$trailers" | sed -n 's/^\([^:]*\): .*/\1/p')
if [[ "$(value Units)" == "none" ]]; then
    problems+=("'Units: none': leave the Units trailer out when no unit is named")
fi

body=$(grep -v '^#' "$message_file")
subject=$(printf '%s\n' "$body" | sed -n '1p')
if (( ${#subject} > 100 )); then
    problems+=("the subject line has ${#subject} characters; keep it to 100 (the change in a short sentence)")
fi
kinds='Rule|Semantics|Definition|Typing|Theorem|Lowering|Proposal|Check|Control|Refusal|Trust|Wire|Docs|Example|Counterexample|Tooling'
while IFS= read -r heading; do
    kind=${heading%% *}
    problems+=("the change heading '$heading' names the kind '$kind', which is not one of ${kinds//|/, } (the kind is what the object is, never where it lives)")
done < <(printf '%s\n' "$body" | grep -E '^[A-Z][A-Za-z]* (added|modified|removed) \(' | grep -Ev "^($kinds) ")
while IFS= read -r heading; do
    problems+=("a change heading must close on its own line with '):' — '$heading' wraps")
done < <(printf '%s\n' "$body" | grep -E "^($kinds) (added|modified|removed) \\(" | grep -v '):')
if ! printf '%s\n' "$body" | grep -q '^Why:'; then
    problems+=("no 'Why:' section (the problem this commit addresses)")
fi
if [[ "$outcome" != "no-behaviour-change" ]] &&
    ! printf '%s\n' "$body" | grep -Eq '^(Rule|Semantics|Definition|Typing|Theorem|Lowering|Proposal|Check|Refusal|Trust|Wire) (added|modified|removed)'; then
    problems+=("no change block such as 'Rule added (name):' or 'Lowering modified (name):'")
fi

if (( ${#problems[@]} )); then
    echo "This commit message is not a commit record:"
    for p in "${problems[@]}"; do
        echo "  - $p"
    done
    echo "Format: .claude/skills/review/SKILL.md. The trailers are the last block of"
    echo "the message, one 'Key: value' per line; git interpret-trailers --parse reads them."
    exit 1
fi
