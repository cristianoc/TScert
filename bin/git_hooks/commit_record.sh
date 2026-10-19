#!/bin/bash

# commit-msg hook: every commit carries a commit
# record (.claude/skills/review/SKILL.md): a Why: section, a change block when
# behaviour changes, and trailers git can parse, with Outcome and Parts, and
# Trust unless the outcome is no-behaviour-change.

exec 1>&2

message_file=$1
git_dir=$(git rev-parse --git-dir)

# a merge commit has no record of its own
if [[ -f "$git_dir/MERGE_HEAD" ]]; then
    exit 0
fi

# a reword changes no files and keeps its record
if git diff --cached --quiet; then
    exit 0
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
while IFS= read -r heading; do
    problems+=("a change heading must close on its own line with '):' — '$heading' wraps")
done < <(printf '%s\n' "$body" | grep -E '^(Rule|Semantics|Definition|Typing|Lowering|Refusal|Trust|Wire|Docs|Tooling|Example|Counterexample) (added|modified|removed) \(' | grep -v '):')
if ! printf '%s\n' "$body" | grep -q '^Why:'; then
    problems+=("no 'Why:' section (the problem this commit addresses)")
fi
if [[ "$outcome" != "no-behaviour-change" ]] &&
    ! printf '%s\n' "$body" | grep -Eq '^(Rule|Semantics|Definition|Typing|Lowering|Refusal|Trust|Wire) (added|modified|removed)'; then
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
