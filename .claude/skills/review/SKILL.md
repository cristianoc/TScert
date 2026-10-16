---
name: review
description: Commit records and review pages for verification work. Use when committing verification changes, when an agent reports its work, and when the user asks to review, compare or choose branches to merge. Every commit message is a structured record — a semantic diff with its reason; review pages are rendered from records, never written by hand.
---

# Commit records and review pages

## Principles

1. **A record is a semantic diff.** An ordinary diff is a delta on code; a
   record is the delta on the high-level things the code implements: a proof
   rule, the semantics, a lowering, a trust assumption, a refusal, the wire.
   Each change says which object changed and how: added, removed or
   modified, with Before and After for a modification.
2. **Every change has its reason.** The record opens with `Why:`: the
   problem in concrete terms — the program that failed, how it showed (the
   refusal message, the wrong value under Node), and why the old design could
   not handle it. A reader learns what was wrong before reading what changed.
3. **Each kind of object has its visual language.** TypeScript is shown as
   highlighted code (one version, or Before/After side by side when the code
   changes); rules and semantics as typeset mathematics; a lowering as source
   form ⇝ target term; outcomes as `refused → verified`.
4. **Plain words.** A record is read by someone who knows TypeScript and type
   systems but not this codebase. Use standard terms; define any notation
   where it appears; Lean names go in the `Lean:` trailer, not the prose.
   Describe JavaScript behaviour apart from the model's representation of it.
5. **Lists, not tables.** Use bullet lists; a table only for a long list of
   regular items.
6. **The author uses discretion; tools guide.** A semantic diff is written
   with judgement: what to show, what to hide, pseudo-code where it explains
   better than the exact form. Tools extract the exact facts the author starts
   from (`make lowering FILE=<file.ts> [FN=<function>]`, which runs
   `node dev/lowering-dump.mts`, prints the program graph the verifier
   checks); every abstraction in the record must
   be one those facts support.
7. **The record states history; documents do not.** A commit is where "what
   was wrong" and "what changed" belong. The global writing rules (present
   facts, claims as strong as their evidence, numbers labelled by what
   produced them) apply to each sentence, and the document rule "no history"
   does not apply to records.

## The record

```
<subject: the change, in a short sentence>

Why:
    <the problem: the failing program, the refusal message or the wrong
    value, and why the old design could not handle it>

<Kind> <added|modified|removed> (<object>):
  Before:
    <the old form>
  After:
    <the new form>

Effect:
    <case>   <kind>   <old outcome> → <new outcome>   <reason>

Example (ts):   (only for a program that is no pipeline case)
    <the program, at most 10 lines>

Gap:        (optional) what stays unsupported, and what it needs
Soundness:  (optional) why the change is sound, or where it is proved
Counterexample:  (for a refusal) the program, then what Node prints

Units: <file.ts#unit …>
Outcome: verified | refused | gap | no-behaviour-change
Parts: <lean-semantics lean-rules lean-proofs lean-lowering producer parser wire trust docs tests format tools>
Lean: <theorems and definitions, separated by "; ">
Wire: <the wire change>
Trust: <the new trust sentence, or none>
Depends: <branch or commit the units need beside this one>
Measured: <number, before -> after, and what produced it>
Tests: +positive-case -negative-case forged:what-was-forged
Co-Authored-By: <attribution>
```

- **Kinds:** `Rule`, `Semantics`, `Definition`, `Typing` (rendered as
  mathematics), `Lowering` (source ⇝ term), `Refusal`, `Trust`, `Wire`,
  `Docs` (prose), `Example`, `Counterexample` (code), `Tooling` (lines as
  written). An added or removed object has one form; a modified one has
  `Before:` and `After:`.
- **The object names its stage and its concept:** the parser's gate, the type
  reader, the producer, a lowering, a Lean rule, the verifier's CLI, tooling.
  `Definition modified (type reader: the members of a union)`, not
  `Definition modified (members of a decided union)`.
- **A `Definition` is a concept stated formally:** `name(args) ⟺ …` or
  `name(x) = …`, by cases where it has them, each symbol defined where it
  appears. A sentence about a concept is prose, not a definition: state the
  concept, or describe the change under another kind.
- **`Tooling`** is a change to how the project is built, tested or laid out:
  the runner, a make target, a script, the module structure. It is never a
  `Definition`, since it changes no concept of the calculus or the pipeline.
  Its lines are kept as written, aligned columns included.
- **Sections** are a line `Name:` at the start of a line, followed by text or
  an indented block (2 spaces for `Before:`/`After:`, 4 for content).
- **Mathematics is Unicode, never TeX.** An inference rule is its premises
  (side by side, separated by three or more spaces), a line of `─` ending
  with the rule's name in parentheses, then its conclusion; a blank line
  separates it from other formulas. `_x`, `_{…}` and `^{…}` render as sub-
  and superscripts; an indented line continues the formula above.
- **A lowering line** is `<TypeScript form> ⇝ <term>`; `label: …` lines
  (`true branch: …`) are side conditions; a trailing `(…)` is a note.
- **The examples are the Effect lines.** Each line is one pipeline case,
  its fields three or more spaces apart: the case's name in
  `pipeline/cases.mts`, its kind (`positive`, `negative`, `gap`), its outcome
  before and after (`verified`, `refused`, `gap`; `new` before for an added
  case, `removed` after for a deleted one), and the reason in a few words: the
  refusal's obligation, or what the case shows. `⚠` after the old outcome
  marks it unsound, an acceptance of a program that is not safe. The
  renderer reads each case's program and expected diagnostic from the
  commit, so a line expands to its source with the refused span marked:

  ```
  Effect:
      invalid-computed-conditional-bound   negative   verified ⚠ → refused   number ≤ string at B<number>
      named-tuple-members                  positive   new → verified          plain, optional and rest members
  ```

  An `Example (ts)` block is only for a program that is no case; a case's
  source is never copied into the record.
- **The final block is git trailers**: `Key: value` lines, continuation lines
  indented by one space, nothing after them. `git interpret-trailers --parse`
  must read every key. Every behaviour change states `Outcome` and `Trust`.
- A docs-only or tests-only commit still opens with `Why:` and names what
  it changes (`Docs modified (WORK.md row): …`).

## Rendering

```sh
node dev/commit-records.mts --out review.html <rev>...
node dev/commit-records.mts --out review.html <base>..<tip>...
```

`make semantic-diff REV=<rev or base..tip>` runs the same command, writing to
`$TMPDIR/semantic-diff.html` (`OUT=` names another file).

- Use commit hashes as range bases, so a page keeps its meaning when a
  branch moves.
- A revision renders one card; a range renders its commits under a heading,
  after a bullet summary per range (units by outcome, parts, new trust, wire,
  depends) and the files more than one range changes.
- `--fragment` omits the document skeleton, for publishing with the Artifact
  tool. The page uses no script and no external data.
- A note on `refs/notes/records` overrides the commit message's record. Use
  it only for what is added after a commit exists; the record itself belongs
  in the commit message.

## When to produce a review

- After a batch of agent work, before any merge: render each range and give
  the user the pages. The user chooses what to merge from them.
- When an agent finishes: its report lists the commits; their records are the
  description of the work.
- Agent briefs require records in this format (paste the principles and the
  format into the brief).
