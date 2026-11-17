# The note's rules at acceptance

## The existing mechanism this extends

| Concern | Lean definitions | Owning document |
|---|---|---|
| Effects per exit, rebasing, composition of summaries | `Exits`, `ExitSpec`, `CommandSummary`, `CommandSummary.Sound`, `ThenEvidence`, `Post.compose_rebases`, `rebaseAll`, `RebaseOk` | [Effects of commands](effects-of-commands.md), [Footprints](../FOOTPRINTS.md) |
| Checked consequence and derivations | `checkDerivation`, `checkScoped`, `checkConsequences`, `ExitSpec.weakenCheck` | [Parity interfaces](parity-interfaces.md) |
| Recorded visits of the pass | `SinglePass.VisitRecord`, `StepCertificate`, `StepGrades`, `footprintCheck`, `recordsAdmit` | [Source elaboration](../SOURCE-ELABORATION.md#checking-a-unit-in-one-pass) |
| Loops | `LoopEvidence`, `CommandLoops`, `headExit` | [the note](tolerant-frames-note/note.tex), Loop |

The goal is the [parity skill](../../.claude/skills/parity/SKILL.md)'s: for
each example in the part the note covers, an agent with only the note and
the verifier give the same verdict. The map of rules to mechanisms is the
[rule table](parity-rule-table.md).

## Designs considered, and what each buys under the goal

The designer's answer at commit `81d7f232` proposed four designs. Each is
recorded with the verdicts it can move.

**A. Composition used by acceptance.** Every accepted body gets a
certified summary relative to its entry, composed over the graph's edges
by Seq-Eff on both exits, with a caught throw composed with its handler's
exits; exports and recursive assumptions are weakenings of it. Under the
goal it removes one restriction that can make the pass refuse what the
note accepts: where a throw escapes, the walk requires the declared normal
bound within the exceptional bound, whatever the effect of the throw's
actual prefix. The rest of A is a second proof of decisions already proved
sound.

**B. Checked transfer by derivation.** The existing deciders (frame
keeping, Entry, arithmetic, allocation) emit derivations that
`checkScoped` checks at every edge, merge and loop head. B is what the
goal requires of the rules that keep and establish facts.

**C. Rule Loop with its frame.**

```math
\frac{\{I\land\Box_\Phi R\}\ c\ \{I\} \qquad c:\Phi \qquad \Phi\ \text{rigid}}
     {\{I\land\Box_\Phi R\}\ \mathrm{loop}\ c\ \{I\land\Box_\Phi R\}}
```

The head's facts split into an invariant and a frame kept under the loop's
rigid effect, with each use inside the body bounded by a certified prefix.
Under the goal C matters where an example of the note needs the loop frame
to verify.

**D. The checking round.** Every example of the note runs through the
verifier and through an agent that has only the note; the round's
disagreements are the work list. D is the goal's test itself.

## The work list

From the inventory of the note's 70 example rows against the pipeline
cases (33 with an exact case, 31 with a close one, 6 with none), read on
2026-11-15 with nothing run.

**Disagreements.**

- **C1, Str-Read.** The note gives a string's element at an index below
  its length (rule Str-Read). `bounds-pattern-string-element-refused`
  (`badElement`, `text[i]!` with `i < text.length`) is a declared gap.
- **C2, an upper bound kept under separation** (the full example's
  regional effect; the patterns' rows 2 and 9). By Sep, Rigid and Alloc
  the bound is kept. In `bounds-pattern-grow-upper-refused`, `paths` (a
  fresh `lists.widths` apart from `a.flags`) and `straight` (one call under
  `flags !== out && starts !== out`) are refused.
- **C3, a quantified fact across a write to a disjoint object** (the
  patterns' row 6, the typed-array example). The frame theorem keeps it,
  the support being disjoint from the write.
  `bounds-pattern-fresh-field-write-refused` drops a `forall` over `items`
  across `fragment.width = s` on a fresh object.
- **C4, the note's first example as written.** The aliasing example
  writes `out[j]` with no guard; the verifier refuses such a write
  (`invalid-index-write-no-compare`). The guarded form
  (`element-write-keeps-lengths`) verifies.

**Examples with no case.**

- The fresh-array example's second claim: `0 < |xs|` is not derivable after
  `shrink(xs)`, so `xs[0]` is refused.
- The typed-array example's field claim: `o.n ≐ 1` is kept across `b[0] = 7`
  by field support.
- An iterator's own region: `it.next() : {it.fields : any}`.
- A write through a fresh typed array keeps its entry `views: grow`.
- The limit "derived effects are bounds".
- The limit on transfer at regional effects.

**The checking round** follows these: every example row, the four
disagreements closed first.

## The test, per example

1. The example's text and the note alone go to an agent, which answers
   whether the example verifies, and by which rules.
2. The verifier runs the example's pipeline case; a case is added where
   none exists.
3. Equal answers close the example. A different answer is closed on one
   side: the pass changes, or the note changes with the owner's approval.
