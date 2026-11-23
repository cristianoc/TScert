# An experimental mode under the paper's rules

The verifier gains a mode in which it applies the rules of
[An effect language for TScert](effect-languages.md) (effect variables,
bounds, `else`), with its own verdict. Each rule the mode uses is a Lean
proposition, collected in one file. The mode's soundness theorem takes those
propositions as a premise, and an idealised model of the paper proves them.
Nothing changes what an ordinary accepted verdict means.

## The existing mechanism this extends

The mechanism is the frame at a call
([footprints](../FOOTPRINTS.md#support-and-respect),
[the Tolerant frames note](../REFERENCES.md#the-tolerant-frames-note)). As
read from `PromiseCalls.frameKeeps`, `PromiseCalls.callerFrame`,
`IndexFact.keeps` and `Support.respects`:

```text
at a call y = f(args) in the pass:
  eff := the Effect of f's signature             -- EffectSignatures.Effect; from a
                                                  -- written Modifies<P, T> (statedResult)
  Φ   := eff.frame renamed to the caller's slots -- callerFrame
  for each index fact a of the knowledge k:
    S := a.fact.support? ctx                     -- the fact's support
    keep a  iff  respects(query k, S, Φ)          -- ∀ (r:δ)∈S ∀ (r':γ)∈Φ. γ ⊑ δ ∨ q.disjoint r r'
```

The check is sound by `IndexFact.keeps_sound` through `respect_sound`, and
the whole pass by `SourceClaimJson.PassUnit.mode8Accepted_sound`, whose
premise is the verifier's command's exact condition for an accepted
verdict. A callback parameter's type gives `eff` from its written
`Modifies<P, T>`, one closed footprint for every closure passed for it.

**Example, as it is.** In the walker of the paper's Section 1, the
visitor's type states `Modifies<{ values: "any"; spines: "grow" }, void>`.
At `visit(c.i)` the fact `c.i < xs.length` has
`S = {c.i: keep, xs.spine: grow}` and `Φ = {values: any, spines: grow}`. The
pair `(c.i: keep)` against the entry `(values: any)` fails both
alternatives, so the fact is dropped and `walk` is refused at `xs[c.i]`.

## The proposed change

Three parts, each its own step.

**1. The rules file.** A Lean module,
`Verification/Paper/EffectLanguage/Rules.lean`, defines each rule of the
paper the mode uses as a proposition over a semantics, and bundles them:

```lean
structure Semantics where           -- states, admissible transitions, the action of an effect, …
def BoundRule (S : Semantics) : Prop := …   -- the paper's Bound
def AnchRule  (S : Semantics) : Prop := …   -- Anch
def InstRule  (S : Semantics) : Prop := …   -- Inst
def MeetRule  (S : Semantics) : Prop := …   -- inclusion in a meet
structure PaperRules (S : Semantics) : Prop where
  bound : BoundRule S
  anch : AnchRule S
  inst : InstRule S
  meet : MeetRule S
```

`Semantics` is an interface that both the idealised model and TScert's
calculus instantiate. Proving `PaperRules` for TScert's instance later
turns `paperAccepted_sound` into an ordinary theorem with no premise. The
module states and proves nothing else. It holds no `sorry` and no
axiom, so it builds under `warningAsError` and passes the axiom checks
unchanged. The rules of the paper that TScert already proves (Frame,
Seq-Eff, Call, Fun) are not in it; the mode uses their existing theorems.

**2. The idealised model.**
`Verification/Paper/EffectLanguage/Model.lean` gives the paper's effects a
meaning over the heaps, regions and changes of
`Verification.Semantics.Footprints`, the ones the verifier's `Post` reads. A
state is a heap; an effect is a list of atoms, their meet; an atom is an
effect of the paper with its `else` and the environment its regions are read
in, so an instance is read in its caller's environment, or `{old: any}` at a
call. Its transitions are heap extensions; it reads no admissibility. It
proves:

```lean
theorem model_rules : PaperRules Model.semantics
```

A rule that is false fails to prove here. A rule that proves here holds in
the model, not in TScert's calculus. The model fixes two premises the paper
leaves implicit:

- **An anchored instance keeps every location allocated since the call.**
  An instance whose `else` is wider than `keep` changes new storage, the
  cursor of `walk` included, so Anch needs the instance's `else` at `keep`.
- **Inst's substitution reads every position at the caller.** The
  existing `Post.renameM` widens a position with no argument slot to `all`
  at the entry's change. That is sound for an effect whose `else` is
  `keep`, and unsound for one whose `else` is wider than the entry's change,
  which the widened entry would narrow.

**3. The mode.** The verifier, under a flag, reads the paper's annotations
and applies its rules:

- **Annotations.** `else` in a `Modifies` literal, `E extends AtMost<P>`,
  `Modifies<E, T>` and `Modifies<[E, P], T>` at a type parameter `E`,
  instantiations written at calls, and regions at a closure's captures,
  read by `statedResult` and carried on the fragment's wire.
- **Signatures.** `EffectSignatures.Effect` gains effect variables and
  bounds.
- **The frame at a call of a callback parameter.** A pair `(r: δ)` of the
  fact's support is kept when the bound keeps it or `r` is storage the
  function allocated:

  ```text
  keep pair (r:δ)  iff  respects(q, [r:δ], bound entries) ∧ (bound.else ⊑ δ ∨ r ⊆ an entry)
                        ∨  q.disjoint r old                          -- Bound, Anch, meet
  ```

- **Inst at a call of a quantified function.** The instance written at the
  call is checked against the bound at the actual arguments with the
  existing check: `respects(q, bound entries, instance)`. The bound's
  entries read as a support, since its `else` is `any`, and the instance's
  `else` is `keep`.
- **The verdict.** A unit the mode accepts prints its own verdict,
  "accepted under the paper's rules", never the ordinary one. Its theorem
  takes the rules as a premise:

  ```lean
  theorem paperAccepted_sound (rules : PaperRules TScert.semantics)
      (h : PaperAccepted f i) : PassUnitSafe f i
  ```

  `mode8Accepted_sound` and its premise are unchanged.

**Example, through the change.** With
`walk<E extends AtMost<{ "xs[*]": "keep"; else: "any" }>>`, at
`visit(c.i)`:

- the pair `(c.i: keep)` is kept because `c` was allocated in the body, so
  `c.i` is disjoint from `old`;
- the pair `(xs.spine: grow)` is kept by the bound's entry `xs.spine: keep`.

The read is in bounds, and `walk` is accepted under the paper's rules.

At the call in `sumAndTrace`, the instance `{ "visited[*]": "extend" }`
respects the bound `{xs.spine: keep}`: the fresh `visited` is apart from
`xs`. In `sumAndAlias`, `visited` is `xs`, so `extend ⊑ keep` fails and the
call is refused. `sumAndAlias` is safe under Node (its `push` throws at the
maximal length), so it is a refusal of a safe program, not a negative case.

## The prototype

A proved mode needs an arrow whose effect is a variable, and the frame
cannot state "within the bound and no change to storage allocated since
entry": that needs a region the entry state reads (`Region.mem` has 266
uses in 33 files) or a bound in the exit schema (199 uses in 22 files). So
the rules run first in a prototype, which reuses the whole pass:

- **The hook.** `SinglePass.PassChecker.extended` runs a checker a caller
  supplies, threaded as `layer : Option PassLayer := none` through
  `passGroupMode8`. The ordinary verifier passes none; `CheckerScope` has no
  case for it, so `mode8Accepted_sound` and its premise are unchanged.
- **The layer**, in `lean/PaperRulesPrototype.lean`, the root of the
  `paper-rules-prototype` executable outside the `Verification` library. At
  a call of a parameter bound by an effect variable it adds back each fact
  the ordinary layers dropped whose support's every pair is kept by the
  bound or lies in an object the body allocated (read from the separation
  fact the allocation records). At every other step its step and its
  normal effect are the ordinary checker's (`run_eq_base`), so such a step
  keeps the facts it does not name as in the ordinary pass. Its soundness
  is the one axiom `paperKeptFactsSurvive`.
- **The side file.** `dev/paper-annotations.mts` reads the bounds and the
  instances from the source, written as the paper writes them:
  `AtMost<{ "xs[*]": "keep"; else: "any" }>`,
  `walk<{ "visited[*]": "extend" }>`, and a callback's effect as its type's
  result `Modifies<E, T>`. The ordinary reader reads that result as changing
  every location and the bound's and instance's arguments as arguments
  without type meaning
  ([SOURCE-CONTRACTS.md](../SOURCE-CONTRACTS.md#arguments-without-type-meaning)).
- **Inst** is decided by the side script: an instance's root is a caller's
  local, which a checker does not see by name. A `const` local initialised
  by an object or array literal and never assigned is apart from the
  bound's root. This decision is outside Lean.

`node dev/paper-rules.mts dev/paper-rules/walk.ts --project dev/paper-rules`
prints, on the walk of the paper:

```text
ordinary: unverified: reject: … evidence search failed …
prototype: walk: accepted under the paper's rules (assumes paperKeptFactsSurvive)
prototype: sumAndTrace: accepted
prototype: sumAndAlias: refused: the instance changes visited[*] by extend; the bound allows xs[*]: keep
```

With an empty side file the prototype refuses `walk` as the ordinary
verifier does. Declared reach (`"x.**"`) is not read yet.

## What this duplicates

- **Effects and their action.** The paper's effect with `else: keep` is
  `Footprint` with `Post`, and with `else: any` it is the support read by
  `Supported`. The mode adds effect variables and bounds, and no other
  representation of a closed effect.
- **Inclusion.** Every inclusion the mode decides is `Support.respects`,
  with its theorem `respect_sound`.
- **The model.** Part 2 reuses `Footprints.Region`, `Region.mem`,
  `Change.Holds`, `Change.min_holds` and `Region.renameM`, the definitions
  the verifier's frame reads.
- **Trust.** The removed read-only frame accepted a unit under an
  obligation on code outside its component. This mode's verdict rests on
  the rules, named in its theorem's premise and proved in the model. It is
  a separate verdict, and no ordinary verdict depends on it.

## Cost and order

Not measured. The files the steps change:

- step 1: one new module;
- step 2: one new module, over `Verification.Semantics.Footprints`;
- step 3: `tools/type-term.mts` (`statedResult`), `tools/fragment.mts` and
  `tools/declaration-types.mts` with Lean's decoder (the wire),
  `EffectSignatures.Effect`, `PromiseCalls` (the frame at a call and
  Inst), and `RequestCli` (the verdict line).

The cases are the paper's walk, with `walk`, `sumAndTrace` and
`sumAndCount` accepted under the rules and `sumAndAlias` refused, and W3
from Pretext.

Steps 1 and 2 are Lean only and can land first. They show whether the
rules hold in the model before any verifier code depends on them.

## Decisions for the owner

- **The flag's name and whether the census reports the mode's verdicts.**
