import Verification.Programs.TypingBasics
import Verification.Semantics.ExceptionalPosts

/-! # What a code's body must establish

A code (a function body checked as graph code, `CodeEntry`) is given the
specification its signature states on both exits (the note *Tolerant
frames*, §6, rule Call read from the callee: the body's exits entail the
signature's). One computation decides what its run must establish
(`codeObligations`): its arity within its arguments, its signature's scope
at its arity (`Effect.below`) and no precondition beyond its promise, every
postcondition the signature exports on either exit among those the body's
run establishes (`codeEstablished`, a consequence by membership), and the
closed bound of each exit the run is checked within (`CodeObligations.bound`).

A closed bound entails the requested frame: the frame of an exit is its
closed bound and the receiver entries its scope admits. An exit whose bound
is `⊤` asks nothing of the run, so with both exits at `⊤` and no fresh
result the run is given no bound; a pure body establishes the empty bound
on both exits by itself. Every consumer (the check of a unit's code
requests, the proposals, the diagnosis) reads these two projections,
`codeConditions` and `codeBound`. -/
namespace Verification.ProgramTyping
open Verification CallEffects Parity

section
variable {ι : Type}

/-- **What a code's run must establish**: the closed bound of each exit,
and whether its normal result is fresh. -/
structure CodeObligations where
  bound : Option (Exits Footprints.Closed)
  freshResult : Bool
  deriving DecidableEq

/-- **The postconditions a code's run establishes**: the fresh result where
its bound states one. -/
def codeEstablished (fresh : Bool) : List FormulaSchema :=
  if fresh then [.operation (.freshStore 0)] else []

/-- The closed bounds of a signature's two exits: its footprint on a normal
return, and on a throw where it states `onThrow`, `⊤` otherwise. -/
def exitBounds (e : Effect) : Exits Footprints.Closed :=
  ⟨e.footprint, if e.onThrow then e.footprint else .top⟩

/-- **The closed bounds a code's run is checked within**: none where both
exits are `⊤` and the result is not fresh, or where a pure body states no
fresh result; both exits' bounds otherwise. -/
def runBounds (c : CodeEntry ι) : Option (Exits Footprints.Closed) :=
  if ((exitBounds c.row.effect).normal == .top && (exitBounds c.row.effect).exceptional == .top &&
      !c.row.effect.fresh) || (!c.row.effect.fresh && c.exprs.all Purity.pureTerm)
  then none else some (exitBounds c.row.effect)

/-- **The bound the run is given**: the normal exit's closed bound, whether
the result is fresh, and whether the throw is bounded by the same closed
bound (its exceptional bound not `⊤`). -/
def codeRunBound (c : CodeEntry ι) : Option (Footprints.Closed × Bool × Bool) :=
  (runBounds c).map fun b => (b.normal, c.row.effect.fresh, b.exceptional != .top)

/-- **The obligations of a code's run**: its arity within its arguments, its
signature's scope at its arity, no precondition beyond its promise, and
every postcondition its signature exports on either exit established by its
run; then its run's bounds and fresh result. -/
def codeObligations (c : CodeEntry ι) : Option CodeObligations :=
  if decide (c.arity ≤ c.row.arguments.length) && c.row.effect.below c.arity && c.row.effect.requires.isNone &&
      c.row.effect.schema.normal.ensures.all (· ∈ codeEstablished c.row.effect.fresh) &&
      c.row.effect.schema.exceptional.ensures.all (· ∈ ([] : List FormulaSchema)) then
    some ⟨runBounds c, c.row.effect.fresh⟩
  else none

/-- A code's conditions: it has obligations. -/
def codeConditions (c : CodeEntry ι) : Bool := (codeObligations c).isSome

/-- The bound a code's run is given, from its obligations. -/
def codeBound (c : CodeEntry ι) : Option (Footprints.Closed × Bool × Bool) :=
  (codeObligations c).bind fun o => o.bound.map fun b => (b.normal, o.freshResult, b.exceptional != .top)

theorem codeBound_eq {c : CodeEntry ι} (h : codeConditions c = true) : codeBound c = codeRunBound c := by
  unfold codeConditions at h
  unfold codeBound codeRunBound
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp h
  have ho' := ho
  unfold codeObligations at ho'
  split at ho'
  · cases ho'; rw [ho]; rfl
  · cases ho'

/-- **What the conditions give**: the arity, the scope, no precondition, and
none of the postconditions a run does not establish (a fresh object, an
elements promise, an append, an element write). -/
theorem codeConditions_spec {c : CodeEntry ι} (h : codeConditions c = true) :
    c.arity ≤ c.row.arguments.length ∧ c.row.effect.below c.arity = true ∧ c.row.effect.requires = none ∧
      c.row.effect.freshObject = false ∧ c.row.effect.elements = none := by
  unfold codeConditions at h
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp h
  unfold codeObligations at ho
  split at ho
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none, List.all_eq_true,
      decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨ha, hb⟩, hr⟩, hm⟩, -⟩ := hc
    refine ⟨ha, hb, hr, ?_, ?_⟩
    · cases hf : c.row.effect.freshObject
      · rfl
      · have := hm (.operation (.freshObject 0)) (by simp [Effect.schema, Effect.normalSchema, hf])
        simp [codeEstablished] at this
    · cases he : c.row.effect.elements with
      | none => rfl
      | some R =>
        have := hm (.operation (.elementsWhen 0 .tru 1 R)) (by simp [Effect.schema, Effect.normalSchema, he])
        simp [codeEstablished] at this
  · cases ho

end

/-- **A run keeps the heap at least as long as a bound it starts above**,
on a normal return and on a throw. -/
theorem SafePostExc.grow {Ξ T : Fam} {Q : HeapObservations.Post} {R : Heap → Prop} {b : Nat} :
    ∀ {n W h t}, b ≤ h.length → HeapObservations.SafePostExc Ξ T Q R n W h t →
      HeapObservations.SafePostExc Ξ T (fun h' v => Q h' v ∧ b ≤ h'.length) (fun h' => R h' ∧ b ≤ h'.length)
        n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ hs; exact hs
  | succ n ih =>
    intro W h t hb hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, hT, hQ⟩ | ⟨hth, hR⟩) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, hT, hQ, hb⟩)
    · exact .inl (.inr ⟨hth, hR, hb⟩)
    · exact .inr ⟨U, h', t', hx, hu, step, hh, ih (Nat.le_trans hb (Footprints.step_length_le step)) hs⟩

end Verification.ProgramTyping
