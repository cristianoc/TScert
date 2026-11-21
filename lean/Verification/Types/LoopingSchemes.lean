import Verification.Types.PositiveRules
import Verification.Semantics.LoopingClosures

/-! # Looping closures at generic methods

A generic method's contract is a scheme row: a callable meeting its
signatures at every instantiation of its binders (`schemeSemWithArgs`). A
member of a record type states such a contract of the forwarding function
`.bind` makes of the value read and its host (`MethodMembers.boundOn`). The
looping closure (`LoopingClosures.loopFn`) bound to any host meets every
scheme row of call signatures (`boundLoop_scheme`), and so every type one
of whose labels is such a row (`boundLoop_meaning`), and the looping closure
itself meets them too (`loop_scheme`, `loop_meaning`). With
`LoopingClosures.loop_callsT` and `loop_restsT` this gives a value for each
member of a record of methods, generic or not, the inhabitance of a framed
plan's initial premise reads (the framed acceptance draft, "The
initialization as a premise"). -/
namespace Verification.LoopingSchemes
open Verification PositiveGraphs PositiveRules LoopingClosures

variable {ι : Type} {k : ParameterSpace}

/-- **The looping closure bound to a host meets every scheme of call
signatures** (proved): it is invocable, and at every instance its fixed and
variadic signatures are met by `boundLoop_callsT` and `boundLoop_restsT`. -/
theorem boundLoop_scheme (I : ParameterInterpretation ι k) (Ξ : Fam)
    (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (hc : s.construct = false) (n : Nat) (W : WorldT n) (fn : Nat) (c : ComponentTag) (oid : Nat) {v : Tm}
    (hv : isVal v = true) (hs : Scoped 0 v) (oid' : Nat) :
    schemeSemWithArgs I Ξ D η s n W (boundLoop fn c oid v oid') := by
  refine ⟨by simp only [Callee, hc, Bool.false_eq_true, ite_false]; exact boundLoop_invocable fn c oid hs oid',
    fun j hj As _ _ _ => ?_⟩
  simp only [instanceTWithArgs, sigsT, hc, Bool.false_eq_true, ite_false]
  exact ⟨boundLoop_callsT _ fn c oid hv hs oid', boundLoop_restsT _ fn c oid hv hs oid'⟩

/-- **The looping closure meets every scheme of call signatures** (proved). -/
theorem loop_scheme (I : ParameterInterpretation ι k) (Ξ : Fam)
    (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (hc : s.construct = false) (n : Nat) (W : WorldT n) (fn : Nat) (c : ComponentTag) (oid : Nat) :
    schemeSemWithArgs I Ξ D η s n W (loopFn fn c oid) := by
  refine ⟨by simp only [Callee, hc, Bool.false_eq_true, ite_false]; exact loop_invocable fn c oid,
    fun j hj As _ _ _ => ?_⟩
  simp only [instanceTWithArgs, sigsT, hc, Bool.false_eq_true, ite_false]
  exact ⟨loop_callsT _ fn c oid, loop_restsT _ fn c oid⟩

/-- **A label of call schemes**: no parameter row, and a scheme row of call
signatures. -/
def CallScheme (G : NormalGraph ι) (l : ι) : Prop :=
  G.params l = false ∧ ∃ s, G.schemes l = some s ∧ s.construct = false

/-- **A value meeting every scheme meets each label of call schemes**
(proved): such a label's denotation, unfolded once, is its scheme row's. -/
theorem denote_callScheme {G : NormalGraph ι} {l : ι} (hl : CallScheme G l) {n : Nat} {W : WorldT n} {u : Tm}
    (hu : ∀ (I : ParameterInterpretation ι .mixed) Ξ D η (s : SchemeRow ι), s.construct = false →
      schemeSemWithArgs I Ξ D η s n W u) :
    normalDenote G l n W u := by
  obtain ⟨hp, s, hs, hc⟩ := hl
  unfold normalDenote
  rw [qDenoteWithArgs_unfold]
  simp only [qLayerWithArgs, hp, Bool.false_eq_true, ite_false, hs]
  exact hu _ _ _ _ s hc

/-- **The looping closure bound to a host meets a type with a label of call
schemes** (proved). -/
theorem boundLoop_meaning {G : NormalGraph ι} {S : List ι} (hS : ∃ l ∈ S, CallScheme G l) (n : Nat) (W : WorldT n)
    (fn : Nat) (c : ComponentTag) (oid : Nat) {v : Tm} (hv : isVal v = true) (hs : Scoped 0 v) (oid' : Nat) :
    meaning G S n W (boundLoop fn c oid v oid') := by
  obtain ⟨l, hl, hc⟩ := hS
  exact ⟨l, hl, denote_callScheme hc fun I Ξ D η s hsc => boundLoop_scheme I Ξ D η s hsc n W fn c oid hv hs oid'⟩

/-- **The looping closure meets a type with a label of call schemes**
(proved). -/
theorem loop_meaning {G : NormalGraph ι} {S : List ι} (hS : ∃ l ∈ S, CallScheme G l) (n : Nat) (W : WorldT n)
    (fn : Nat) (c : ComponentTag) (oid : Nat) : meaning G S n W (loopFn fn c oid) := by
  obtain ⟨l, hl, hc⟩ := hS
  exact ⟨l, hl, denote_callScheme hc fun I Ξ D η s hsc => loop_scheme I Ξ D η s hsc n W fn c oid⟩

end Verification.LoopingSchemes
