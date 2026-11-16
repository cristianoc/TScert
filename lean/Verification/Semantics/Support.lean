import Verification.Semantics.Footprints

/-! # Support

The note's Definition *Support* (`docs/drafts/tolerant-frames-note/note.tex`,
§5, "Entering the modality"), stated once over any domain of states: a
support `S` of an assertion `A` in a condition `C` is a footprint whose
constraints, met by a transition (`Supported`), keep `A` along it. A domain
gives the heap a state's regions are read at and the transitions it admits.
Both assertion languages read support through this relation: the acceptance
path over arbitrary heaps (`heaps`, `Footprints.Supports`), the paper layer
over indexed states (`Parity.Supports`). The note's Definition *Respect* is
one check, `respects`, of a support against an effect under a separation
query, sound by `respect_sound`; both languages run it, each with its own
query. -/
namespace Verification.Footprints

/-- **A domain of states for support**: the heap each state's regions are
read at, and the transitions the domain admits. -/
structure SupportDomain (State : Type) where
  heap : State → Heap
  admissible : State → State → Prop

/-- An assertion over a domain's states, read at a valuation and an entry
mark. -/
abbrev AssertionOn (State : Type) := Env → Nat → State → Prop

/-- A condition on both endpoints of a transition, read at a valuation and
an entry mark. -/
abbrev ConditionOn (State : Type) := Env → Nat → State → State → Prop

namespace SupportDomain
variable {State : Type} {D : SupportDomain State}

/-- **`S` supports `A` in the condition `C`** (the note, §5, Definition
"Support", read in a context): every admissible transition meeting `C`,
from a state of `A`, within `S` at the first state's heap, reaches a state
of `A`. `C` is the evidence the support relies on besides `S` (a stable
field's contents, a typed array's length kept). An assertion may have
several supports, none greatest. -/
def Supports (D : SupportDomain State) (C : ConditionOn State) (A : AssertionOn State) (S : Footprint) : Prop :=
  ∀ ρ m s s', D.admissible s s' → C ρ m s s' → A ρ m s → Supported S ρ (D.heap s) (D.heap s') → A ρ m s'

/-- A support in a weaker condition is one in a stronger condition. -/
theorem Supports.weaken {C C' : ConditionOn State} {A : AssertionOn State} {S : Footprint}
    (hs : D.Supports C A S) (hc : ∀ ρ m s s', C' ρ m s s' → C ρ m s s') : D.Supports C' A S :=
  fun ρ m s s' ha hc' hA hS => hs ρ m s s' ha (hc ρ m s s' hc') hA hS

/-- The empty support: the assertion is invariant along the admissible
transitions meeting the condition. -/
theorem Supports.of_invariant {C : ConditionOn State} {A : AssertionOn State}
    (hi : ∀ ρ m s s', D.admissible s s' → C ρ m s s' → A ρ m s → A ρ m s') : D.Supports C A [] :=
  fun ρ m s s' ha hc hA _ => hi ρ m s s' ha hc hA

/-- A support of a conjunction: the union of supports of its parts. -/
theorem Supports.and {C : ConditionOn State} {A B : AssertionOn State} {S T : Footprint}
    (hA : D.Supports C A S) (hB : D.Supports C B T) :
    D.Supports C (fun ρ m s => A ρ m s ∧ B ρ m s) (S ++ T) :=
  fun ρ m s s' ha hc hab hS => ⟨hA ρ m s s' ha hc hab.1 fun e he => hS e (List.mem_append_left _ he),
    hB ρ m s s' ha hc hab.2 fun e he => hS e (List.mem_append_right _ he)⟩

/-- A support of a disjunction: the union of supports of its parts, which
keeps the part that held. -/
theorem Supports.or {C : ConditionOn State} {A B : AssertionOn State} {S T : Footprint}
    (hA : D.Supports C A S) (hB : D.Supports C B T) :
    D.Supports C (fun ρ m s => A ρ m s ∨ B ρ m s) (S ++ T) :=
  fun ρ m s s' ha hc hab hS =>
    hab.imp (fun h1 => hA ρ m s s' ha hc h1 fun e he => hS e (List.mem_append_left _ he))
      (fun h2 => hB ρ m s s' ha hc h2 fun e he => hS e (List.mem_append_right _ he))

/-- A larger support (more regions constrained) is a support. -/
theorem Supports.mono {C : ConditionOn State} {A : AssertionOn State} {S T : Footprint}
    (hs : D.Supports C A S) (hst : ∀ e ∈ S, e ∈ T) : D.Supports C A T :=
  fun ρ m s s' ha hc hA hS => hs ρ m s s' ha hc hA fun e he => hS e (hst e he)

end SupportDomain

/-- **Arbitrary heaps**, every transition admitted: the domain of the
support lemmas of the acceptance path, the strongest a support can be
proved in. -/
def heaps : SupportDomain Heap := ⟨fun h => h, fun _ _ => True⟩

/-- **A support proved over arbitrary heaps holds in every domain**, its
assertion and condition read at the states' heaps. -/
theorem SupportDomain.Supports.pullback {State : Type} (D : SupportDomain State) {C : ConditionOn Heap}
    {A : AssertionOn Heap} {S : Footprint} (hs : heaps.Supports C A S) :
    D.Supports (fun ρ m s s' => C ρ m (D.heap s) (D.heap s')) (fun ρ m s => A ρ m (D.heap s)) S :=
  fun ρ m s s' _ hc hA hS => hs ρ m (D.heap s) (D.heap s') trivial hc hA hS

/-- **`S` supports `P` in the context `C`, over arbitrary heaps**: the
acceptance path's assertions and contexts, which read no entry mark. -/
abbrev Supports (C : Env → Heap → Heap → Prop) (P : Env → Heap → Prop) (S : Footprint) : Prop :=
  heaps.Supports (fun ρ _ => C ρ) (fun ρ _ => P ρ) S

/-- A support over arbitrary heaps, from its transitions. -/
theorem Supports.intro {C : Env → Heap → Heap → Prop} {P : Env → Heap → Prop} {S : Footprint}
    (hs : ∀ ρ h h', C ρ h h' → P ρ h → Supported S ρ h h' → P ρ h') : Supports C P S :=
  fun ρ _ h h' _ hc hP hS => hs ρ h h' hc hP hS

/-- A support over arbitrary heaps, at one transition. -/
theorem Supports.apply {C : Env → Heap → Heap → Prop} {P : Env → Heap → Prop} {S : Footprint}
    (hs : Supports C P S) {ρ : Env} {h h' : Heap} (hc : C ρ h h') (hP : P ρ h) (hS : Supported S ρ h h') :
    P ρ h' :=
  hs ρ 0 h h' trivial hc hP hS

/-! ## Separation queries and respect -/

/-- **A separation query**: whether two regions denote disjoint sets. Its
meaning is `SepQuery.Sound`, stated of a prestate: wherever the evidence
the query was built from holds, a positive answer means the two regions
share no location there. -/
structure SepQuery where
  disjoint : Region → Region → Bool

/-- The query is sound at the state `(ρ, h)`. -/
def SepQuery.Sound (q : SepQuery) (ρ : Env) (h : Heap) : Prop :=
  ∀ r s l, q.disjoint r s = true → r.mem ρ h l = true → s.mem ρ h l = true → False

/-- Two queries, either of which may answer. -/
def SepQuery.or (q q' : SepQuery) : SepQuery := ⟨fun r s => q.disjoint r s || q'.disjoint r s⟩

theorem SepQuery.or_sound {q q' : SepQuery} {ρ h} (hq : q.Sound ρ h) (hq' : q'.Sound ρ h) :
    (q.or q').Sound ρ h := by
  intro r s l hd hr hs
  simp only [SepQuery.or, Bool.or_eq_true] at hd
  rcases hd with hd | hd
  · exact hq r s l hd hr hs
  · exact hq' r s l hd hr hs

/-- **Respect** (the note's Definition): every pair `r : δ` of the support
and every entry `r' : γ` of the effect have `γ ⊑ δ`, or the query answers
that `r` and `r'` are disjoint. Change order is compared first; the query is
asked only where it fails. -/
def respects (q : SepQuery) (S Φ : Footprint) : Bool :=
  S.all fun e => Φ.all fun f => f.2.le e.2 || q.disjoint e.1 f.1

/-- **Respect is sound**: an effect respecting a support under a query
sound at the prestate changes each support region within its change. -/
theorem respect_sound {q : SepQuery} {S Φ ρ h h'} (hc : respects q S Φ = true)
    (hq : q.Sound ρ h) (hp : Post Φ ρ h h') : Supported S ρ h h' := by
  intro e he l v hm hv
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with rfl | ⟨f, hf, hfm, hh⟩
  · exact Change.Holds.refl _ _ _
  · have := List.all_eq_true.mp (List.all_eq_true.mp hc e he) f hf
    simp only [Bool.or_eq_true] at this
    rcases this with hle | hap
    · exact hh.mono hle
    · exact (hq e.1 f.1 l hap hm hfm).elim

end Verification.Footprints
