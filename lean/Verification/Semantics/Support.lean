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
query. Its Theorem *Tolerant frame* is one theorem, `frame_step`, at a
transition, and its modal form `frame_box`, over every action of the
effect; every frame of both languages is an instance. -/
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

/-- **An assertion language's supports, by finite evidence**: its formulas
and their meaning over a domain, the contexts a support relies on and the
condition each states, and a check of a footprint against a formula by
evidence, sound for `SupportDomain.Supports`. Each assertion language reads
the one support relation through an instance; the evidence is finite and
syntactic, its meaning given by the check's soundness alone. -/
structure SupportLanguage {State : Type} (D : SupportDomain State) where
  Formula : Type
  sat : Formula → AssertionOn State
  Context : Type
  condition : Context → ConditionOn State
  Evidence : Type
  check : Context → Formula → Footprint → Evidence → Bool
  check_sound : ∀ c F S ev, check c F S ev = true → D.Supports (condition c) (sat F) S

/-! ## Separation queries and respect -/

/-- **A separation query**: whether two regions denote disjoint sets. Its
meaning is `SepQuery.Sound`, stated of a prestate: wherever the evidence
the query was built from holds, a positive answer means the two regions
share no allocated location there, the locations `Post` and `Supported`
constrain. -/
structure SepQuery where
  disjoint : Region → Region → Bool

/-- The query is sound at the state `(ρ, h)`. -/
def SepQuery.Sound (q : SepQuery) (ρ : Env) (h : Heap) : Prop :=
  ∀ r s l, l < h.length → q.disjoint r s = true → r.mem ρ h l = true → s.mem ρ h l = true → False

/-- The query of no separation evidence: it answers no two regions disjoint. -/
def SepQuery.empty : SepQuery := ⟨fun _ _ => false⟩

theorem SepQuery.empty_sound (ρ : Env) (h : Heap) : SepQuery.empty.Sound ρ h :=
  fun _ _ _ _ hd => by cases hd

/-- Two queries, either of which may answer. -/
def SepQuery.or (q q' : SepQuery) : SepQuery := ⟨fun r s => q.disjoint r s || q'.disjoint r s⟩

theorem SepQuery.or_sound {q q' : SepQuery} {ρ h} (hq : q.Sound ρ h) (hq' : q'.Sound ρ h) :
    (q.or q').Sound ρ h := by
  intro r s l hl hd hr hs
  simp only [SepQuery.or, Bool.or_eq_true] at hd
  rcases hd with hd | hd
  · exact hq r s l hl hd hr hs
  · exact hq' r s l hl hd hr hs

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
    · exact (hq e.1 f.1 l (List.getElem?_eq_some_iff.mp hv).1 hap hm hfm).elim

/-! ## The tolerant frame -/

namespace SupportDomain
variable {State : Type}

/-- **An action of the effect `Φ`** in a domain, at a valuation: an
admissible transition whose heaps meet `Φ`'s postcondition, its regions read
at the heap it starts from. -/
def Action (D : SupportDomain State) (Φ : Footprint) (ρ : Env) (s s' : State) : Prop :=
  D.admissible s s' ∧ Post Φ ρ (D.heap s) (D.heap s')

/-- **The condition of a support holds of every action** (the note's
Theorem "Tolerant frame", its premise on `C`): every single change bounded
by `Φ` from a state of `K` meets `C`. -/
def ConditionOnActions (D : SupportDomain State) (K : AssertionOn State) (Φ : Footprint) (C : ConditionOn State) :
    Prop :=
  ∀ ρ m s s', K ρ m s → D.Action Φ ρ s s' → C ρ m s s'

end SupportDomain

/-- **The tolerant frame, at a transition** (the note, §5, Theorem
"Tolerant frame"): an assertion with a support `S` under `C`, and an effect
respecting `S` under a query sound at the prestate, hold after every
admissible transition meeting the effect's postcondition and `C`. Every
frame of both assertion languages is an instance. -/
theorem frame_step {State : Type} {D : SupportDomain State} {C : ConditionOn State} {A : AssertionOn State}
    {S Φ : Footprint} {q : SepQuery} (hs : D.Supports C A S) (hr : respects q S Φ = true) {ρ : Env} {m : Nat}
    {s s' : State} (hq : q.Sound ρ (D.heap s)) (hp : Post Φ ρ (D.heap s) (D.heap s')) (ha : D.admissible s s')
    (hc : C ρ m s s') (hA : A ρ m s) : A ρ m s' :=
  hs ρ m s s' ha hc hA (respect_sound hr hq hp)

/-- **The tolerant frame at the empty support** (the note, §5, Theorem
"Tolerant frame", where the support is empty): every effect respects the
empty support (`respects` is vacuous), so an assertion it supports holds
after every admissible transition meeting its condition, whatever the
transition changes. -/
theorem frame_nil {State : Type} {D : SupportDomain State} {C : ConditionOn State} {A : AssertionOn State}
    (hs : D.Supports C A []) {ρ : Env} {m : Nat} {s s' : State} (ha : D.admissible s s') (hc : C ρ m s s')
    (hA : A ρ m s) : A ρ m s' :=
  hs ρ m s s' ha hc hA fun _ he => nomatch he

/-- **The tolerant frame as a modal law** (the note, §5, Theorem "Tolerant
frame"): `K ∧ A ⊢ □_Φ A` where `S` supports `A` under `C`, `C` holds of
every action of `Φ` from a state of `K`, and `Φ` respects `S` under a query
sound at every state of `K` (`frame_step` at each action). -/
theorem frame_box {State : Type} {D : SupportDomain State} {K : AssertionOn State} {C : ConditionOn State}
    {A : AssertionOn State} {S Φ : Footprint} {q : SepQuery} (hs : D.Supports C A S) (hr : respects q S Φ = true)
    (hq : ∀ ρ m s, K ρ m s → q.Sound ρ (D.heap s)) (hc : D.ConditionOnActions K Φ C) :
    ∀ ρ m s, K ρ m s → A ρ m s → ∀ s', D.Action Φ ρ s s' → A ρ m s' :=
  fun ρ m s hK hA s' ha => frame_step hs hr (hq ρ m s hK) ha.2 ha.1 (hc ρ m s s' hK ha) hA

end Verification.Footprints
