import Verification.Paper.TolerantFrames.ReadOnlyExec

/-! # Read-only handles: a member's certificate from its body

The draft "Read-only handles" (`docs/drafts/readonly-handles.md`, "The
protocol" and "The guarantee"), the certificate a member's call needs
(`Cert`, `ReadOnlyExec.lean`) built from what its body's check establishes.

- **A step within `Ψ` below `b`** (`StepWithin`): every location of `R_P`
  below `b` before the step changes within `Ψ` at its part. With `b` the
  length of the heap at a call's entry, the locations the call allocates are
  free (Tolerant frames' `fresh_eff`).
- **A run's own steps** (`RunSeq`): checked steps at a depth, each meeting
  a property, and inner runs related by `Inner`; a member's own steps
  (`MemberRun.Own`) are a run whose inner runs, of code that is not the
  package's, are one call deeper, a call's segment one whose inner runs are
  at the caller's depth. **Its bound** (`RunSeq.within`): own steps within
  `Ψ` below `b`, inner runs bounded by `Ψ`, bound `R_P` below `b`.
- **The body's bound** (`MemberRun.within`): a member's call whose own steps
  are within `Ψ` below its entry's length, its runs one call deeper bounded
  on `R_P` by `Ψ`, bounds `R_P` at its entry by `Ψ`: the steps by
  themselves, the runs by their bound, composed along the call
  (`Change.Holds.trans`), the region growing (`InR.mono`).
- **The certificate** (`Cert.ofBody`): the member's effect is `Ψ` itself,
  certified by the body's bound wherever every execution of the member's
  call is one whose own steps are within `Ψ` below its entry (the body's
  effect soundness specialized to the member's executions); each invariant
  of `G_P` kept by each checked step (`tolerant`).
- **The protocol's check at a step** (`chargeCheck`, `stepWithin_of_check`):
  the decided check that each charge (the parts a write may change and its
  change) is within `Ψ`, and a step each of whose changes below `b` to a
  location of `R_P` is one of a charge at the location's part, give
  `StepWithin`.
- **The guarantee's check at a step** (`SupportParts`, `keeps_of_charges`):
  an invariant whose support at the parts `S` tolerates `Θ` is kept by a
  step that changes each location of `R_P` at a part of `S` within `Θ`; a
  step whose charges at the parts of `S` are within `Θ` is one. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

variable {P : Package}

/-! ## Steps within the protocol -/

/-- **A step within `Ψ` below `b`**: every location of `R_P` below `b`
before the step changes within `Ψ` at its part. -/
def StepWithin (Ψ : Protocol P) (b : Nat) (st st' : St P) : Prop :=
  ∀ l v, l < b → st.g.InR l → st.s.h[l]? = some v →
    ∃ v', st'.s.h[l]? = some v' ∧ (Ψ (st.part l)).Holds st.s.h.length v v'

/-- A step within a smaller protocol is one within a larger. -/
theorem StepWithin.mono {Ψ Ψ' : Protocol P} (hle : ∀ p, (Ψ p).le (Ψ' p) = true) {b : Nat} {st st' : St P}
    (h : StepWithin Ψ b st st') : StepWithin Ψ' b st st' := fun l v hb hr hv =>
  let ⟨v', hv', hc⟩ := h l v hb hr hv
  ⟨v', hv', Change.Holds.mono (hle _) hc⟩

/-- **A step within `Ψ` below `b` at every location**: every location below
`b` before the step changes within `Ψ` at its part, in `R_P` or not. -/
def StepAll (Ψ : Protocol P) (b : Nat) (st st' : St P) : Prop :=
  ∀ l v, l < b → st.s.h[l]? = some v →
    ∃ v', st'.s.h[l]? = some v' ∧ (Ψ (st.part l)).Holds st.s.h.length v v'

/-- A step within `Ψ` at every location is one within `Ψ` on `R_P`. -/
theorem StepAll.within {Ψ : Protocol P} {b : Nat} {st st' : St P} (h : StepAll Ψ b st st') :
    StepWithin Ψ b st st' := fun l v hb _ hv => h l v hb hv

/-- A step within a smaller protocol at every location is one within a larger. -/
theorem StepAll.mono {Ψ Ψ' : Protocol P} (hle : ∀ p, (Ψ p).le (Ψ' p) = true) {b : Nat} {st st' : St P}
    (h : StepAll Ψ b st st') : StepAll Ψ' b st st' := fun l v hb hv =>
  let ⟨v', hv', hc⟩ := h l v hb hv
  ⟨v', hv', Change.Holds.mono (hle _) hc⟩

/-- **A bound below `b` at every location**: the marks kept, every location
below `b` at the first state changed within `Ψ` at its part. -/
def AllBelow (Ψ : Protocol P) (b : Nat) (st st' : St P) : Prop := Kept st st' ∧ StepAll Ψ b st st'

theorem AllBelow.refl {Ψ : Protocol P} {b : Nat} (st : St P) : AllBelow Ψ b st st :=
  ⟨Kept.refl st, fun _ v _ hv => ⟨v, hv, Change.Holds.refl _ _ _⟩⟩

/-- **Bounds below `b` at every location compose** (proved, as
`RBoundBelow.trans`): the marks fix each old location's part. -/
theorem AllBelow.trans {Ψ : Protocol P} {b : Nat} {st₁ st₂ st₃ : St P} (h₁ : AllBelow Ψ b st₁ st₂)
    (h₂ : AllBelow Ψ b st₂ st₃) : AllBelow Ψ b st₁ st₃ := by
  refine ⟨h₁.1.trans h₂.1, fun l v₁ hb hv₁ => ?_⟩
  have hl : l < st₁.s.h.length := (List.getElem?_eq_some_iff.mp hv₁).1
  obtain ⟨v₂, hv₂, hc₁⟩ := h₁.2 l v₁ hb hv₁
  obtain ⟨v₃, hv₃, hc₂⟩ := h₂.2 l v₂ hb hv₂
  rw [h₁.1.part hl] at hc₂
  exact ⟨v₃, hv₃, Change.Holds.trans h₁.1.1.length_le hc₁ hc₂⟩

/-- **A bound on `R_P` below `b`**: the marks kept, the history growing,
every location of `R_P` below `b` at the first state changed within `Ψ`. -/
def RBoundBelow (Ψ : Protocol P) (d b : Nat) (st st' : St P) : Prop :=
  Kept st st' ∧ Grows d st.g st'.g ∧ StepWithin Ψ b st st'

theorem RBoundBelow.refl {Ψ : Protocol P} {d b : Nat} {st : St P} (hok : Ok d st) : RBoundBelow Ψ d b st st :=
  ⟨Kept.refl st, Grows.refl hok.pos hok.len, fun _ v _ _ hv => ⟨v, hv, Change.Holds.refl _ _ _⟩⟩

theorem RBoundBelow.trans {Ψ : Protocol P} {d b : Nat} {st₁ st₂ st₃ : St P} (h₁ : RBoundBelow Ψ d b st₁ st₂)
    (h₂ : RBoundBelow Ψ d b st₂ st₃) : RBoundBelow Ψ d b st₁ st₃ := by
  refine ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun l v₁ hb hr hv₁ => ?_⟩
  have hl : l < st₁.s.h.length := (List.getElem?_eq_some_iff.mp hv₁).1
  obtain ⟨v₂, hv₂, hc₁⟩ := h₁.2.2 l v₁ hb hr hv₁
  have hr₂ : st₂.g.InR l := InR.mono h₁.2.1 (h₁.1.2 l hl) hr
  obtain ⟨v₃, hv₃, hc₂⟩ := h₂.2.2 l v₂ hb hr₂ hv₂
  rw [h₁.1.part hl] at hc₂
  exact ⟨v₃, hv₃, Change.Holds.trans h₁.1.1.length_le hc₁ hc₂⟩

/-- A bound below `b` at a smaller protocol is one at a larger. -/
theorem RBoundBelow.mono {Ψ Ψ' : Protocol P} (hle : ∀ p, (Ψ p).le (Ψ' p) = true) {d b : Nat} {st st' : St P}
    (h : RBoundBelow Ψ d b st st') : RBoundBelow Ψ' d b st st' :=
  ⟨h.1, h.2.1, h.2.2.mono hle⟩

/-- A bound on all of `R_P` is one below every `b`. -/
theorem RBound.below {Ψ : Protocol P} {d : Nat} {st st' : St P} (h : RBound Ψ d st st') (b : Nat) :
    RBoundBelow Ψ d b st st' :=
  ⟨h.1, h.2.1, fun l v _ hr hv => h.2.2 l v hr hv⟩

/-- A bound below the first heap's length is one on all of `R_P`: every
location the first heap holds is below it. -/
theorem RBoundBelow.all {Ψ : Protocol P} {d : Nat} {st st' : St P} (h : RBoundBelow Ψ d st.s.h.length st st') :
    RBound Ψ d st st' :=
  ⟨h.1, h.2.1, fun l v hr hv => h.2.2 l v (List.getElem?_eq_some_iff.mp hv).1 hr hv⟩

/-! ## A member's own steps -/

/-- **A run whose own steps meet `q`** (the draft's `RunSeq`): steps in `R`
at depth `d`, each meeting `q`, and runs related by `Inner` from states
with at least `dᵢ` sets of the history. A member's call is `dᵢ = d + 1`, its
runs of code that is not the package's one call deeper; a call's segment is
`dᵢ = d`, its runs of outside code at the caller's depth. -/
inductive RunSeq {tv : TypeView} (R : StepRel P tv) (Inner : St P → St P → Prop) (d dᵢ : Nat)
    (q : St P → St P → Prop) : St P → St P → Prop
  | nil (st : St P) : RunSeq R Inner d dᵢ q st st
  | step {st st' st'' : St P} : R.Rel d st st' → q st st' → RunSeq R Inner d dᵢ q st' st'' →
      RunSeq R Inner d dᵢ q st st''
  | inner {st st' st'' : St P} : dᵢ ≤ st.g.A.length → Inner st st' → RunSeq R Inner d dᵢ q st' st'' →
      RunSeq R Inner d dᵢ q st st''

/-- **A member's call whose own steps meet `q`**: a `MemberRunOf R` each of
whose steps in `R` (not those of its runs one call deeper) meets `q`, a run
whose inner runs are one call deeper. -/
abbrev MemberRun.Own {tv : TypeView} (R : StepRel P tv) (Inner : St P → St P → Prop) (d : Nat)
    (q : St P → St P → Prop) : St P → St P → Prop :=
  RunSeq R Inner d (d + 1) q

/-- **The run's bound** (proved, by induction on the run; the draft's
`RunSeq.within`): a run whose own steps are within `Ψ` below `b`, its inner
runs, at `d` or one call deeper, bounded on `R_P` by `Ψ` at their depth,
bounds `R_P` below `b` by `Ψ` and keeps the invariants. -/
theorem RunSeq.within {tv : TypeView} {R : StepRel P tv} {Ψ : Protocol P} {Inner : St P → St P → Prop}
    {d dᵢ b : Nat} (hdi : dᵢ = d ∨ dᵢ = d + 1)
    (hI : ∀ t t', Inner t t' → Ok dᵢ t → RBound Ψ dᵢ t t' ∧ Ok dᵢ t') {st st' : St P}
    (hr : RunSeq R Inner d dᵢ (StepWithin Ψ b) st st') (hok : Ok d st) :
    RBoundBelow Ψ d b st st' ∧ Ok d st' := by
  induction hr with
  | nil st => exact ⟨RBoundBelow.refl hok, hok⟩
  | step hp hq _ ih =>
    obtain ⟨ok₁, k₁, g₁⟩ := pkg_step_ok (R.pkg hp) hok
    obtain ⟨hb, ok₂⟩ := ih ok₁
    exact ⟨RBoundBelow.trans ⟨k₁, g₁, hq⟩ hb, ok₂⟩
  | inner hl hin _ ih =>
    rcases hdi with rfl | rfl
    · obtain ⟨⟨k₁, g₁, hc₁⟩, ok₁⟩ := hI _ _ hin hok
      obtain ⟨hb, ok₂⟩ := ih ok₁
      exact ⟨RBoundBelow.trans (RBound.below ⟨k₁, g₁, hc₁⟩ _) hb, ok₂⟩
    · obtain ⟨⟨k₁, g₁, hc₁⟩, ok₁⟩ := hI _ _ hin (hok.deeper hl)
      obtain ⟨hb, ok₂⟩ := ih (ok₁.shallower hok.pos)
      exact ⟨RBoundBelow.trans (RBound.below ⟨k₁, g₁.weaken hok.pos, hc₁⟩ _) hb, ok₂⟩

/-- **The body's bound**: a member's call whose own steps are within `Ψ`
below `b`, its runs one call deeper bounded on `R_P` by `Ψ`, bounds `R_P`
below `b` by `Ψ` and keeps the invariants (proved, `RunSeq.within` one
call deeper). -/
theorem MemberRun.within {tv : TypeView} {R : StepRel P tv} {Ψ : Protocol P} {Inner : St P → St P → Prop}
    {d b : Nat}
    (hI : ∀ t t', Inner t t' → Ok (d + 1) t → RBound Ψ (d + 1) t t' ∧ Ok (d + 1) t') {st st' : St P}
    (hr : MemberRun.Own R Inner d (StepWithin Ψ b) st st') (hok : Ok d st) :
    RBoundBelow Ψ d b st st' ∧ Ok d st' :=
  RunSeq.within (.inr rfl) hI hr hok

/-! ## The certificate -/

/-- **A member's certificate from its body** (the draft, "The protocol"):
its effect is `Ψ`. Every execution of the member's call (`Call`, a checked
run `MemberRun`) is one whose own steps are within `Ψ` below the length of
its entry's heap (`body`, the body's effect soundness specialized to the
member's executions: the locations the call allocates are free), so with
its runs one call deeper bounded by `Ψ` it bounds `R_P` at its entry by
`Ψ` (`MemberRun.within`); each invariant of `G_P` is kept by each step in
`R` (`tolerant`). -/
def Cert.ofBody {tv : TypeView} {R : StepRel P tv} {Ψ : Protocol P} {G : (St P → Prop) → Prop}
    {Call : Nat → St P → St P → Prop}
    (body : ∀ (d : Nat) (Inner : St P → St P → Prop) (st st' : St P), MemberRunOf R Inner d st st' →
      Call d st st' → MemberRun.Own R Inner d (StepWithin Ψ st.s.h.length) st st')
    (tolerant : ∀ I, G I → ∀ (d : Nat) t t', R.Rel d t t' → Ok d t → I t → I t') :
    Cert R Ψ G Call where
  eff := Ψ
  within p := by simp [Change.le]
  certified d Inner hI st st' hr hc hok l v hR hv :=
    (MemberRun.within hI (body d Inner st st' hr hc) hok).1.all.2.2 l v hR hv
  tolerant := tolerant

/-! ## The protocol's check at a step -/

/-- **The protocol's check** (`ComponentChecks.protocolDiags` decides it
over the family's code): each charge, the parts a write may change with its
change, is within `Ψ` at each of its parts. -/
def chargeCheck (Ψ : Protocol P) (charges : List (List (Part P) × Change)) : Bool :=
  charges.all fun e => e.1.all fun p => e.2.le (Ψ p)

/-- **The check gives a step within `Ψ`**, where each change the step makes
below `b` to a location of `R_P` is one of a charge at the location's part
(the step's interpretation by its writes: the flow of possible sites gives
the location's part, the write its change). -/
theorem stepWithin_of_check {Ψ : Protocol P} {charges : List (List (Part P) × Change)} {b : Nat} {st st' : St P}
    (hc : chargeCheck Ψ charges = true)
    (hint : ∀ l v, l < b → st.g.InR l → st.s.h[l]? = some v → ∃ v', st'.s.h[l]? = some v' ∧
      (v' = v ∨ ∃ e ∈ charges, st.part l ∈ e.1 ∧ e.2.Holds st.s.h.length v v')) :
    StepWithin Ψ b st st' := by
  intro l v hb hr hv
  obtain ⟨v', hv', hch⟩ := hint l v hb hr hv
  refine ⟨v', hv', ?_⟩
  rcases hch with rfl | ⟨e, he, hp, hh⟩
  · exact Change.Holds.refl _ _ _
  · have := List.all_eq_true.mp (List.all_eq_true.mp hc e he) _ hp
    exact hh.mono this

/-! ## The guarantee's check at a step -/

/-- **An invariant whose support lies at the parts `S` of `R_P`, tolerating
`Θ`**: a transition keeping the marks that changes every location of `R_P`
at a part of `S` within `Θ` keeps it. -/
def SupportParts (Θ : Protocol P) (S : Part P → Bool) (I : St P → Prop) : Prop :=
  ∀ st st', I st → Kept st st' → (∀ l v, st.g.InR l → S (st.part l) = true → st.s.h[l]? = some v →
    ∃ v', st'.s.h[l]? = some v' ∧ (Θ (st.part l)).Holds st.s.h.length v v') → I st'

/-- A support at parts is one in `R_P` (`SupportInR`, (L4)'s premise). -/
theorem SupportParts.inR {Θ : Protocol P} {S : Part P → Bool} {I : St P → Prop} (h : SupportParts Θ S I) :
    SupportInR Θ I :=
  fun st st' hi hk hb => h st st' hi hk fun l v hr _ hv => hb l v hr hv

/-- **A step whose charges at the support's parts are within `Θ` keeps the
invariant** (the guarantee's check at a write): each change the step makes
to a location of `R_P` is one of a charge at its part, and each charge at a
part of `S` is within `Θ` there. -/
theorem keeps_of_charges {Θ : Protocol P} {S : Part P → Bool} {I : St P → Prop} {charges : List (List (Part P) × Change)}
    {st st' : St P} (hs : SupportParts Θ S I) (hk : Kept st st')
    (hc : charges.all (fun e => e.1.all fun p => !S p || e.2.le (Θ p)) = true)
    (hint : ∀ l v, st.g.InR l → st.s.h[l]? = some v → ∃ v', st'.s.h[l]? = some v' ∧
      (v' = v ∨ ∃ e ∈ charges, st.part l ∈ e.1 ∧ e.2.Holds st.s.h.length v v'))
    (hi : I st) : I st' := by
  refine hs st st' hi hk fun l v hr hS hv => ?_
  obtain ⟨v', hv', hch⟩ := hint l v hr hv
  refine ⟨v', hv', ?_⟩
  rcases hch with rfl | ⟨e, he, hp, hh⟩
  · exact Change.Holds.refl _ _ _
  · have := List.all_eq_true.mp (List.all_eq_true.mp hc e he) _ hp
    rw [hS] at this
    exact hh.mono (by simpa using this)

end Verification.TolerantFrames.ReadOnly
