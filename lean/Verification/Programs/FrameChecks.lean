import Verification.Semantics.ExitSummaries

/-! # Frame checks

The checks a consumer of an exit's frame makes against an enclosing bound,
each over the frame's region-and-change entries, read at the environment
the frame is instantiated at (the note *Tolerant frames*, Frame and
Fresh-Eff).

- **Freshness** (`Region.freshSpine`, the note's Fresh-Eff): an entry whose
  region is the spine of a call position holding a spine allocated at or
  after a mark `b` (its spine field, the spine field at the empty path, as an
  argument spine region states it, or the selected spine at the empty path,
  each possibly restricted to a class) covers no location below `b`
  (`Region.freshSpine_mem`); on the old locations it is discharged
  (`Footprint.old`). A region reached through a nonempty path from a fresh
  position stays: a fresh spine may list old cells.
- **The closed bound below a mark** (`Footprint.boundBelow`): the closed
  bound of the entries freshness does not discharge, each category's
  largest change of an entry whose region may hold it; a transition the
  frame allows is within it on the locations below `b`
  (`Footprint.boundBelow_sound`), and its order is entry by entry
  (`Footprint.boundBelow_le`).
- **Inclusion in a footprint bound** (`Footprint.includedIn`): each entry is
  discharged by freshness, lies in an entry of the bound with at least its
  change by region containment (`Region.sub`, with class evidence), or is
  covered category by category by the bound's class entries; a region whose
  containment is unknown is read at every category it may hold
  (`Region.cats`). A transition the frame allows is the bound's on the
  locations below `b` (`Footprint.includedIn_sound`).
- **Inclusion in the empty effect** (`Footprint.keepsHeap`): every entry
  changes nothing its region may hold; success gives the entry heap as a
  prefix of the exit heap (`Footprint.keepsHeap_prefix`). Where the entries
  at regions other than `R` are included in it (`Footprint.without`), every
  old location outside `R` keeps its contents
  (`Footprint.keepsHeap_outside`).

**The exceptional exit's frame** (the note's rule Call, instantiated at
the exceptional exit) bounds the heaps of a throw
(`CallEffects.Effect.callExc_frame`). -/
namespace Verification.Footprints
open Verification

/-! ## Freshness -/

/-- **Whether a region is the spine of a call position the list `P`
names** (the note's Fresh-Eff, `x.spine` with `x` fresh): its spine field,
its spine field at the empty path, its selected spine at the empty path, or
such a region restricted to a class. -/
def Region.freshSpine (P : List Nat) : Region → Bool
  | .field i k => decide (k = arraySpineKey) && P.contains i
  | .path i [] k => decide (k = arraySpineKey) && P.contains i
  | .spine i [] => P.contains i
  | .inCls r _ => r.freshSpine P
  | _ => false

/-- The positions `P` hold values whose array spine was allocated at or
after the mark `b`. -/
def FreshPositions (P : List Nat) (b : Nat) (ρ : Env) : Prop := ∀ i ∈ P, FreshAt b (ρ i)

theorem FreshPositions.nil (b : Nat) (ρ : Env) : FreshPositions [] b ρ := fun _ hi => nomatch hi

/-- **A fresh spine covers no old location.** -/
theorem Region.freshSpine_mem {P : List Nat} {b : Nat} {ρ : Env} {R : Region} {h : Heap} {l : Nat}
    (hP : FreshPositions P b ρ) (hR : R.freshSpine P = true) (hm : R.mem ρ h l = true) : b ≤ l := by
  have hfield : ∀ i, i ∈ P → (Region.field i arraySpineKey).mem ρ h l = true → b ≤ l := by
    intro i hi hm
    obtain ⟨s, hs, hb⟩ := hP i hi
    simp only [Region.mem, beq_iff_eq] at hm
    rw [spineOf_lookup hs] at hm
    cases hm
    exact hb
  induction R with
  | field i k =>
    simp only [Region.freshSpine, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hR
    obtain ⟨rfl, hi⟩ := hR
    exact hfield i hi hm
  | path i p k =>
    cases p with
    | nil =>
      simp only [Region.freshSpine, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hR
      obtain ⟨rfl, hi⟩ := hR
      rw [Region.mem_path_nil] at hm
      exact hfield i hi hm
    | cons _ _ => simp [Region.freshSpine] at hR
  | spine i p =>
    cases p with
    | nil =>
      simp only [Region.freshSpine, List.contains_iff_mem] at hR
      obtain ⟨s, hs, hb⟩ := hP i hR
      simp only [Region.mem, HeapKnowledge.readPath, beq_iff_eq] at hm
      have hfs := spineOf_lookup hs
      cases hv : ρ i <;> rw [hv] at hfs hm <;> simp only [fieldsOf, List.lookup] at hfs
      case objAt fs c x =>
        simp only [HeapKnowledge.elementsOf, hfs, Option.some.injEq] at hm
        exact hm ▸ hb
      all_goals cases hfs
    | cons _ _ => simp [Region.freshSpine] at hR
  | inCls r c ih =>
    simp only [Region.freshSpine] at hR
    simp only [Region.mem, Bool.and_eq_true] at hm
    exact ih hR hm.1
  | _ => simp [Region.freshSpine] at hR

/-- The entries of a frame that may cover an old location: those freshness
does not discharge. -/
def Footprint.old (P : List Nat) (Φ : Footprint) : Footprint := List.filter (fun e => !e.1.freshSpine P) Φ

/-! ## The closed bound below a mark -/

/-- **The closed bound of a frame below a mark**: the closed bound
(`Footprint.close`) of the entries freshness does not discharge. -/
def Footprint.boundBelow (P : List Nat) (Φ : Footprint) : Closed := Footprint.close (Footprint.old P Φ)

/-- **A frame is within its closed bound below the mark** (proved): every
location below `b` changes as the bound's component for its contents
allows, where the positions `P` hold spines allocated at or after `b`. -/
theorem Footprint.boundBelow_sound {P : List Nat} {Φ : Footprint} {ρ : Env} {b : Nat} {h h' : Heap}
    (hp : Post Φ ρ h h') (hP : FreshPositions P b ρ) : (Φ.boundBelow P).HoldsOn (· < b) h h' := by
  refine ⟨hp.1, fun l v hl hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rw [Footprint.boundBelow, Footprint.close_at, Footprint.changeAt_holds]
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact .inl rfl
  · cases hf : e.1.freshSpine P
    · exact .inr ⟨e, List.mem_filter.mpr ⟨he, by simp [hf]⟩, Region.cats_mem hv hm, hh⟩
    · exact absurd (Region.freshSpine_mem hP hf hm) (by omega)

@[simp] theorem Change.keep_max (a : Change) : Change.keep.max a = a := by cases a <;> rfl
@[simp] theorem Change.max_keep (a : Change) : a.max .keep = a := by cases a <;> rfl
@[simp] theorem Change.any_max (a : Change) : Change.any.max a = .any := by cases a <;> rfl
@[simp] theorem Change.max_any (a : Change) : a.max .any = .any := by cases a <;> rfl

theorem Change.max_assoc (a b c : Change) : (a.max b).max c = a.max (b.max c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Footprint.changeAt_nil (k : Category) : Footprint.changeAt [] k = .keep := rfl

theorem Footprint.changeAt_cons (e : Region × Change) (Φ : Footprint) (k : Category) :
    Footprint.changeAt (e :: Φ) k = if e.1.cats.has k then e.2.max (Φ.changeAt k) else Φ.changeAt k := rfl

theorem Footprint.changeAt_append (Φ Ψ : Footprint) (k : Category) :
    (Φ ++ Ψ).changeAt k = (Φ.changeAt k).max (Ψ.changeAt k) := by
  induction Φ with
  | nil => simp [Footprint.changeAt_nil]
  | cons e Φ ih =>
    simp only [List.cons_append, Footprint.changeAt_cons, ih]
    split
    · rw [Change.max_assoc]
    · rfl

theorem Footprint.close_eq (Φ : Footprint) : Φ.close = ⟨Φ.changeAt .value, Φ.changeAt .array, Φ.changeAt .view⟩ :=
  rfl

theorem Footprint.close_append (Φ Ψ : Footprint) : (Φ ++ Ψ).close = Φ.close.join Ψ.close := by
  simp only [Footprint.close_eq, Closed.join, Footprint.changeAt_append]

theorem Footprint.close_nil : Footprint.close [] = Closed.empty := rfl

/-- **The closed bound's order is entry by entry** (proved): below `c`
exactly where every entry freshness does not discharge has its own closed
bound below `c`. -/
theorem Footprint.boundBelow_le (P : List Nat) (Φ : Footprint) (c : Closed) :
    (Φ.boundBelow P).le c = Φ.all fun e => e.1.freshSpine P || (Footprint.close [e]).le c := by
  unfold Footprint.boundBelow Footprint.old
  induction Φ with
  | nil => simp [Footprint.close_nil, Closed.empty_le]
  | cons e Φ ih =>
    simp only [List.filter_cons, List.all_cons]
    cases hf : e.1.freshSpine P
    · simp only [Bool.not_false, if_true, Bool.false_or]
      rw [show e :: List.filter (fun e => !e.1.freshSpine P) Φ = [e] ++ List.filter (fun e => !e.1.freshSpine P) Φ
        from rfl, Footprint.close_append, Closed.join_le, ih]
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.true_or, Bool.true_and]
      exact ih

/-- A closed footprint's entries close to itself. -/
theorem Closed.fp_close (c : Closed) : Footprint.close c.fp = c := by
  rcases c with ⟨v, a, w⟩
  cases v <;> cases a <;> cases w <;> rfl

/-- A closed footprint's entries are their own closed bound below any mark:
no class entry is a fresh spine. -/
theorem Footprint.boundBelow_fp (P : List Nat) (c : Closed) : Footprint.boundBelow P c.fp = c :=
  Closed.fp_close c

/-- The empty frame's closed bound is the empty footprint. -/
theorem Footprint.boundBelow_nil (P : List Nat) : Footprint.boundBelow P [] = Closed.empty := rfl

/-! ## Inclusion in a footprint bound -/

/-- **Whether an entry is included in a bound**: discharged by freshness; in
an entry of the bound with at least its change, by region containment
(`Region.sub` with the class evidence `cl`); or, category by category, in
the bound's class entries. -/
def Footprint.entryIncluded (cl : ClassEvidence) (P : List Nat) (Ψ : Footprint) (e : Region × Change) : Bool :=
  e.1.freshSpine P || Ψ.any (fun f => e.2.le f.2 && Region.sub cl e.1 f.1) ||
    (Footprint.close [e]).le (Footprint.close (Footprint.classes Ψ))

/-- **Whether a frame is included in a bound**, entry by entry. -/
def Footprint.includedIn (cl : ClassEvidence) (P : List Nat) (Φ Ψ : Footprint) : Bool :=
  Φ.all (Footprint.entryIncluded cl P Ψ)

/-- A footprint's postcondition on the locations below the mark `b`. -/
def PostBelow (b : Nat) (Ψ : Footprint) (ρ : Env) (h h' : Heap) : Prop :=
  h.length ≤ h'.length ∧ ∀ l v, l < b → h[l]? = some v → ∃ v', h'[l]? = some v' ∧ Allowed Ψ ρ h l v v'

/-- On a closed footprint, the postcondition below a mark is the closed
bound on the locations below it. -/
theorem PostBelow.closed_iff {b : Nat} {c : Closed} {ρ : Env} {h h' : Heap} :
    PostBelow b c.fp ρ h h' ↔ c.HoldsOn (· < b) h h' := by
  constructor
  · rintro ⟨hl, ha⟩
    refine ⟨hl, fun l v hb hv => ?_⟩
    obtain ⟨v', hv', hal⟩ := ha l v hb hv
    exact ⟨v', hv', (Closed.allowed_iff hv).mp hal⟩
  · rintro ⟨hl, ha⟩
    refine ⟨hl, fun l v hb hv => ?_⟩
    obtain ⟨v', hv', hc⟩ := ha l v hb hv
    exact ⟨v', hv', (Closed.allowed_iff (ρ := ρ) hv).mpr hc⟩

private theorem class_cover {Ψ : Footprint} {ρ : Env} {h h' : Heap} {l : Nat} {v v' : Val}
    (hv : h[l]? = some v) (hl : h.length ≤ h'.length) (hv' : h'[l]? = some v')
    {c : Closed} (hc : (c.at v).Holds h.length v v') (hle : c.le (Footprint.close (Footprint.classes Ψ)) = true) :
    Allowed Ψ ρ h l v v' := by
  have hon : c.HoldsOn (· = l) h h' := ⟨hl, fun l'' w heq hw => by
    subst heq; rw [hv] at hw; cases hw; exact ⟨v', hv', hc⟩⟩
  obtain ⟨u, hu, hh⟩ := (hon.mono hle).2 l v rfl hv
  rw [hv'] at hu; cases hu
  rw [Footprint.close_at, Footprint.changeAt_holds] at hh
  rcases hh with rfl | ⟨f, hf, hk, hfh⟩
  · exact .inl rfl
  · obtain ⟨hfΨ, hcls⟩ := List.mem_filter.mp hf
    refine .inr ⟨f, hfΨ, ?_, hfh⟩
    obtain ⟨R, δ⟩ := f
    cases R <;> simp only [Region.isClass, Bool.false_eq_true] at hcls
    simpa [Region.cats, Region.mem, hv, Selector.selects] using hk

/-- **Inclusion is sound** (proved): a transition a frame allows is the
bound's on the locations below the mark `b`, where the class evidence holds
at the heap they are read at and the positions `P` hold spines allocated at
or after `b`. -/
theorem Footprint.includedIn_sound {cl : ClassEvidence} {P : List Nat} {Φ Ψ : Footprint} {ρ : Env} {b : Nat}
    {h h' : Heap} (hi : Footprint.includedIn cl P Φ Ψ = true) (hc : ClassOk cl ρ h) (hP : FreshPositions P b ρ)
    (hp : Post Φ ρ h h') : PostBelow b Ψ ρ h h' := by
  refine ⟨hp.1, fun l v hb hv => ?_⟩
  have hlt := (List.getElem?_eq_some_iff.mp hv).1
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact .inl rfl
  have hei := List.all_eq_true.mp hi e he
  simp only [Footprint.entryIncluded, Bool.or_eq_true] at hei
  rcases hei with (hf | hsub) | hcat
  · exact absurd (Region.freshSpine_mem hP hf hm) (by omega)
  · obtain ⟨f, hf, hfe⟩ := List.any_eq_true.mp hsub
    simp only [Bool.and_eq_true] at hfe
    exact .inr ⟨f, hf, Region.sub_mem hfe.2 hc hlt hm, hh.mono hfe.1⟩
  · refine class_cover hv hp.1 hv' ?_ hcat
    rw [Footprint.close_at, Footprint.changeAt_holds]
    exact .inr ⟨e, List.mem_singleton_self _, Region.cats_mem hv hm, hh⟩

/-- **The closed bound below a mark is an inclusion in the closed bound's
entries**: where it is below `c`, the frame is included in `c.fp`. -/
theorem Footprint.includedIn_of_boundBelow {cl : ClassEvidence} {P : List Nat} {Φ : Footprint} {c : Closed}
    (h : (Φ.boundBelow P).le c = true) : Footprint.includedIn cl P Φ c.fp = true := by
  rw [Footprint.boundBelow_le] at h
  have hcl : Footprint.classes c.fp = c.fp := by
    simp [Footprint.classes, Closed.fp, Region.isClass]
  refine List.all_eq_true.mpr fun e he => ?_
  have := List.all_eq_true.mp h e he
  simp only [Bool.or_eq_true] at this
  simp only [Footprint.entryIncluded, hcl, Closed.fp_close, Bool.or_eq_true]
  rcases this with hf | hle
  · exact .inl (.inl hf)
  · exact .inr hle

/-! ## Inclusion in the empty effect -/

/-- **Whether a frame is included in the empty effect**: its closed bound is
`empty`, every entry changing nothing its region may hold. -/
def Footprint.keepsHeap (Φ : Footprint) : Bool := (Φ.boundBelow []).le .empty

/-- **A frame included in the empty effect keeps the entry heap**
(proved): the heap a transition it allows leaves extends the entry heap. -/
theorem Footprint.keepsHeap_prefix {Φ : Footprint} {ρ : Env} {h h' : Heap} (hk : Φ.keepsHeap = true)
    (hp : Post Φ ρ h h') : h.IsPrefix h' := by
  have hb := (Footprint.boundBelow_sound (b := h.length) hp (FreshPositions.nil _ _)).mono hk
  exact Closed.holds_empty.mp (Closed.holds_of_on
    ⟨hb.1, fun l v _ hv => hb.2 l v (List.getElem?_eq_some_iff.mp hv).1 hv⟩)

/-- No region is the spine of a position of the empty list. -/
theorem Region.freshSpine_nil (R : Region) : R.freshSpine [] = false := by
  induction R with
  | inCls r _ ih => simpa [Region.freshSpine] using ih
  | path _ p _ => cases p <;> simp [Region.freshSpine]
  | spine _ p => cases p <;> simp [Region.freshSpine]
  | _ => first | rfl | simp [Region.freshSpine]

/-- **A frame's entries at regions other than `R`.** -/
def Footprint.without (R : Region) (Φ : Footprint) : Footprint := Φ.filter fun e => !(e.1 == R)

/-- **A frame whose entries outside a region keep the heap keeps every old
location outside it** (proved): where `Φ.without R` is included in the empty
effect, a transition `Φ` allows leaves every old location `R` does not cover
as it was. -/
theorem Footprint.keepsHeap_outside {R : Region} {Φ : Footprint} {ρ : Env} {h h' : Heap}
    (hk : (Φ.without R).keepsHeap = true) (hp : Post Φ ρ h h') {l : Nat} {v : Val}
    (hl : R.mem ρ h l = false) (hv : h[l]? = some v) : h'[l]? = some v := by
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact hv'
  have hne : (e.1 == R) = false := by
    cases heq : e.1 == R
    · rfl
    · rw [beq_iff_eq] at heq; rw [heq, hl] at hm; cases hm
  have hon : (Footprint.boundBelow [] (Φ.without R)).HoldsOn (· = l) h h' := ⟨hp.1, fun l'' w heq hw => by
    subst heq; rw [hv] at hw; cases hw
    refine ⟨v', hv', ?_⟩
    rw [Footprint.boundBelow, Footprint.close_at, Footprint.changeAt_holds]
    exact .inr ⟨e, List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨he, by simp [hne]⟩, by simp [Region.freshSpine_nil]⟩,
      Region.cats_mem hv hm, hh⟩⟩
  obtain ⟨u, hu, hc⟩ := (hon.mono hk).2 l v rfl hv
  rw [Closed.at_empty] at hc
  rw [hu, hc]

end Verification.Footprints
