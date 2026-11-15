import Verification.Semantics.ExitSummaries
import Verification.Semantics.ParityDerivations

/-! # Frame checks

The checks a consumer of an exit's frame makes against an enclosing bound,
each over the frame's region-and-change entries, read at the environment
the frame is instantiated at (the note *Tolerant frames*, Frame and
Fresh-Eff).

- **Freshness** (`Region.freshStore`, the note's Fresh-Eff): an entry whose
  region is the store of a call position holding a store allocated at or
  after a mark `b` (its store field, the store field at the empty path, as an
  argument store region states it, or the selected store at the empty path,
  each possibly restricted to a class) covers no location below `b`
  (`Region.freshStore_mem`); on the old locations it is discharged
  (`Footprint.old`). A region reached through a nonempty path from a fresh
  position stays: a fresh store may list old cells.
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
  prefix of the exit heap (`Footprint.keepsHeap_prefix`).

**The frame of a signature** (`Effect.frame`, the normal exit's frame of
`Effect.summary`) has the closed bound below a mark its present fields
determine (`CallEffects.Effect.frame_boundBelow`): the receiver's own change
where it states `receiverOwn`, its coarse bound where it states no receiver
store or the receiver's store is fresh, and `top` otherwise. **The
exceptional exit's frame** (the note's rule Call, instantiated at the
exceptional exit) bounds the heaps of a throw
(`CallEffects.Effect.callExc_frame`). -/
namespace Verification.Footprints
open Verification

/-! ## Freshness -/

/-- **Whether a region is the store of a call position the list `P`
names** (the note's Fresh-Eff, `x.store` with `x` fresh): its store field,
its store field at the empty path, its selected store at the empty path, or
such a region restricted to a class. -/
def Region.freshStore (P : List Nat) : Region → Bool
  | .field i k => decide (k = arrayStoreKey) && P.contains i
  | .path i [] k => decide (k = arrayStoreKey) && P.contains i
  | .store i [] => P.contains i
  | .inCls r _ => r.freshStore P
  | _ => false

/-- The positions `P` hold values whose array store was allocated at or
after the mark `b`. -/
def FreshPositions (P : List Nat) (b : Nat) (ρ : Env) : Prop := ∀ i ∈ P, FreshAt b (ρ i)

theorem FreshPositions.nil (b : Nat) (ρ : Env) : FreshPositions [] b ρ := fun _ hi => nomatch hi

/-- **A fresh store covers no old location.** -/
theorem Region.freshStore_mem {P : List Nat} {b : Nat} {ρ : Env} {R : Region} {h : Heap} {l : Nat}
    (hP : FreshPositions P b ρ) (hR : R.freshStore P = true) (hm : R.mem ρ h l = true) : b ≤ l := by
  have hfield : ∀ i, i ∈ P → (Region.field i arrayStoreKey).mem ρ h l = true → b ≤ l := by
    intro i hi hm
    obtain ⟨s, hs, hb⟩ := hP i hi
    simp only [Region.mem, beq_iff_eq] at hm
    rw [storeOf_lookup hs] at hm
    cases hm
    exact hb
  induction R with
  | field i k =>
    simp only [Region.freshStore, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hR
    obtain ⟨rfl, hi⟩ := hR
    exact hfield i hi hm
  | path i p k =>
    cases p with
    | nil =>
      simp only [Region.freshStore, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hR
      obtain ⟨rfl, hi⟩ := hR
      rw [Region.mem_path_nil] at hm
      exact hfield i hi hm
    | cons _ _ => simp [Region.freshStore] at hR
  | store i p =>
    cases p with
    | nil =>
      simp only [Region.freshStore, List.contains_iff_mem] at hR
      obtain ⟨s, hs, hb⟩ := hP i hR
      simp only [Region.mem, HeapKnowledge.readPath, beq_iff_eq] at hm
      have hfs := storeOf_lookup hs
      cases hv : ρ i <;> rw [hv] at hfs hm <;> simp only [fieldsOf, List.lookup] at hfs
      case objAt fs c x =>
        simp only [HeapKnowledge.elementsOf, hfs, Option.some.injEq] at hm
        exact hm ▸ hb
      all_goals cases hfs
    | cons _ _ => simp [Region.freshStore] at hR
  | inCls r c ih =>
    simp only [Region.freshStore] at hR
    simp only [Region.mem, Bool.and_eq_true] at hm
    exact ih hR hm.1
  | _ => simp [Region.freshStore] at hR

/-- The entries of a frame that may cover an old location: those freshness
does not discharge. -/
def Footprint.old (P : List Nat) (Φ : Footprint) : Footprint := List.filter (fun e => !e.1.freshStore P) Φ

/-! ## The closed bound below a mark -/

/-- **The closed bound of a frame below a mark**: the closed bound
(`Footprint.close`) of the entries freshness does not discharge. -/
def Footprint.boundBelow (P : List Nat) (Φ : Footprint) : Closed := Footprint.close (Footprint.old P Φ)

/-- **A frame is within its closed bound below the mark** (proved): every
location below `b` changes as the bound's component for its contents
allows, where the positions `P` hold stores allocated at or after `b`. -/
theorem Footprint.boundBelow_sound {P : List Nat} {Φ : Footprint} {ρ : Env} {b : Nat} {h h' : Heap}
    (hp : Post Φ ρ h h') (hP : FreshPositions P b ρ) : (Φ.boundBelow P).HoldsOn (· < b) h h' := by
  refine ⟨hp.1, fun l v hl hv => ?_⟩
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨v', hv', ?_⟩
  rw [Footprint.boundBelow, Footprint.close_at, Footprint.changeAt_holds]
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact .inl rfl
  · cases hf : e.1.freshStore P
    · exact .inr ⟨e, List.mem_filter.mpr ⟨he, by simp [hf]⟩, Region.cats_mem hv hm, hh⟩
    · exact absurd (Region.freshStore_mem hP hf hm) (by omega)

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
    (Φ.boundBelow P).le c = Φ.all fun e => e.1.freshStore P || (Footprint.close [e]).le c := by
  unfold Footprint.boundBelow Footprint.old
  induction Φ with
  | nil => simp [Footprint.close_nil, Closed.empty_le]
  | cons e Φ ih =>
    simp only [List.filter_cons, List.all_cons]
    cases hf : e.1.freshStore P
    · simp only [Bool.not_false, if_true, Bool.false_or]
      rw [show e :: List.filter (fun e => !e.1.freshStore P) Φ = [e] ++ List.filter (fun e => !e.1.freshStore P) Φ
        from rfl, Footprint.close_append, Closed.join_le, ih]
    · simp only [Bool.not_true, Bool.false_eq_true, if_false, Bool.true_or, Bool.true_and]
      exact ih

/-- A closed footprint's entries close to itself. -/
theorem Closed.fp_close (c : Closed) : Footprint.close c.fp = c := by
  rcases c with ⟨v, a, w⟩
  cases v <;> cases a <;> cases w <;> rfl

/-- A closed footprint's entries are their own closed bound below any mark:
no class entry is a fresh store. -/
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
  e.1.freshStore P || Ψ.any (fun f => e.2.le f.2 && Region.sub cl e.1 f.1) ||
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
at the heap they are read at and the positions `P` hold stores allocated at
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
  · exact absurd (Region.freshStore_mem hP hf hm) (by omega)
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

end Verification.Footprints

namespace Verification.CallEffects
open Verification Footprints

/-! ## The frame of a signature -/

private theorem old_closed (P : List Nat) (c : Footprints.Closed) : Footprint.old P c.fp = c.fp := rfl

/-- The argument store regions of a signature freshness does not discharge
at the positions `P`. -/
def Effect.oldRegions (e : Effect) (P : List Nat) : List ArgumentStoreRegion :=
  e.regions.filter fun r => !(regionEntry r).1.freshStore P

/-- **The coarse bound below a mark**: the closed bound, or `top` where an
argument store region freshness does not discharge remains. -/
def Effect.footprintBelow (e : Effect) (P : List Nat) : Footprints.Closed :=
  if (e.oldRegions P).isEmpty then e.closed else .top

/-- With no fresh position the coarse bound below a mark is the coarse
bound. -/
theorem Effect.footprintBelow_nil (e : Effect) : e.footprintBelow [] = e.footprint := by
  unfold Effect.footprintBelow Effect.oldRegions Effect.footprint
  have : e.regions.filter (fun r => !(regionEntry r).1.freshStore []) = e.regions :=
    List.filter_eq_self.mpr fun r _ => by
      cases hp : r.path <;> simp [regionEntry, ArgumentStoreRegion.entry, Region.freshStore, hp]
  rw [this]

private theorem old_regions (P : List Nat) (rs : List ArgumentStoreRegion) :
    Footprint.old P (rs.map regionEntry) = (rs.filter fun r => !(regionEntry r).1.freshStore P).map regionEntry := by
  unfold Footprint.old
  rw [List.filter_map]
  rfl

private theorem old_append (P : List Nat) (Φ Ψ : Footprint) :
    Footprint.old P (Φ ++ Ψ) = Footprint.old P Φ ++ Footprint.old P Ψ :=
  List.filter_append _ _

private theorem old_receiver (P : List Nat) (e : Effect) :
    Footprint.old P e.receiverEntries = if e.receiverOwn then [(.inCls (.own 0) .values, .any)]
      else if e.receiverStore && !P.contains 0 then [(.field 0 arrayStoreKey, .any)] else [] := by
  unfold Effect.receiverEntries
  by_cases h0 : 0 ∈ P <;> cases e.receiverOwn <;> cases e.receiverStore <;>
    simp [Footprint.old, Region.freshStore, h0]

private theorem changeAt_regions (rs : List ArgumentStoreRegion) (k : Category) :
    Footprint.changeAt (rs.map regionEntry) k = if rs.isEmpty then Change.keep else Change.any := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    cases k <;> simp [Footprint.changeAt_cons, regionEntry, ArgumentStoreRegion.entry, Region.cats, Selector.has]

private theorem changeAt_closed (c : Footprints.Closed) :
    Footprint.changeAt c.fp .value = c.value ∧ Footprint.changeAt c.fp .array = c.array ∧
      Footprint.changeAt c.fp .view = c.view :=
  ⟨congrArg Footprints.Closed.value (Closed.fp_close c), congrArg Footprints.Closed.array (Closed.fp_close c),
    congrArg Footprints.Closed.view (Closed.fp_close c)⟩

/-- **A signature's frame has the closed bound below a mark its fields
determine** (proved), its coarse bound below the mark
(`Effect.footprintBelow`) `c`: the receiver's own change `⟨any, c.array,
c.view⟩` where it states `receiverOwn`; else `c` where it states no receiver
store or the receiver's position is fresh; else `top`. -/
theorem Effect.frame_boundBelow (e : Effect) (P : List Nat) :
    Footprint.boundBelow P e.frame = if e.receiverOwn then
        ⟨.any, (e.footprintBelow P).array, (e.footprintBelow P).view⟩
      else if !e.receiverStore || P.contains 0 then e.footprintBelow P else Footprints.Closed.top := by
  unfold Footprint.boundBelow Effect.frame
  rw [old_append, old_append, old_closed, old_regions, old_receiver, Footprint.close_append,
    Footprint.close_append]
  obtain ⟨hv, ha, hw⟩ := changeAt_closed e.closed
  have hreg := changeAt_regions (e.regions.filter fun r => !(regionEntry r).1.freshStore P)
  unfold Effect.footprintBelow Effect.oldRegions
  by_cases h0 : 0 ∈ P <;> cases ho : e.receiverOwn <;> cases hs : e.receiverStore <;>
    cases hr : (e.regions.filter fun r => !(regionEntry r).1.freshStore P).isEmpty <;>
    simp [Footprint.close_eq, Closed.join, Footprint.changeAt_cons, Footprint.changeAt_nil, Region.cats,
      Selector.has, hv, ha, hw, hreg, hr, h0, Closed.top]

/-- The exceptional exit's frame is the signature's frame where it states
`onThrow`, and `⊤` otherwise. -/
theorem Effect.summary_exceptional_frame (e : Effect) (n : Nat) :
    (e.summary n).exceptional.frame = if e.onThrow then e.frame else Parity.topEffect := by
  unfold Effect.summary; cases e.onThrow <;> rfl

/-- The own change of a closed bound bounds it. -/
theorem Effect.join_own (c : Footprints.Closed) : c.join ⟨.any, c.array, c.view⟩ = ⟨.any, c.array, c.view⟩ := by
  rcases c with ⟨v, a, w⟩
  simp [Footprints.Closed.join, Footprints.Change.max_self]

end Verification.CallEffects
