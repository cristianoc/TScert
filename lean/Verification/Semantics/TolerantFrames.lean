import Verification.Semantics.IndexedStates

/-! # Tolerant frames: an effect that is not rigid, and length lower bounds

Two instances of the note "Tolerant frames" over the indexed states of
`IndexedStates`: the effect `x[∗]` at `any`, which is not rigid
(`cells_not_rigid`), and a length lower bound, at a variable and at a path,
which enters the modality of `{values: any, spines: grow}` in
`TolerantFramesRuns` (`grow`, `grow_path`). -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations

/-! ## An effect that is not rigid

`x[∗]`, the spine of `x` with the cells it lists, both at `any`: a first
action may make the spine list an old cell, and a second may then change that
cell, which the first heap's region does not cover. -/

/-- A contract admitting every value. -/
def anyCtr : Ctr 1 := fun _ _ _ v => isVal v = true

/-- A world of three locations admitting every value: an array spine, then
two element cells. -/
def anyWorld : WorldT 1 := ofEntries [(.spine .array, anyCtr), (.elem, anyCtr), (.elem, anyCtr)]

theorem anyWorld_lookup {l : Nat} {c : Ctr 1} (hl : lookup anyWorld l = some c) : l < 3 ∧ c = anyCtr := by
  simp only [lookup, anyWorld, toList, entries_ofEntries] at hl
  rcases l with _ | _ | _ | l <;> simp at hl
  all_goals exact ⟨by omega, hl.symm⟩

theorem anyWorld_adm : WorldAdm anyWorld := by
  refine ⟨fun l c hl => ?_, fun l f N hr => ?_⟩
  · obtain ⟨-, rfl⟩ := anyWorld_lookup hl
    exact ⟨fun _ _ _ _ _ _ hv => hv, fun _ _ _ _ hv => hv⟩
  · simp only [roleAt, roles, anyWorld, entries_ofEntries] at hr
    rcases l with _ | _ | _ | l <;> simp at hr

/-- A heap of `anyWorld`: a spine listing its element cells, and two source
values without references. -/
theorem anyWorld_ok {ls : List (Option Nat)} {a b : Val} (hls : ∀ l, some l ∈ ls → l = 1 ∨ l = 2)
    (ha : isSourceVal a = true) (hb : isSourceVal b = true) (hra : refs a = []) (hrb : refs b = []) :
    HeapOk 1 anyWorld [.arr ls, a, b] := by
  have hvals : ∀ v ∈ [Tm.arr ls, a, b], isVal v = true := by
    intro v hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · rfl
    · exact sourceVal_isVal ha
    · exact sourceVal_isVal hb
  refine ⟨⟨by simp [anyWorld, toList], fun l c hc => ?_⟩, fun l r hr => ?_⟩
  · obtain ⟨hlt, rfl⟩ := anyWorld_lookup hc
    have hlh : l < [Tm.arr ls, a, b].length := by simpa using hlt
    exact ⟨_, List.getElem?_eq_getElem hlh, fun _ _ => hvals _ (List.getElem_mem hlh)⟩
  · simp only [roleAt, roles, anyWorld, entries_ofEntries] at hr
    rcases l with _ | _ | _ | l <;> simp at hr <;> subst hr
    · refine ⟨_, rfl, ⟨ls, rfl⟩, RefsOk_arr_iff.mpr fun l hl => ?_⟩
      rcases hls l hl with rfl | rfl <;> simp [roleAt, roles, anyWorld]
    · exact ⟨_, rfl, ha, RefsOk_of_nil hra⟩
    · exact ⟨_, rfl, hb, RefsOk_of_nil hrb⟩

/-- A state of `anyWorld` at budget 1. -/
def anyState (h : Heap) (ok : HeapOk 1 anyWorld h) : IndexedHeap :=
  ⟨1, anyWorld, h, Nat.one_pos, anyWorld_adm, ok⟩

theorem anyState_admissible {h h' : Heap} {ok ok'} :
    Admissible (anyState h ok) (anyState h' ok') :=
  ⟨Nat.le_refl 1, by show WExt (trunc 1 (Nat.le_refl 1) anyWorld) anyWorld; rw [trunc_id]; exact WExt_refl _⟩

/-- **`x[∗] : any` is not rigid.** -/
theorem cells_not_rigid :
    ¬ Rigid [(.field 0 arraySpineKey, .any), (.cells 0, .any)]
      (fun _ => .objAt [(arraySpineKey, 0)] .absent 0) := by
  intro hr
  let s₁ := anyState [.arr [some 1], .nul, .nul] (anyWorld_ok (by simp) rfl rfl rfl rfl)
  let s₂ := anyState [.arr [some 2], .nul, .nul] (anyWorld_ok (by simp) rfl rfl rfl rfl)
  let s₃ := anyState [.arr [some 2], .nul, .tru] (anyWorld_ok (by simp) rfl rfl rfl rfl)
  have a₁ : Action [(.field 0 arraySpineKey, .any), (.cells 0, .any)]
      (fun _ => .objAt [(arraySpineKey, 0)] .absent 0) s₁ s₂ := by
    refine ⟨anyState_admissible, by simp [s₁, s₂, anyState], fun l v hl => ?_⟩
    rcases l with _ | _ | _ | l <;> simp [s₁, s₂, anyState] at hl ⊢
    · exact .inr ⟨_, List.mem_cons_self .., by decide, trivial⟩
    · exact .inl hl
    · exact .inl hl
  have a₂ : Action [(.field 0 arraySpineKey, .any), (.cells 0, .any)]
      (fun _ => .objAt [(arraySpineKey, 0)] .absent 0) s₂ s₃ := by
    refine ⟨anyState_admissible, by simp [s₂, s₃, anyState], fun l v hl => ?_⟩
    rcases l with _ | _ | _ | l <;> simp [s₂, s₃, anyState] at hl ⊢
    · exact .inl hl
    · exact .inl hl
    · exact .inr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by decide, trivial⟩
  obtain ⟨-, -, hp⟩ := hr s₁ s₂ s₃ a₁ a₂
  obtain ⟨v', hv', ha⟩ := hp 2 .nul (by simp [s₁, anyState])
  simp [s₃, anyState] at hv'
  subst hv'
  rcases ha with he | ⟨e, he, hm, -⟩
  · cases he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [s₁, anyState, Region.mem, spineCells, entriesAt, HeapKnowledge.descriptorSpine, spineEntries, fieldsOf] at hm

/-! ## A length lower bound -/

open HeapKnowledge in
/-- `y ≤ |x|`: slot `y` holds an integer at most the length of `x`'s spine. -/
def lowerBoundFact (y x : Nat) : IndexFact := .linear (.le [(.value y, 1), (.length x, -1)] 0)

/-- `y ≤ |x|` as an assertion. -/
def LowerBound (ε : HeapKnowledge.EntryState) (y x : Nat) : Assertion := fun ρ _ s => (lowerBoundFact y x).HoldsAt ε ρ s.h

/-- `y ≤ |x.p|`: the value the path `p` reads from `x` has a spine at least as
long as the integer slot `y` holds. -/
def PathLowerBound (y x : Nat) (p : List String) : Assertion := fun ρ _ s =>
  ∃ w a len, HeapKnowledge.readPath s.h (ρ x) p = some w ∧ HeapKnowledge.intValue (ρ y) = some a ∧
    HeapKnowledge.lengthOf s.h w = some len ∧ a ≤ len

open HeapKnowledge in
/-- `y ≤ |x.p|` as the pass states it: a linear index fact over the value of
slot `y` and the length term at `x`'s path `p`. -/
def pathLowerBoundFact (y x : Nat) (p : List String) : IndexFact :=
  .linear (.le [(.value y, 1), ((HeapKnowledge.Term.now .length x p), -1)] 0)

/-- **`PathLowerBound` is the pass's path-term index fact.** -/
theorem pathLowerBound_iff {y x : Nat} {p : List String} {ρ : Env} {m : Nat} {s : IndexedHeap} :
    PathLowerBound y x p ρ m s ↔ (pathLowerBoundFact y x p).HoldsAt ε ρ s.h := by
  have e1 : HeapKnowledge.termValue ε ρ s.h (.value y) = HeapKnowledge.intValue (ρ y) := rfl
  have e2 : HeapKnowledge.termValue ε ρ s.h (HeapKnowledge.Term.now .length x p) =
      (HeapKnowledge.readPath s.h (ρ x) p).bind (HeapKnowledge.lengthOf s.h) := rfl
  simp only [PathLowerBound, pathLowerBoundFact, HeapKnowledge.IndexFact.HoldsAt, Linear.Fact.vars,
    Linear.Fact.Holds, Linear.Form.eval, List.map, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, HeapKnowledge.termValuation, e1, e2]
  constructor
  · rintro ⟨w, a, len, hw, ha, hl, hle⟩
    rw [ha, hw]
    simp only [Option.bind_some, hl, Option.isSome_some, Option.getD_some, true_and]
    omega
  · rintro ⟨⟨hy, hx⟩, hle⟩
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hy
    obtain ⟨len, hl⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨w, hw, hl'⟩ := Option.bind_eq_some_iff.mp hl
    rw [ha, hl] at hle
    simp only [Option.getD_some] at hle
    exact ⟨w, a, len, hw, ha, hl', by omega⟩

end Verification.TolerantFrames
