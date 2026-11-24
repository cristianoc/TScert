import Verification.Semantics.Reach.Runs
import Verification.Semantics.Footprints
import Verification.Semantics.Survival
import Verification.Semantics.HeapObservations

/-! # Local-object confinement and no-forge framing

A location set `Priv` is **confined** (`ClosedOut h Priv`) when every allocated
location outside `Priv` holds a value whose direct location steps (`Reach.Leaves`)
stay outside `Priv`. By induction on path length (`ClosedOut.not_reaches`), no
value whose own `Leaves` stay outside `Priv` (`NoPriv Priv v`) can reach any
location in `Priv` through `h`.

For any multi-step evaluation `Steps k h t h' t'` whose roots in `t` all satisfy
`NoPriv Priv` (and where every location of `Priv` is allocated in `h`), the
calculus's no-forge lemmas (`Reach.step_reach`, `Reach.step_noForge`,
`Reach.step_writes`) establish (`steps_confined_unreachable`):
1. every location of `Priv` keeps its exact contents (`h'[loc]? = h[loc]?`);
2. `ClosedOut h' Priv` holds after the evaluation;
3. every root of `t'` (in particular, a returned value or thrown error) satisfies
   `NoPriv Priv`.

For a transition from `h` to `h'` that leaves every allocated location outside
`Priv` unchanged (`∀ m < h.length, ¬ Priv m → h'[m]? = h[m]?`, such as a
heap-preserving step or a call whose checked footprint modifies only `Priv`),
extending `Priv` with the newly allocated interval `[h.length, h'.length)` keeps
`ClosedOut` (`closedOut_of_keep_outside`). -/
namespace Verification.Confinement

open Verification Footprints HeapObservations
open Verification.TolerantFrames.Reach

/-- A value has no direct outgoing reference (nor closure-captured reference)
into `Priv`. -/
def NoPriv (Priv : Nat → Prop) (v : Val) : Prop :=
  ∀ l, Leaves allC v l → ¬ Priv l

/-- Every allocated location outside `Priv` holds a value with `NoPriv Priv`. -/
def ClosedOut (h : Heap) (Priv : Nat → Prop) : Prop :=
  ∀ m, m < h.length → ¬ Priv m → ∀ v, h[m]? = some v → NoPriv Priv v

theorem ClosedOut.empty (h : Heap) : ClosedOut h (fun _ => False) :=
  fun _ _ _ _ _ _ _ hf => hf

theorem NoPriv.of_inert {Priv : Nat → Prop} {v : Val} (hi : Inert allC v) : NoPriv Priv v := by
  intro l ⟨x, hcr, a, hn⟩
  cases hcr with
  | refl => rw [hi.1 a] at hn; cases hn
  | step hx _ => rw [hi.2] at hx; cases hx

theorem NoPriv.of_lt {Priv : Nat → Prop} {m : Nat} {v : Val}
    (hge : ∀ l, Priv l → m ≤ l) (hlt : ∀ l, Leaves allC v l → l < m) : NoPriv Priv v :=
  fun l hl hp => Nat.not_lt.mpr (hge l hp) (hlt l hl)

theorem NoPriv.of_code {Priv : Nat → Prop} {v x : Val} (hv : NoPriv Priv v) (hx : x ∈ codeVals allC v) :
    NoPriv Priv x :=
  fun l hl => hv l (Leaves.code hx hl)

theorem NoPriv.of_codeReach {Priv : Nat → Prop} {v x : Val} (hv : NoPriv Priv v) (hcr : CodeReach allC v x) :
    NoPriv Priv x := by
  induction hcr with
  | refl => exact hv
  | step hx _ ih => exact ih (hv.of_code hx)

theorem NoPriv.of_next {Priv : Nat → Prop} {v : Val} {a : Label} {l : Nat}
    (hv : NoPriv Priv v) (hn : next v a = some l) : ¬ Priv l :=
  hv l ⟨v, .refl v, a, hn⟩

/-- No value satisfying `NoPriv Priv` can reach `Priv` through a `ClosedOut` heap. -/
theorem ClosedOut.not_follows {h : Heap} {Priv : Nat → Prop} (hc : ClosedOut h Priv) :
    ∀ {π : List Label} {v : Val} {l : Nat}, NoPriv Priv v → Follows allC h v π l → ¬ Priv l
  | [], _, _, _, hf => False.elim hf
  | [a], v, l, hv, hf => hv.of_next hf
  | a :: b :: π, v, l, hv, hf => by
    obtain ⟨v₀, hsucc, hrest⟩ := hf
    rcases hsucc with ⟨l₀, hn, hl₀⟩ | ⟨i, -, hi⟩
    · have hnp : ¬ Priv l₀ := hv.of_next hn
      have hlt : l₀ < h.length := (List.getElem?_eq_some_iff.mp hl₀).1
      exact hc.not_follows (hc l₀ hlt hnp v₀ hl₀) hrest
    · exact hc.not_follows (hv.of_code (List.mem_of_getElem? hi)) hrest

theorem ClosedOut.not_reaches {h : Heap} {Priv : Nat → Prop} (hc : ClosedOut h Priv)
    {v : Val} {l : Nat} (hv : NoPriv Priv v) (hr : Reaches allC h v l) : ¬ Priv l :=
  let ⟨_, hf⟩ := hr
  hc.not_follows hv hf

theorem ClosedOut.not_reachesFrom {h : Heap} {Priv : Nat → Prop} (hc : ClosedOut h Priv)
    {R : List Val} {l : Nat} (hR : ∀ v ∈ R, NoPriv Priv v) (hr : ReachesFrom allC h R l) : ¬ Priv l :=
  let ⟨v, hv, hreach⟩ := hr
  hc.not_reaches (hR v hv) hreach

/-! ## Heap value invariant across `Step` -/

/-- Every location in a heap holds a value. -/
def HeapVals (h : Heap) : Prop :=
  ∀ (l : Nat) (v : Val), h[l]? = some v → isVal v = true

theorem heapVals_of_indexed (s : TolerantFrames.IndexedHeap) : HeapVals s.h :=
  fun _ _ hv => heap_isVal hv

private theorem heapVals_append {h xs : Heap} (hh : HeapVals h) (hxs : ∀ v ∈ xs, isVal v = true) :
    HeapVals (h ++ xs) := by
  intro l v hv
  by_cases hl : l < h.length
  · rw [List.getElem?_append_left hl] at hv
    exact hh l v hv
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hl)] at hv
    exact hxs v (List.mem_of_getElem? hv)

private theorem heapVals_set {h : Heap} {l : Nat} {x : Val} (hh : HeapVals h) (hx : isVal x = true) :
    HeapVals (h.set l x) := by
  intro m v hv
  by_cases hm : m = l
  · subst hm
    rw [List.getElem?_set_self'] at hv
    cases hm' : h[m]? with
    | none => rw [hm'] at hv; cases hv
    | some _ => rw [hm'] at hv; simp at hv; subst hv; exact hx
  · rw [List.getElem?_set_ne (Ne.symm hm)] at hv
    exact hh m v hv

/-- A calculus step preserves `HeapVals`. -/
theorem step_heapVals {h h' : Heap} {t t' : Tm} (hs : Step h t h' t') (hh : HeapVals h) : HeapVals h' := by
  induction hs
  case makeFields hv _ =>
    exact heapVals_append (heapVals_append hh hv) (by intro v hv; simp at hv; subst hv; rfl)
  case writeField hv _ _ => exact heapVals_set hh hv
  case arrAlloc hv _ => exact heapVals_append hh hv
  case arrAllocThrow _ _ => exact heapVals_append hh (by intro v hv; simp at hv; subst hv; rfl)
  case setPresent hv _ _ => exact heapVals_set hh hv
  case setGrow hv _ _ => exact heapVals_append hh (by intro v hv; simp at hv; subst hv; exact hv)
  case lenStrThrow _ => exact heapVals_append hh (by intro v hv; simp at hv; subst hv; rfl)
  case arithThrow _ => exact heapVals_append hh (by intro v hv; simp at hv; subst hv; rfl)
  all_goals first | exact hh | (rename_i ih; exact ih hh)

theorem steps_heapVals {k : Nat} {h h' : Heap} {t t' : Tm} (hst : Steps k h t h' t') (hh : HeapVals h) :
    HeapVals h' := by
  induction hst with
  | refl => exact hh
  | next hs _ ih => exact ih (step_heapVals hs hh)

/-! ## Unreachable evaluation preserves `Priv` and `ClosedOut` -/

/-- One calculus step from a term whose roots satisfy `NoPriv Priv` leaves
every allocated location of `Priv` unchanged, keeps `ClosedOut`, and leaves
every root of the resulting term satisfying `NoPriv Priv`. -/
theorem step_confined_unreachable {h h' : Heap} {t t' : Tm} {Priv : Nat → Prop}
    (hh : HeapVals h) (hs : Step h t h' t')
    (hbound : ∀ loc, Priv loc → loc < h.length)
    (hclosed : ClosedOut h Priv)
    (hroots : ∀ x ∈ vals allC .empty true false t, NoPriv Priv x) :
    (∀ loc, Priv loc → h'[loc]? = h[loc]?) ∧
    ClosedOut h' Priv ∧
    (∀ x ∈ vals allC .empty true false t', NoPriv Priv x) := by
  have hrl : ∀ tag, Realm.empty.tags tag = true → allC tag = false := fun _ h => by simp at h
  have hc : allC (activeTag .empty none false t) = false := rfl
  have hsame : ∀ loc, Priv loc → h'[loc]? = h[loc]? := by
    intro loc hp
    have hlt := hbound loc hp
    obtain ⟨v, hv⟩ : ∃ v, h[loc]? = some v := ⟨h[loc], List.getElem?_eq_getElem hlt⟩
    by_cases heq : h'[loc]? = some v
    · rw [heq, hv]
    · obtain ⟨u, hu, a, hn⟩ := step_reach (ofC := allC) (rl := .empty) hs none false hc hv heq
      exact absurd hp ((hroots u (by simpa [allC] using hu)).of_next hn)
  have hclosed' : ClosedOut h' Priv := by
    intro m _ hnp u hu
    by_cases hkeep : ∃ w, h[m]? = some w ∧ h'[m]? = some w
    · obtain ⟨w, hw, hw'⟩ := hkeep
      rw [hu] at hw'; cases hw'
      exact hclosed m (List.getElem?_eq_some_iff.mp hw).1 hnp u hw
    · by_cases hi : Inert allC u
      · exact NoPriv.of_inert hi
      · exact hroots u (by simpa [allC] using step_writes (ofC := allC) (rl := .empty) hs none false hc hkeep hu hi)
  have hroots' : ∀ x ∈ vals allC .empty true false t', NoPriv Priv x := by
    intro x hx l hl
    have hrf : ReachesFrom allC h' (vals allC .empty (!allC none) false t') l :=
      ⟨x, by simpa [allC] using hx, hl.reaches⟩
    rcases step_noForge (ofC := allC) (rl := .empty) (nk := false) hrl hh hs none hc l hrf with hpre | hnew
    · exact hclosed.not_reachesFrom (fun v hv => hroots v (by simpa [allC] using hv)) hpre
    · exact fun hp => Nat.not_lt.mpr hnew (hbound l hp)
  exact ⟨hsame, hclosed', hroots'⟩

/-- Multi-step version of `step_confined_unreachable`. -/
theorem steps_confined_unreachable {k : Nat} {h h' : Heap} {t t' : Tm} {Priv : Nat → Prop}
    (hh : HeapVals h) (hst : Steps k h t h' t')
    (hbound : ∀ loc, Priv loc → loc < h.length)
    (hclosed : ClosedOut h Priv)
    (hroots : ∀ x ∈ vals allC .empty true false t, NoPriv Priv x) :
    (∀ loc, Priv loc → h'[loc]? = h[loc]?) ∧
    ClosedOut h' Priv ∧
    (∀ x ∈ vals allC .empty true false t', NoPriv Priv x) := by
  induction hst with
  | refl => exact ⟨fun _ _ => rfl, hclosed, hroots⟩
  | @next j h₀ h₁ h₂ t₀ t₁ t₂ hs hrest ih =>
    obtain ⟨hsame₁, hcl₁, hr₁⟩ := step_confined_unreachable hh hs hbound hclosed hroots
    have hlen₁ := Footprints.step_length_le hs
    have hbound₁ : ∀ loc, Priv loc → loc < h₁.length := fun loc hp => Nat.lt_of_lt_of_le (hbound loc hp) hlen₁
    obtain ⟨hsame₂, hcl₂, hr₂⟩ := ih (step_heapVals hs hh) hbound₁ hcl₁ hr₁
    exact ⟨fun loc hp => (hsame₂ loc hp).trans (hsame₁ loc hp), hcl₂, hr₂⟩

theorem noPriv_of_val {Priv : Nat → Prop} {v : Tm}
    (hroots : ∀ x ∈ vals allC .empty true false v, NoPriv Priv x) : NoPriv Priv v := by
  by_cases hi : Inert allC v
  · exact NoPriv.of_inert hi
  · exact hroots v (mem_vals_self hi)

theorem noPriv_of_raises {Priv : Nat → Prop} {t e : Tm}
    (hr : Raises t e) (hroots : ∀ x ∈ vals allC .empty true false t, NoPriv Priv x) : NoPriv Priv e :=
  noPriv_of_val fun x hx => hroots x (raises_vals hr hx)

/-! ## Confined-effect and heap-preserving transitions -/

private theorem leaves_lt_of_refsOkN {n : Nat} {W : WorldT n} {h : Heap}
    (hlenW : (entries W).length = h.length) {u : Val} (huok : RefsOkN W u) {l : Nat} (hl : Leaves allC u l) :
    l < h.length := by
  obtain ⟨x, hcr, a, hnx⟩ := hl
  have hx : RefsOkN W x := CodeReach.refsOkN hcr huok
  have lt_role : ∀ {l₀ r}, roleAt W l₀ = some r → l₀ < h.length := fun hr => by
    have := roleAt_lt hr; omega
  cases a with
  | code => cases hnx
  | key k =>
    simp only [next] at hnx
    cases x
    case objAt fs c oid =>
      simp only [fieldsOf] at hnx
      have hsr : SlotRole k (roleAt W l) :=
        hx _ (TolerantFrames.Reach.slot_mem_refs (c := c) (i := oid) (lookup_mem_pair hnx)) (by simp)
      cases hr : roleAt W l with
      | none => rw [hr] at hsr; exact hsr.elim
      | some r => exact lt_role hr
    all_goals simp [fieldsOf] at hnx
  | view =>
    simp only [next] at hnx
    cases x
    case objAt fs c oid =>
      cases c
      case view s' f len =>
        simp only [HeapKnowledge.descriptorSpine, Option.some.injEq] at hnx
        subst hnx
        have hsr := hx _ (by simp [refs] : Ref.view s' f len (fs.lookup arraySpineKey).isNone ∈
          refs (.objAt fs (.view s' f len) oid)) (by simp)
        exact lt_role hsr.2
      all_goals simp [HeapKnowledge.descriptorSpine] at hnx
    all_goals simp [HeapKnowledge.descriptorSpine] at hnx
  | cell i =>
    simp only [next] at hnx
    cases x
    case arr ls =>
      simp only [spineEntries] at hnx
      cases hi : ls[i]? with
      | none => rw [hi] at hnx; cases hnx
      | some o =>
        rw [hi] at hnx; simp only [Option.join_some] at hnx
        cases o with
        | none => cases hnx
        | some m₀ =>
          cases hnx
          have hm₀ : some l ∈ ls := List.mem_of_getElem? hi
          have hr : Ref.elem l ∈ refs (.arr ls) := by
            simp only [refs, spineRefs, List.mem_filterMap]; exact ⟨some l, hm₀, rfl⟩
          exact lt_role (hx _ hr (by simp))
    case viewSpine f cs =>
      simp only [spineEntries] at hnx
      cases hi : (cs.map some)[i]? with
      | none => rw [hi] at hnx; cases hnx
      | some o =>
        rw [hi] at hnx; simp only [Option.join_some] at hnx
        cases o with
        | none => cases hnx
        | some m₀ =>
          cases hnx
          have hm₀ : l ∈ cs := by simpa using List.mem_of_getElem? hi
          have hr : Ref.elem l ∈ refs (.viewSpine f cs) := by
            simp only [refs, List.mem_map]; exact ⟨l, hm₀, rfl⟩
          exact lt_role (hx _ hr (by simp))
    all_goals simp [spineEntries] at hnx

/-- Extending `Priv` with the newly allocated locations `[h.length, h'.length)`
preserves `ClosedOut` whenever every allocated location outside `Priv` kept its
contents from `h` to `h'` and `h` was well-formed (`HeapOk`). -/
theorem closedOut_of_keep_outside {n : Nat} {W : WorldT n} {h h' : Heap} {Priv : Nat → Prop}
    (hok : HeapOk n W h) (hclosed : ClosedOut h Priv)
    (hkeep : ∀ m, m < h.length → ¬ Priv m → h'[m]? = h[m]?) :
    ClosedOut h' (fun loc => Priv loc ∨ (h.length ≤ loc ∧ loc < h'.length)) := by
  intro m hm hnot v hv l hl hp'
  have hmlt : m < h.length := Decidable.byContradiction fun hge => hnot (.inr ⟨Nat.le_of_not_lt hge, hm⟩)
  have hnp : ¬ Priv m := fun hp => hnot (.inl hp)
  have hv0 : h[m]? = some v := by rw [← hkeep m hmlt hnp]; exact hv
  rcases hp' with hp | ⟨hge, _⟩
  · exact hclosed m hmlt hnp v hv0 l hl hp
  · have hlenW : (entries W).length = h.length := by
      have := hok.1.1; simp only [toList, List.length_map] at this; exact this.symm
    have hval : RefsOk W v := by
      obtain ⟨r, hr⟩ := roleAt_some (W := W) (l := m) (by omega)
      obtain ⟨u, hu, -, hokv⟩ := hok.2 m r hr
      rw [hv0] at hu; cases hu; exact hokv
    have hlt := leaves_lt_of_refsOkN hlenW (RefsOk.refsOkN hval) hl
    omega

/-! ## Owned regions and footprint subsumption -/

/-- Every non-spine field location of each slot in `owned` lies in `Priv`. -/
def OwnedFields (ρ : Env) (owned : List Nat) (Priv : Nat → Prop) : Prop :=
  ∀ x ∈ owned, ∀ loc ∈ fieldLocs (ρ x), Priv loc

/-- Every spine location and element cell of each slot in `ownedArr` lies in `Priv`. -/
def OwnedArrays (h : Heap) (ρ : Env) (ownedArr : List Nat) (Priv : Nat → Prop) : Prop :=
  ∀ x ∈ ownedArr,
    (∀ loc, HeapKnowledge.elementsOf (ρ x) = some loc → Priv loc) ∧
    (∀ loc, some loc ∈ spineCells h (ρ x) → Priv loc)

/-- Every slot in `ownedSpines` holds a `.arr` spine whose element cells lie in `Priv`. -/
def OwnedSpines (ρ : Env) (ownedSpines : List Nat) (Priv : Nat → Prop) : Prop :=
  ∀ x ∈ ownedSpines, ∃ ls, ρ x = .arr ls ∧ ∀ loc, some loc ∈ ls → Priv loc

/-- Every slot outside `holders` holds a value with `NoPriv Priv`. -/
def HoldersCover (ρ : Env) (holders : List Nat) (Priv : Nat → Prop) : Prop :=
  ∀ y, y ∉ holders → NoPriv Priv (ρ y)

/-- The `.keep` footprint covering every field of `owned` and every spine/cell of `ownedArr`. -/
def confinedFootprint (owned ownedArr : List Nat) : Footprint :=
  owned.map (fun x => (.fields x, .keep)) ++
    ownedArr.flatMap (fun x => [(.spine x [], .keep), (.cells x, .keep)])

/-- When every location of `Priv` keeps its contents from `h` to `h'`, the
`confinedFootprint` of owned slots is `Supported`. -/
theorem confinedFootprint_supported {h h' : Heap} {ρ : Env} {owned ownedArr : List Nat} {Priv : Nat → Prop}
    (hof : OwnedFields ρ owned Priv) (hoa : OwnedArrays h ρ ownedArr Priv)
    (hsame : ∀ loc, Priv loc → h'[loc]? = h[loc]?) :
    Supported (confinedFootprint owned ownedArr) ρ h h' := by
  intro e he loc v hmem hv
  simp only [confinedFootprint, List.mem_append, List.mem_map, List.mem_flatMap] at he
  rcases he with ⟨x, hx, rfl⟩ | ⟨x, hx, he⟩
  · simp only [Region.mem, List.contains_iff_mem] at hmem
    have hp := hof x hx loc hmem
    exact ⟨v, (hsame loc hp).trans hv, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · simp only [Region.mem, HeapKnowledge.readPath, beq_iff_eq] at hmem
      have hp := (hoa x hx).1 loc hmem
      exact ⟨v, (hsame loc hp).trans hv, rfl⟩
    · simp only [Region.mem, List.contains_iff_mem] at hmem
      have hp := (hoa x hx).2 loc hmem
      exact ⟨v, (hsame loc hp).trans hv, rfl⟩

/-- Pure syntactic region inclusion into an owned `.keep` region. -/
def regionSub : Region → Region → Bool
  | .field x k, .fields y => x == y && k != arraySpineKey
  | .path x [] k, .fields y => x == y && k != arraySpineKey
  | .fields x, .fields y => x == y
  | .pathFields x [], .fields y => x == y
  | .field x k, .spine y [] => x == y && k == arraySpineKey
  | .path x [] k, .spine y [] => x == y && k == arraySpineKey
  | .spine x [], .spine y [] => x == y
  | .cells x, .cells y => x == y
  | .pathCells x [], .cells y => x == y
  | r, R => r == R

theorem regionSub_mem {ρ : Env} {h : Heap} {r R : Region} {loc : Nat}
    (hsub : regionSub r R = true) (hm : r.mem ρ h loc = true) : R.mem ρ h loc = true := by
  cases r with
  | field x k =>
    cases R with
    | fields y =>
      simp only [regionSub, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hsub
      rcases hsub with ⟨rfl, hne⟩
      simp only [Region.mem, beq_iff_eq] at hm
      simp only [Region.mem, List.contains_iff_mem, fieldLocs, List.mem_map, List.mem_filter, bne_iff_ne]
      exact ⟨(k, loc), ⟨lookup_mem_pair hm, hne⟩, rfl⟩
    | spine y p =>
      cases p with
      | nil =>
        simp only [regionSub, Bool.and_eq_true, beq_iff_eq] at hsub
        rcases hsub with ⟨rfl, rfl⟩
        simp only [Region.mem, beq_iff_eq] at hm
        simp only [Region.mem, HeapKnowledge.readPath, beq_iff_eq]
        cases hv : ρ x
        case objAt fs cc oid =>
          rw [hv] at hm; simp only [fieldsOf] at hm; simp [HeapKnowledge.elementsOf, hm]
        all_goals (rw [hv] at hm; simp [fieldsOf] at hm)
      | cons _ _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
    | field y k' =>
      simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
    | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
  | path x p k =>
    cases p with
    | nil =>
      rw [Region.mem_path_nil] at hm
      cases R with
      | fields y =>
        simp only [regionSub, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hsub
        rcases hsub with ⟨rfl, hne⟩
        simp only [Region.mem, beq_iff_eq] at hm
        simp only [Region.mem, List.contains_iff_mem, fieldLocs, List.mem_map, List.mem_filter, bne_iff_ne]
        exact ⟨(k, loc), ⟨lookup_mem_pair hm, hne⟩, rfl⟩
      | spine y p' =>
        cases p' with
        | nil =>
          simp only [regionSub, Bool.and_eq_true, beq_iff_eq] at hsub
          rcases hsub with ⟨rfl, rfl⟩
          simp only [Region.mem, beq_iff_eq] at hm
          simp only [Region.mem, HeapKnowledge.readPath, beq_iff_eq]
          cases hv : ρ x
          case objAt fs cc oid =>
            rw [hv] at hm; simp only [fieldsOf] at hm; simp [HeapKnowledge.elementsOf, hm]
          all_goals (rw [hv] at hm; simp [fieldsOf] at hm)
        | cons _ _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
      | path y p' k' =>
        simp only [regionSub, beq_iff_eq] at hsub; cases hsub
        simpa [Region.mem_path_nil] using hm
      | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
    | cons _ _ =>
      cases R with
      | path y p' k' => simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
      | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
  | fields x =>
    cases R with
    | fields y => simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
    | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
  | pathFields x p =>
    cases p with
    | nil =>
      rw [Region.mem_pathFields_nil] at hm
      cases R with
      | fields y => simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
      | pathFields y p' =>
        simp only [regionSub, beq_iff_eq] at hsub; cases hsub
        simpa [Region.mem_pathFields_nil] using hm
      | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
    | cons _ _ =>
      cases R with
      | pathFields y p' => simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
      | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
  | spine x p =>
    cases p with
    | nil =>
      cases R with
      | spine y p' =>
        cases p' with
        | nil => simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
        | cons _ _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
      | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
    | cons _ _ =>
      cases R with
      | spine y p' => simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
      | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
  | cells x =>
    cases R with
    | cells y => simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
    | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
  | pathCells x p =>
    cases p with
    | nil =>
      rw [Region.mem_pathCells_nil] at hm
      cases R with
      | cells y => simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
      | pathCells y p' =>
        simp only [regionSub, beq_iff_eq] at hsub; cases hsub
        simpa [Region.mem_pathCells_nil] using hm
      | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
    | cons _ _ =>
      cases R with
      | pathCells y p' => simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
      | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
  | cls c =>
    cases R with
    | cls c' => simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
    | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
  | elemSpines x p =>
    cases R with
    | elemSpines y p' => simp only [regionSub, beq_iff_eq] at hsub; cases hsub; exact hm
    | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub
  | all =>
    cases R with
    | all => exact hm
    | _ => simp only [regionSub, beq_iff_eq] at hsub; cases hsub

/-- An entry `(r, δ)` of a fact's support is covered by a kept footprint `S`
when `S` contains `(r, δ)` directly or keeps a region containing `r`. -/
def entryCoveredBy (S : Footprint) (e : Region × Change) : Bool :=
  S.contains e || S.any fun p => p.2 == .keep && regionSub e.1 p.1

theorem entryCoveredBy_supported {S T : Footprint} {ρ : Env} {h h' : Heap}
    (hS : Supported S ρ h h') (hcov : T.all (entryCoveredBy S) = true) :
    Supported T ρ h h' := by
  intro e he loc v hmem hv
  have h1 := List.all_eq_true.mp hcov e he
  simp only [entryCoveredBy, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at h1
  rcases h1 with hmemS | ⟨⟨R, γ⟩, hR, hγ, hsub⟩
  · exact hS e hmemS loc v hmem hv
  · subst hγ
    obtain ⟨v', hv', hkeep⟩ := hS (R, .keep) hR loc v (regionSub_mem hsub hmem) hv
    simp only [Change.Holds] at hkeep
    rw [hkeep] at hv'
    exact ⟨v, hv', Change.Holds.refl e.2 h.length v⟩

/-! ## References in source terms below the entry mark -/

/-- Every location reference (other than identities) in a term lies below `m`. -/
def TmRefsBelow (m : Nat) (t : Tm) : Prop :=
  ∀ u ∈ vals allC .all true true t, ∀ l, Leaves allC u l → l < m

/-- A term valid at a world `W` of a well-formed heap `h₀` has `TmRefsBelow h₀.length`. -/
theorem refsOk_tmRefsBelow {n : Nat} {W : WorldT n} {h₀ : Heap} {t : Tm}
    (hok : HeapOk n W h₀) (href : RefsOk W t) : TmRefsBelow h₀.length t := by
  intro u hu l hl
  have hlenW : (entries W).length = h₀.length := by
    have := hok.1.1; simp only [toList, List.length_map] at this; exact this.symm
  exact leaves_lt_of_refsOkN hlenW (vals_refsOkN (RefsOk.refsOkN href) hu) hl

/-- Every free slot of `t` at depth `d` satisfies `p`. -/
def FreeSlotsOk (d : Nat) (p : Nat → Prop) : Tm → Prop
  | .var i => d ≤ i → p (i - d)
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => True
  | .objAt _ .absent _ => True
  | .makeAt .absent _ args => ∀ a ∈ args, FreeSlotsOk d p a
  | .objAt _ (.bound t r pre) _ => FreeSlotsOk d p t ∧ FreeSlotsOk d p r ∧ ∀ a ∈ pre, FreeSlotsOk d p a
  | .makeAt (.bound t r pre) _ args =>
      FreeSlotsOk d p t ∧ FreeSlotsOk d p r ∧ (∀ a ∈ pre, FreeSlotsOk d p a) ∧ (∀ a ∈ args, FreeSlotsOk d p a)
  | .objAt _ (.graph _ _ _ _ caps _ _ _) _ => ∀ a ∈ caps, FreeSlotsOk d p a
  | .makeAt (.graph _ _ _ _ caps _ _ _) _ args =>
      (∀ a ∈ caps, FreeSlotsOk d p a) ∧ (∀ a ∈ args, FreeSlotsOk d p a)
  | .letE a b => FreeSlotsOk d p a ∧ FreeSlotsOk (d + 1) p b
  | .invoke f r args => FreeSlotsOk d p f ∧ FreeSlotsOk d p r ∧ ∀ a ∈ args, FreeSlotsOk d p a
  | .construct f args => FreeSlotsOk d p f ∧ ∀ a ∈ args, FreeSlotsOk d p a
  | .writeAt _ a b | .arith _ a b | .elemAt a b | .indexAt a b | .merge _ a b | .makeKey a b =>
      FreeSlotsOk d p a ∧ FreeSlotsOk d p b
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => FreeSlotsOk d p a
  | .setElem a b c => FreeSlotsOk d p a ∧ FreeSlotsOk d p b ∧ FreeSlotsOk d p c
  | .arrLit args => ∀ a ∈ args, FreeSlotsOk d p a
  | .ite c a b => FreeSlotsOk d p c ∧ FreeSlotsOk d p a ∧ FreeSlotsOk d p b
  | _ => False

/-- `NoPriv` for an object whose own field locations stay outside `Priv` and
whose code's values all satisfy `NoPriv`. -/
private theorem noPriv_objAt {Priv : Nat → Prop} {fs : List (PropKey × Nat)} {cc : CallCode} {oid : Nat}
    (hnext : ∀ a l, next (.objAt fs cc oid) a = some l → ¬ Priv l)
    (hcode : ∀ x ∈ codeVals allC (.objAt fs cc oid), NoPriv Priv x) :
    NoPriv Priv (.objAt fs cc oid) := by
  intro l ⟨y, hcr, a, hn⟩
  cases hcr with
  | refl => exact hnext a l hn
  | step hx hcr' => exact (hcode _ hx).of_codeReach hcr' l ⟨y, .refl y, a, hn⟩

/-- Instantiating a term whose own constants stay below `m` (`TmRefsBelow m`)
and whose free slots all hold `NoPriv Priv` values produces a term whose every
root in `vals allC .all true true` satisfies `NoPriv Priv`. -/
theorem instantiate_noPriv {Priv : Nat → Prop} {m : Nat} {ρ : Env}
    (hge : ∀ l, Priv l → m ≤ l) :
    ∀ (t : Tm) (d : Nat), TmRefsBelow m t →
      FreeSlotsOk d (fun i => isVal (ρ i) = true ∧ NoPriv Priv (ρ i)) t →
      ∀ x ∈ vals allC .all true true (instantiate d ρ t), NoPriv Priv x := by
  intro t
  induction t using Tm.induct
  case var i =>
    intro d _ hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate] at hx
    split at hx
    · simp [vals] at hx
    · rename_i hlt
      obtain ⟨hv, hno⟩ := hf (Nat.le_of_not_lt hlt)
      exact hno.of_codeReach (vals_codeReach hv hx)
  case objAbsent fs oid =>
    intro d hlt _ x hx
    simp only [instantiate] at hx
    exact NoPriv.of_lt hge (hlt x hx)
  case objBound fs oid t r pre iht ihr ihp =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    have hself : NoPriv Priv (.objAt fs (.bound t r pre) oid) :=
      NoPriv.of_lt hge (hlt _ (by rw [vals_objAt]; exact List.mem_cons_self))
    have hpart : ∀ y ∈ codeVals allC (.objAt fs (.bound t r pre) oid), ∀ l, Leaves allC y l → l < m :=
      fun y hy => hlt y (by rw [vals_objAt]; exact List.mem_cons_of_mem _ hy)
    simp only [codeVals, List.mem_append, valsArgs_eq, List.mem_flatMap] at hpart
    have hcode : ∀ y ∈ codeVals allC (.objAt fs (.bound (instantiate d ρ t) (instantiate d ρ r)
        (instantiateArgs d ρ pre)) oid), NoPriv Priv y := by
      intro y hy
      simp only [codeVals, List.mem_append, valsArgs_eq, List.mem_flatMap, instantiateArgs_eq_map,
        List.mem_map] at hy
      rcases hy with (hy | hy) | ⟨_, ⟨p, hp, rfl⟩, hy⟩
      · exact iht d (fun z hz => hpart z (.inl (.inl hz))) hf.1 y hy
      · exact ihr d (fun z hz => hpart z (.inl (.inr hz))) hf.2.1 y hy
      · exact ihp p hp d (fun z hz => hpart z (.inr ⟨p, hp, hz⟩)) (hf.2.2 p hp) y hy
    simp only [instantiate] at hx
    rw [vals_objAt] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · refine noPriv_objAt (fun a l hn => ?_) hcode
      rw [objAt_next_eq rfl] at hn
      exact hself.of_next hn
    · exact hcode x hx
  case objGraph fs oid n E K st caps k r comp ihE ihc =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    have hself : NoPriv Priv (.objAt fs (.graph n E K st caps k r comp) oid) :=
      NoPriv.of_lt hge (hlt _ (by rw [vals_objAt]; exact List.mem_cons_self))
    have hpart : ∀ y ∈ codeVals allC (.objAt fs (.graph n E K st caps k r comp) oid), ∀ l, Leaves allC y l → l < m :=
      fun y hy => hlt y (by rw [vals_objAt]; exact List.mem_cons_of_mem _ hy)
    simp only [codeVals, allC, Bool.false_eq_true, ↓reduceIte, List.mem_append, valsArgs_eq,
      List.mem_flatMap] at hpart
    have hcode : ∀ y ∈ codeVals allC (.objAt fs (.graph n E K st (instantiateArgs d ρ caps) k r comp) oid),
        NoPriv Priv y := by
      intro y hy
      simp only [codeVals, allC, Bool.false_eq_true, ↓reduceIte, List.mem_append, valsArgs_eq,
        List.mem_flatMap, instantiateArgs_eq_map, List.mem_map] at hy
      rcases hy with ⟨e, he, hy⟩ | ⟨_, ⟨p, hp, rfl⟩, hy⟩
      · exact NoPriv.of_lt hge (hpart y (.inl ⟨e, he, hy⟩))
      · exact ihc p hp d (fun z hz => hpart z (.inr ⟨p, hp, hz⟩)) (hf p hp) y hy
    simp only [instantiate] at hx
    rw [vals_objAt] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · refine noPriv_objAt (fun a l hn => ?_) hcode
      rw [objAt_next_eq rfl] at hn
      exact hself.of_next hn
    · exact hcode x hx
  case alloc ns args iha =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, valsArgs_eq, instantiateArgs_eq_map, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨_, ⟨a, ha, rfl⟩, hx⟩ := hx
    exact iha a ha d (fun z hz => hlt z (by simp only [vals, valsArgs_eq, List.mem_flatMap]; exact ⟨a, ha, hz⟩))
      (hf a ha) x hx
  case makeBound t r pre ns args iht ihr ihp iha =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append, valsArgs_eq, instantiateArgs_eq_map, List.mem_flatMap,
      List.mem_map] at hx
    have hlt' : ∀ z, (z ∈ vals allC .all true true t ∨ z ∈ vals allC .all true true r ∨
        (∃ p ∈ pre, z ∈ vals allC .all true true p) ∨ (∃ a ∈ args, z ∈ vals allC .all true true a)) →
        ∀ l, Leaves allC z l → l < m := by
      intro z hz; exact hlt z (by
        simp only [vals, List.mem_append, valsArgs_eq, List.mem_flatMap]
        rcases hz with h | h | h | h
        · exact .inl (.inl (.inl h))
        · exact .inl (.inl (.inr h))
        · exact .inl (.inr h)
        · exact .inr h)
    rcases hx with ((hx | hx) | ⟨_, ⟨p, hp, rfl⟩, hx⟩) | ⟨_, ⟨a, ha, rfl⟩, hx⟩
    · exact iht d (fun z hz => hlt' z (.inl hz)) hf.1 x hx
    · exact ihr d (fun z hz => hlt' z (.inr (.inl hz))) hf.2.1 x hx
    · exact ihp p hp d (fun z hz => hlt' z (.inr (.inr (.inl ⟨p, hp, hz⟩)))) (hf.2.2.1 p hp) x hx
    · exact iha a ha d (fun z hz => hlt' z (.inr (.inr (.inr ⟨a, ha, hz⟩)))) (hf.2.2.2 a ha) x hx
  case makeGraph n E K st caps k r comp ns args ihE ihc iha =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, allC, Bool.not_false, Bool.and_self, ↓reduceIte, List.mem_append, valsArgs_eq,
      instantiateArgs_eq_map, List.mem_flatMap, List.mem_map] at hx
    have hlt' : ∀ z, ((∃ e ∈ E, z ∈ vals allC .all true true e) ∨
        (∃ p ∈ caps, z ∈ vals allC .all true true p) ∨ (∃ a ∈ args, z ∈ vals allC .all true true a)) →
        ∀ l, Leaves allC z l → l < m := by
      intro z hz; exact hlt z (by
        simp only [vals, allC, Bool.not_false, Bool.and_self, ↓reduceIte, List.mem_append, valsArgs_eq, List.mem_flatMap]
        rcases hz with h | h | h
        · exact .inl (.inl h)
        · exact .inl (.inr h)
        · exact .inr h)
    rcases hx with (⟨e, he, hx⟩ | ⟨_, ⟨p, hp, rfl⟩, hx⟩) | ⟨_, ⟨a, ha, rfl⟩, hx⟩
    · exact NoPriv.of_lt hge (hlt' x (.inl ⟨e, he, hx⟩))
    · exact ihc p hp d (fun z hz => hlt' z (.inr (.inl ⟨p, hp, hz⟩))) (hf.1 p hp) x hx
    · exact iha a ha d (fun z hz => hlt' z (.inr (.inr ⟨a, ha, hz⟩))) (hf.2 a ha) x hx
  case letE a b iha ihb =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf.1 x hx
    · exact ihb (d + 1) (fun z hz => hlt z (by simp [vals, hz])) hf.2 x hx
  case invoke f r args ihf ihr iha =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append, valsArgs_eq, instantiateArgs_eq_map, List.mem_flatMap,
      List.mem_map] at hx
    rcases hx with (hx | hx) | ⟨_, ⟨a, ha, rfl⟩, hx⟩
    · exact ihf d (fun z hz => hlt z (by simp [vals, hz])) hf.1 x hx
    · exact ihr d (fun z hz => hlt z (by simp [vals, hz])) hf.2.1 x hx
    · exact iha a ha d (fun z hz => hlt z (by
        simp only [vals, List.mem_append, valsArgs_eq, List.mem_flatMap]; exact .inr ⟨a, ha, hz⟩))
        (hf.2.2 a ha) x hx
  case construct f args ihf iha =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append, valsArgs_eq, instantiateArgs_eq_map, List.mem_flatMap,
      List.mem_map] at hx
    rcases hx with hx | ⟨_, ⟨a, ha, rfl⟩, hx⟩
    · exact ihf d (fun z hz => hlt z (by simp [vals, hz])) hf.1 x hx
    · exact iha a ha d (fun z hz => hlt z (by
        simp only [vals, List.mem_append, valsArgs_eq, List.mem_flatMap]; exact .inr ⟨a, ha, hz⟩))
        (hf.2 a ha) x hx
  case arrLit args iha =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, valsArgs_eq, instantiateArgs_eq_map, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨_, ⟨a, ha, rfl⟩, hx⟩ := hx
    exact iha a ha d (fun z hz => hlt z (by simp only [vals, valsArgs_eq, List.mem_flatMap]; exact ⟨a, ha, hz⟩))
      (hf a ha) x hx
  case setElem a b c iha ihb ihc =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf.1 x hx
    · exact ihb d (fun z hz => hlt z (by simp [vals, hz])) hf.2.1 x hx
    · exact ihc d (fun z hz => hlt z (by simp [vals, hz])) hf.2.2 x hx
  case ite c a b ihc iha ihb =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact ihc d (fun z hz => hlt z (by simp [vals, hz])) hf.1 x hx
    · exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf.2.1 x hx
    · exact ihb d (fun z hz => hlt z (by simp [vals, hz])) hf.2.2 x hx
  case write f a b iha ihb =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf.1 x hx
    · exact ihb d (fun z hz => hlt z (by simp [vals, hz])) hf.2 x hx
  case arith op a b iha ihb =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf.1 x hx
    · exact ihb d (fun z hz => hlt z (by simp [vals, hz])) hf.2 x hx
  case elemAt a b iha ihb =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf.1 x hx
    · exact ihb d (fun z hz => hlt z (by simp [vals, hz])) hf.2 x hx
  case index a b iha ihb =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf.1 x hx
    · exact ihb d (fun z hz => hlt z (by simp [vals, hz])) hf.2 x hx
  case merge dr a b iha ihb =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf.1 x hx
    · exact ihb d (fun z hz => hlt z (by simp [vals, hz])) hf.2 x hx
  case makeKey a b iha ihb =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals, List.mem_append] at hx
    rcases hx with hx | hx
    · exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf.1 x hx
    · exact ihb d (fun z hz => hlt z (by simp [vals, hz])) hf.2 x hx
  case read f a iha =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals] at hx
    exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf x hx
  case test k a iha =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals] at hx
    exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf x hx
  case lenOf a iha =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals] at hx
    exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf x hx
  case spread a iha =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals] at hx
    exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf x hx
  case throw a iha =>
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
    simp only [instantiate, vals] at hx
    exact iha d (fun z hz => hlt z (by simp [vals, hz])) hf x hx
  all_goals
    intro d hlt hf x hx
    simp only [FreeSlotsOk] at hf
  all_goals simp [instantiate, vals] at hx

/-- Restrict `instantiate_noPriv` from `.all true true` to `.empty true false`. -/
theorem instantiate_noPriv_empty {Priv : Nat → Prop} {m : Nat} {ρ : Env}
    (hge : ∀ l, Priv l → m ≤ l)
    {t : Tm} (hlt : TmRefsBelow m t)
    (hf : FreeSlotsOk 0 (fun i => isVal (ρ i) = true ∧ NoPriv Priv (ρ i)) t) :
    ∀ x ∈ vals allC .empty true false (instantiate 0 ρ t), NoPriv Priv x :=
  fun x hx => instantiate_noPriv hge t 0 hlt hf x (vals_all allC _ .empty true false hx)

/-! ## Fresh allocation and field-write lemmas -/

private theorem slots_snd_bounds : ∀ (base : Nat) (ns : List PropKey) (p : PropKey × Nat),
    p ∈ slots base ns → base ≤ p.2 ∧ p.2 < base + ns.length
  | _, [], _, h => by simp [slots] at h
  | base, _ :: ns, p, h => by
    simp only [slots, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨Nat.le_refl _, by simp⟩
    · have ⟨h1, h2⟩ := slots_snd_bounds (base + 1) ns p h
      exact ⟨by omega, by simp; omega⟩

/-- Evaluating `.makeAt .absent ns args` to a value allocates every field
location of the result in `[h.length, h'.length)`. -/
theorem steps_makeAt_fresh : ∀ {k : Nat} {h h' : Heap} {ns : List PropKey} {args : List Tm} {v : Val},
    Steps k h (.makeAt .absent ns args) h' v → isVal v = true →
    ∀ loc ∈ fieldLocs v, h.length ≤ loc ∧ loc < h'.length := by
  intro k
  induction k with
  | zero =>
    intro h h' ns args v hst hv
    cases hst; simp [isVal] at hv
  | succ k ih =>
    intro h h' ns args v hst hv
    cases hst with
    | next hs hrest =>
      have hlen := Footprints.step_length_le hs
      cases hs with
      | makeArg _ _ hs' =>
        intro loc hloc
        have ⟨h1, h2⟩ := ih hrest hv loc hloc
        exact ⟨Nat.le_trans hlen h1, h2⟩
      | makeFields _ hne =>
        have hv0 : isVal (.objAt (slots h.length ns) .absent (h.length + args.length)) = true := rfl
        cases hrest with
        | refl =>
          intro loc hloc
          simp only [fieldLocs, fieldsOf, List.mem_map, List.mem_filter] at hloc
          obtain ⟨p, ⟨hp, _⟩, rfl⟩ := hloc
          have ⟨h1, h2⟩ := slots_snd_bounds h.length ns p hp
          exact ⟨h1, by simp; omega⟩
        | next hs2 _ => exact absurd hs2 (value_no_step hv0)

/-- Evaluating `.arrLit args` to a value produces `.arr ls` whose every cell
location lies in `[h.length, h'.length)`. -/
theorem steps_arrLit_fresh : ∀ {k : Nat} {h h' : Heap} {args : List Tm} {v : Val},
    Steps k h (.arrLit args) h' v → isVal v = true →
    ∃ ls, v = .arr ls ∧ ∀ loc, some loc ∈ ls → h.length ≤ loc ∧ loc < h'.length := by
  intro k
  induction k with
  | zero =>
    intro h h' args v hst hv
    cases hst; simp [isVal] at hv
  | succ k ih =>
    intro h h' args v hst hv
    cases hst with
    | next hs hrest =>
      have hlen := Footprints.step_length_le hs
      cases hs with
      | arrArg _ _ hs' =>
        obtain ⟨ls, rfl, hls⟩ := ih hrest hv
        exact ⟨ls, rfl, fun loc hl => ⟨Nat.le_trans hlen (hls loc hl).1, (hls loc hl).2⟩⟩
      | arrSpread _ _ _ =>
        obtain ⟨ls, rfl, hls⟩ := ih hrest hv
        exact ⟨ls, rfl, fun loc hl => ⟨Nat.le_trans hlen (hls loc hl).1, (hls loc hl).2⟩⟩
      | arrAlloc _ _ =>
        cases hrest with
        | refl =>
          refine ⟨elemSlots h.length args.length, rfl, fun loc hl => ?_⟩
          simp only [elemSlots, List.mem_map, Option.some.injEq, List.mem_range] at hl
          obtain ⟨j, hj, rfl⟩ := hl
          exact ⟨by omega, by simp; omega⟩
        | next hs2 _ => exact absurd hs2 (value_no_step (by rfl : isVal (.arr _) = true))
      | arrAllocThrow _ _ =>
        cases hrest with
        | refl => simp [isVal] at hv
        | next hs2 _ => exact absurd hs2 (raises_no_step (Raises.throwV (by rfl) (by rfl)))

/-- Evaluating `.makeAt .absent [arraySpineKey, protoField] [sval, pval]` where
`sval = .arr ls` and `pval` is a value allocates the object fields in
`[h.length, h'.length)`, sets `elementsOf v = some h.length`, and gives
`spineCells h' v = ls`. -/
theorem steps_makeArrObj_fresh {k : Nat} {h h' : Heap} {ls : List (Option Nat)} {pval : Tm} {v : Val}
    (hpval : isVal pval = true) (hv : isVal v = true)
    (hst : Steps k h (.makeAt .absent [arraySpineKey, CallArguments.protoField] [.arr ls, pval]) h' v) :
    (∀ loc ∈ fieldLocs v, h.length ≤ loc ∧ loc < h'.length) ∧
    (∀ loc, HeapKnowledge.elementsOf v = some loc → h.length ≤ loc ∧ loc < h'.length) ∧
    (∀ loc, some loc ∈ spineCells h' v → some loc ∈ ls) := by
  cases hst with
  | refl => simp [isVal] at hv
  | next hs hrest =>
    cases hs with
    | @makeArg _ _ _ idx _ _ _ _ ha _ hs' =>
      cases idx with
      | zero =>
        simp at ha; subst ha
        exact absurd hs' (value_no_step (by rfl : isVal (.arr ls) = true))
      | succ j =>
        cases j with
        | zero =>
          simp at ha; subst ha
          exact absurd hs' (value_no_step hpval)
        | succ _ => simp at ha
    | makeFields _ _ =>
      have hv0 : isVal (.objAt (slots h.length [arraySpineKey, CallArguments.protoField]) .absent (h.length + 2)) = true := rfl
      cases hrest with
      | refl =>
        refine ⟨?_, ?_, ?_⟩
        · intro loc hloc
          simp only [fieldLocs, fieldsOf, slots, List.mem_map, List.mem_filter] at hloc
          obtain ⟨p, ⟨hp, _⟩, rfl⟩ := hloc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact ⟨Nat.le_refl _, by simp⟩
          · exact ⟨by omega, by simp⟩
        · intro loc hloc
          simp only [HeapKnowledge.elementsOf, slots, List.lookup, beq_self_eq_true, Option.some.injEq] at hloc
          subst hloc
          exact ⟨Nat.le_refl _, by simp⟩
        · intro loc hloc
          simp only [spineCells, fieldsOf, slots, List.lookup, beq_self_eq_true,
            HeapKnowledge.descriptorSpine, entriesAt, List.append_nil] at hloc
          have hget : (h ++ [.arr ls, pval] ++ [.nul])[h.length]? = some (.arr ls) := by
            rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
            simp
          rw [hget] at hloc
          simpa [spineEntries] using hloc
      | next hs2 _ => exact absurd hs2 (value_no_step hv0)

/-- Evaluating `.merge d a b` to a value allocates every field location of `v`
in `[h.length, h'.length)`. -/
theorem steps_merge_fresh : ∀ {k : Nat} {h h' : Heap} {d : List PropKey} {a b : Tm} {v : Val},
    Steps k h (.merge d a b) h' v → isVal v = true →
    ∀ loc ∈ fieldLocs v, h.length ≤ loc ∧ loc < h'.length := by
  intro k
  induction k with
  | zero =>
    intro h h' d a b v hst hv
    cases hst; simp [isVal] at hv
  | succ k ih =>
    intro h h' d a b v hst hv
    cases hst with
    | next hs hrest =>
      have hlen := Footprints.step_length_le hs
      cases hs with
      | mergeC1 _ =>
        intro loc hloc
        have ⟨h1, h2⟩ := ih hrest hv loc hloc
        exact ⟨Nat.le_trans hlen h1, h2⟩
      | mergeC2 _ _ =>
        intro loc hloc
        have ⟨h1, h2⟩ := ih hrest hv loc hloc
        exact ⟨Nat.le_trans hlen h1, h2⟩
      | mergeV _ _ _ =>
        intro loc hloc
        have ⟨h1, h2⟩ := steps_makeAt_fresh hrest hv loc hloc
        exact ⟨Nat.le_trans hlen h1, h2⟩

/-- Evaluating `.makeKey a b` to a value allocates every field location of `v`
in `[h.length, h'.length)`. -/
theorem steps_makeKey_fresh : ∀ {k : Nat} {h h' : Heap} {a b : Tm} {v : Val},
    Steps k h (.makeKey a b) h' v → isVal v = true →
    ∀ loc ∈ fieldLocs v, h.length ≤ loc ∧ loc < h'.length := by
  intro k
  induction k with
  | zero =>
    intro h h' a b v hst hv
    cases hst; simp [isVal] at hv
  | succ k ih =>
    intro h h' a b v hst hv
    cases hst with
    | next hs hrest =>
      have hlen := Footprints.step_length_le hs
      cases hs with
      | makeKeyC1 _ =>
        intro loc hloc
        have ⟨h1, h2⟩ := ih hrest hv loc hloc
        exact ⟨Nat.le_trans hlen h1, h2⟩
      | makeKeyC2 _ _ =>
        intro loc hloc
        have ⟨h1, h2⟩ := ih hrest hv loc hloc
        exact ⟨Nat.le_trans hlen h1, h2⟩
      | makeKeyV _ _ =>
        intro loc hloc
        have ⟨h1, h2⟩ := steps_makeAt_fresh hrest hv loc hloc
        exact ⟨Nat.le_trans hlen h1, h2⟩

/-- Evaluating `.writeAt f lhs rhs` where `lhs` and `rhs` are values: if
`f ≠ arraySpineKey` and either `NoPriv Priv rhs` or `∀ loc ∈ fieldLocs lhs, Priv loc`,
then `h'.length = h.length`, `ClosedOut h' Priv` holds, and every valid object's
`spineCells` is unchanged (`SlotRole` separates non-spine keys from spines). -/
theorem steps_writeAt_val_confined {n k : Nat} {W : WorldT n} {h h' : Heap} {f : PropKey} {lhs rhs v : Val}
    {Priv : Nat → Prop} (hlhs : isVal lhs = true) (hrhs : isVal rhs = true) (hv : isVal v = true)
    (hf : f ≠ arraySpineKey) (hrefL : RefsOk W lhs)
    (hclosed : ClosedOut h Priv)
    (hcond : NoPriv Priv rhs ∨ ∀ loc ∈ fieldLocs lhs, Priv loc)
    (hst : Steps k h (.writeAt f lhs rhs) h' v) :
    h'.length = h.length ∧
    ClosedOut h' Priv ∧
    (∀ loc, (∀ x_loc ∈ fieldLocs lhs, loc ≠ x_loc) → h'[loc]? = h[loc]?) ∧
    (∀ obj, RefsOk W obj → spineCells h' obj = spineCells h obj) := by
  cases hst with
  | refl => simp [isVal] at hv
  | next hs hrest =>
    cases hs with
    | writeC1 hs' => exact absurd hs' (value_no_step hlhs)
    | writeC2 _ hs' => exact absurd hs' (value_no_step hrhs)
    | @writeField oid _ fs cc loc _ _ _ hlu hlt =>
      cases hrest with
      | refl =>
        have hloc_fld : loc ∈ fieldLocs (.objAt fs cc oid) := by
          simp only [fieldLocs, fieldsOf, List.mem_map, List.mem_filter, bne_iff_ne]
          exact ⟨(f, loc), ⟨lookup_mem_pair hlu, hf⟩, rfl⟩
        have hloc_role : SlotRole f (roleAt W loc) :=
          hrefL _ (TolerantFrames.Reach.slot_mem_refs (c := cc) (i := oid) (lookup_mem_pair hlu))
        have hne_spine : ∀ {s : Nat} {sf}, roleAt W s = some (.spine sf) → s ≠ loc := by
          intro s sf hrs heq
          subst heq
          rw [hrs] at hloc_role
          cases sf <;> simp only [SlotRole] at hloc_role
          exact hf hloc_role
        refine ⟨by simp, ?_, ?_, ?_⟩
        · intro m hm hnp u hu
          by_cases hml : m = loc
          · subst hml
            rw [List.getElem?_set_self'] at hu
            cases hh : h[m]? with
            | none => rw [hh] at hu; cases hu
            | some _ =>
              rw [hh] at hu; simp at hu; subst hu
              rcases hcond with hno | hown
              · exact hno
              · exact absurd (hown m hloc_fld) hnp
          · rw [List.getElem?_set_ne (Ne.symm hml)] at hu
            exact hclosed m (by simp at hm; omega) hnp u hu
        · intro m hm
          exact List.getElem?_set_ne (Ne.symm (hm loc hloc_fld))
        · intro obj hobj
          unfold spineCells
          congr 1
          · cases ho : (fieldsOf obj).lookup arraySpineKey with
            | none => rfl
            | some s =>
              have hs_ne : s ≠ loc := by
                cases obj with
                | objAt fs' cc' oid' =>
                  simp only [fieldsOf] at ho
                  have hsr : SlotRole arraySpineKey (roleAt W s) :=
                    hobj _ (TolerantFrames.Reach.slot_mem_refs (c := cc') (i := oid') (lookup_mem_pair ho))
                  cases hrole : roleAt W s with
                  | none => rw [hrole] at hsr; exact hsr.elim
                  | some r =>
                    cases r with
                    | spine sf => exact hne_spine hrole
                    | field _ => rw [hrole] at hsr; exact (hsr.2 rfl).elim
                    | cell _ => rw [hrole] at hsr; exact (hsr.2 rfl).elim
                    | elem | identity => rw [hrole] at hsr; exact hsr.elim
                | _ => simp [fieldsOf] at ho
              simp [entriesAt, List.getElem?_set_ne (Ne.symm hs_ne)]
          · cases hd : HeapKnowledge.descriptorSpine obj with
            | none => rfl
            | some s =>
              have hs_ne : s ≠ loc := by
                cases obj with
                | objAt fs' cc' oid' =>
                  cases cc' with
                  | view s' fmt len =>
                    simp only [HeapKnowledge.descriptorSpine, Option.some.injEq] at hd
                    subst hd
                    have hsr := hobj _ (by simp [refs] :
                      Ref.view s' fmt len (fs'.lookup arraySpineKey).isNone ∈ refs (.objAt fs' (.view s' fmt len) oid'))
                    exact hne_spine hsr.2
                  | _ => simp [HeapKnowledge.descriptorSpine] at hd
                | _ => simp [HeapKnowledge.descriptorSpine] at hd
              simp [entriesAt, List.getElem?_set_ne (Ne.symm hs_ne)]
      | next hs2 _ => exact absurd hs2 (value_no_step (by rfl : isVal .nul = true))


/-- Splitting a `Steps` run of `.letE a b` that ends at a value into the run of
`a` to a value `u` and the run of `subst 0 u b` to `v`. -/
private theorem steps_letE_split {k : Nat} {h h' : Heap} {a b v : Tm}
    (hv : isVal v = true) (hst : Steps k h (.letE a b) h' v) :
    ∃ k₁ k₂ h₁ u, isVal u = true ∧ Steps k₁ h a h₁ u ∧ Steps k₂ h₁ (subst 0 u b) h' v := by
  induction k generalizing h a with
  | zero =>
    cases hst
    simp [isVal] at hv
  | succ k ih =>
    cases hst with
    | next hs hr =>
      cases hs with
      | letC hs₁ =>
        obtain ⟨k₁, k₂, h₁, u, hu, h1, h2⟩ := ih hr
        exact ⟨k₁ + 1, k₂, h₁, u, hu, .next hs₁ h1, h2⟩
      | letV hu =>
        exact ⟨0, k, h, a, hu, .refl, hr⟩

/-- Evaluating `.letE (.arrLit args) (.makeAt .absent [arraySpineKey, proto] [.var 0, pval])`
allocates the spine, its cells, and the wrapper object's own fields all at or
above `h.length`. -/
theorem steps_letArrObj_fresh {k : Nat} {h h' : Heap} {args : List Tm} {pval : Tm} {v : Val}
    (hpval : isVal pval = true) (hscp : Scoped 0 pval) (hv : isVal v = true)
    (hst : Steps k h (.letE (.arrLit args)
      (.makeAt .absent [arraySpineKey, CallArguments.protoField] [.var 0, pval])) h' v) :
    (∀ loc ∈ fieldLocs v, h.length ≤ loc ∧ loc < h'.length) ∧
    (∀ loc, HeapKnowledge.elementsOf v = some loc → h.length ≤ loc ∧ loc < h'.length) ∧
    (∀ loc, some loc ∈ spineCells h' v → h.length ≤ loc ∧ loc < h'.length) := by
  obtain ⟨k₁, k₂, h₁, u, hu, h1, h2⟩ := steps_letE_split hv hst
  obtain ⟨ls, rfl, hls⟩ := steps_arrLit_fresh h1 hu
  have hlen1 : h.length ≤ h₁.length := by
    have key : ∀ {j a b t₁ t₂}, Steps j a t₁ b t₂ → a.length ≤ b.length := by
      intro j a b t₁ t₂ hr
      induction hr with
      | refl => exact Nat.le_refl _
      | next hs _ ih => exact Nat.le_trans (Footprints.step_length_le hs) ih
    exact key h1
  have hlen2 : h₁.length ≤ h'.length := by
    have key : ∀ {j a b t₁ t₂}, Steps j a t₁ b t₂ → a.length ≤ b.length := by
      intro j a b t₁ t₂ hr
      induction hr with
      | refl => exact Nat.le_refl _
      | next hs _ ih => exact Nat.le_trans (Footprints.step_length_le hs) ih
    exact key h2
  simp only [subst, substArgs_eq_map, List.map_cons, List.map_nil,
    subst_above hscp (Nat.zero_le 0)] at h2
  obtain ⟨hff, hfe, hfc⟩ := steps_makeArrObj_fresh hpval hv h2
  refine ⟨fun loc hl => ⟨Nat.le_trans hlen1 (hff loc hl).1, (hff loc hl).2⟩,
    fun loc hl => ⟨Nat.le_trans hlen1 (hfe loc hl).1, (hfe loc hl).2⟩,
    fun loc hl => ?_⟩
  have hmem := hfc loc hl
  exact ⟨(hls loc hmem).1, Nat.lt_of_lt_of_le (hls loc hmem).2 hlen2⟩

end Verification.Confinement
