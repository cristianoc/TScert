import Verification.Semantics.FootprintProvenance
import Verification.Programs.PointClaims

/-! # Provenance stamps in the checker's knowledge

A graph point's **stamps** bound its slots' locations against **marks**, ghost
heap lengths at allocations (`Footprints.MarksOk`, `StampsHold`). `after (x, m)`
says every own location of slot `x` is at least mark `m`; `before (y, m, ks)`
says the fields `ks` of slot `y` lie below mark `m`. The valuation of the
marks is existentially quantified at each point, monotone and at most the
current heap's length.

Stamps are the one provenance analysis of the checker. Two fields are apart
when `after` of one slot is at least `before` of the other and the second
field is among those its `before` bounds (`apart_sound`, from
`stamps_separate`). An allocation stamps its result `after` a new mark equal
to the heap's length, and the typed fields of the context's slots `before`
it (`alloc_holds`). An edge renames marks by a monotone map the check
computes (`check_sound`). -/
namespace Verification.HeapStamps
open Footprints

/-- The own locations of a value: an object's field locations, none of a
primitive. -/
def ownLocs (v : Tm) : List Nat := (fieldsOf v).map Prod.snd

def fieldLoc (v : Tm) (k : PropKey) : Option Nat := (fieldsOf v).lookup k

structure Stamps where
  after : List (Nat × Nat) := []
  before : List (Nat × Nat × List PropKey) := []
  deriving DecidableEq, Repr

def Stamps.HoldsAt (s : Stamps) (μ : Nat → Nat) (ρ : Env) : Prop :=
  (∀ p ∈ s.after, ∀ l ∈ ownLocs (ρ p.1), μ p.2 ≤ l) ∧
  (∀ q ∈ s.before, ∀ k ∈ q.2.2, ∀ l, fieldLoc (ρ q.1) k = some l → l < μ q.2.1)

/-- Some monotone valuation of the marks, each at most the heap's length,
meets every stamp. -/
def Stamps.Holds (s : Stamps) (ρ : Env) (h : Heap) : Prop :=
  ∃ μ : Nat → Nat, (∀ i j, i ≤ j → μ i ≤ μ j) ∧ (∀ i, μ i ≤ h.length) ∧ s.HoldsAt μ ρ

theorem holds_empty (ρ : Env) (h : Heap) : ({} : Stamps).Holds ρ h :=
  ⟨fun _ => 0, fun _ _ _ => Nat.le_refl _, fun _ => Nat.zero_le _, by simp, by simp⟩

/-- Stamps survive a heap that only grows. -/
theorem Stamps.Holds.grow {s : Stamps} {ρ h h'} (hs : s.Holds ρ h) (hl : h.length ≤ h'.length) :
    s.Holds ρ h' := by
  obtain ⟨μ, hm, hb, ha⟩ := hs
  exact ⟨μ, hm, fun i => Nat.le_trans (hb i) hl, ha⟩

/-! ## Moving stamps with slots -/

/-- Each stamp of a source slot, at every target slot `pre` gives it. -/
def Stamps.pull (s : Stamps) (pre : Nat → List Nat) : Stamps :=
  ⟨s.after.flatMap fun p => (pre p.1).map fun j => (j, p.2),
   s.before.flatMap fun q => (pre q.1).map fun j => (j, q.2.1, q.2.2)⟩

theorem pull_holds {s : Stamps} {pre : Nat → List Nat} {ρ τ : Env} {h : Heap}
    (hs : s.Holds ρ h) (he : ∀ i j, j ∈ pre i → τ j = ρ i) : (s.pull pre).Holds τ h := by
  obtain ⟨μ, hm, hb, ha, hbf⟩ := hs
  refine ⟨μ, hm, hb, fun p hp l hl => ?_, fun q hq k hk l hl => ?_⟩
  · obtain ⟨a, ha', hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    exact ha a ha' l (by simpa [he _ _ hj] using hl)
  · obtain ⟨b, hb', hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
    exact hbf b hb' k hk l (by simpa [he _ _ hj] using hl)

/-- A pushed result shifts every slot by one. -/
def Stamps.shift (s : Stamps) : Stamps := s.pull fun i => [i + 1]

theorem shift_holds {s : Stamps} {ρ h v} (hs : s.Holds ρ h) : s.shift.Holds (push v ρ) h :=
  pull_holds hs fun i j hj => by
    simp only [List.mem_singleton] at hj
    subst hj; rfl

/-- The result slot is dropped, and every other slot moves down by one. -/
def Stamps.drop (s : Stamps) : Stamps := s.pull fun i => if i = 0 then [] else [i - 1]

theorem drop_holds {s : Stamps} {ρ h v} (hs : s.Holds (push v ρ) h) : s.drop.Holds ρ h :=
  pull_holds hs fun i j hj => by
    split at hj
    · simp at hj
    · simp only [List.mem_singleton] at hj
      subst hj
      cases i with
      | zero => contradiction
      | succ i => rfl

/-! ## Separation -/

/-- Field `f` of slot `x` is apart from field `g` of slot `y` by stamps. -/
def Stamps.apart₁ (s : Stamps) (x : Nat) (y : Nat) (g : PropKey) : Bool :=
  s.after.any fun p => p.1 == x && s.before.any fun q => q.1 == y && q.2.2.contains g && decide (q.2.1 ≤ p.2)

def Stamps.apart (s : Stamps) (x : Nat) (f : PropKey) (y : Nat) (g : PropKey) : Bool :=
  s.apart₁ x y g || s.apart₁ y x f

private theorem apart₁_sound {s : Stamps} {ρ h x y g l l'} (hs : s.Holds ρ h)
    (ha : s.apart₁ x y g = true) (hl : l ∈ ownLocs (ρ x)) (hl' : fieldLoc (ρ y) g = some l') :
    l ≠ l' := by
  obtain ⟨μ, hm, -, hA, hB⟩ := hs
  simp only [Stamps.apart₁, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.contains_iff_mem, decide_eq_true_eq] at ha
  obtain ⟨p, hp, rfl, q, hq, ⟨rfl, hg⟩, hle⟩ := ha
  have h₁ := hA p hp l hl
  have h₂ := hB q hq g hg l' hl'
  have h₃ := hm _ _ hle
  omega

/-- **Stamps separate fields.** -/
theorem apart_sound {s : Stamps} {ρ h x f y g l l'} (hs : s.Holds ρ h)
    (ha : s.apart x f y g = true) (hl : fieldLoc (ρ x) f = some l) (hl' : fieldLoc (ρ y) g = some l') :
    l ≠ l' := by
  simp only [Stamps.apart, Bool.or_eq_true] at ha
  rcases ha with ha | ha
  · exact apart₁_sound hs ha (lookup_mem_snd hl) hl'
  · exact fun he => apart₁_sound hs ha (lookup_mem_snd hl') hl he.symm

/-! ## Edges -/

/-- The source mark a target `before` stamp needs at least: the least mark
of a matching source `before`. -/
private def lowerBound (a : Stamps) (m : PointClaims.Mapping) (q : Nat × Nat × List PropKey) : Nat :=
  ((a.before.filter fun r => r.1 == PointClaims.slot m q.1 && q.2.2.all r.2.2.contains).map
    (·.2.1)).min?.getD 0

/-- The renaming of target marks to source marks: the least monotone map
meeting every target `before` stamp's lower bound. -/
def sigma (a b : Stamps) (m : PointClaims.Mapping) : List Nat :=
  let top := ((b.after.map (·.2)) ++ (b.before.map (·.2.1))).foldl max 0
  ((List.range (top + 1)).foldl (fun (acc : List Nat × Nat) i =>
    let here := (b.before.filter (·.2.1 == i)).foldl (fun c q => max c (lowerBound a m q)) acc.2
    (acc.1 ++ [here], here)) ([], 0)).1

/-- Each target stamp is implied by a source stamp at its slot under the
mapping, its marks renamed by `sigma`, which must be monotone. -/
def check (a b : Stamps) (m : PointClaims.Mapping) : Bool :=
  let σ := sigma a b m
  sortedB σ &&
  b.after.all (fun p => a.after.any fun r => r.1 == PointClaims.slot m p.1 && decide (markAt σ p.2 ≤ r.2)) &&
  b.before.all (fun q => a.before.any fun r => r.1 == PointClaims.slot m q.1 &&
    decide (r.2.1 ≤ markAt σ q.2.1) && q.2.2.all r.2.2.contains)

theorem check_sound {a b : Stamps} {m ρ h} (hc : check a b m = true) (ha : a.Holds ρ h) :
    b.Holds (PointClaims.mapEnv m ρ) h := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hc
  obtain ⟨⟨hσ, hA⟩, hB⟩ := hc
  obtain ⟨μ, hm, hb, hAs, hBs⟩ := ha
  refine ⟨fun i => μ (markAt (sigma a b m) i), fun i j hij => hm _ _ (markAt_mono _ i j hσ hij),
    fun i => hb _, fun p hp l hl => ?_, fun q hq k hk l hl => ?_⟩
  · obtain ⟨r, hr, hslot, hle⟩ := hA p hp
    have := hAs r hr l (by simpa [PointClaims.mapEnv, hslot] using hl)
    exact Nat.le_trans (hm _ _ hle) this
  · obtain ⟨r, hr, ⟨hslot, hle⟩, hks⟩ := hB q hq
    have hk' : k ∈ r.2.2 := by simpa using hks k hk
    have := hBs r hr k hk' l (by simpa [PointClaims.mapEnv, hslot] using hl)
    exact Nat.lt_of_lt_of_le this (hm _ _ hle)

/-! ## Allocation -/

/-- A mark past every mark the stamps name. -/
def Stamps.next (s : Stamps) : Nat :=
  ((s.after.map (·.2)) ++ (s.before.map (·.2.1))).foldl max 0 + 1

private theorem foldl_max_ge : ∀ (xs : List Nat) (a : Nat), a ≤ xs.foldl max a
  | [], _ => Nat.le_refl _
  | x :: xs, a => Nat.le_trans (Nat.le_max_left a x) (foldl_max_ge xs (max a x))

private theorem foldl_max_mem : ∀ (xs : List Nat) (a x : Nat), x ∈ xs → x ≤ xs.foldl max a
  | [], _, _, h => by simp at h
  | y :: ys, a, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right a x) (foldl_max_ge ys _)
    · exact foldl_max_mem ys _ x h

theorem after_lt_next {s : Stamps} {p} (hp : p ∈ s.after) : p.2 < s.next := by
  have := foldl_max_mem ((s.after.map (·.2)) ++ (s.before.map (·.2.1))) 0 p.2
    (List.mem_append_left _ (List.mem_map_of_mem hp))
  simp only [Stamps.next]; omega

theorem before_lt_next {s : Stamps} {q} (hq : q ∈ s.before) : q.2.1 < s.next := by
  have := foldl_max_mem ((s.after.map (·.2)) ++ (s.before.map (·.2.1))) 0 q.2.1
    (List.mem_append_right _ (List.mem_map_of_mem hq))
  simp only [Stamps.next]; omega

/-- The fields of `others` grouped by slot, each slot once. -/
def group (others : List (Nat × PropKey)) : List (Nat × List PropKey) :=
  (others.map Prod.fst).eraseDups.map fun i => (i, (others.filter (·.1 == i)).map Prod.snd)

/-- The listed fields of a slot no `before` stamp bounds yet. -/
def Stamps.unbounded (s : Stamps) (i : Nat) (ks : List PropKey) : List PropKey :=
  ks.filter fun k => !(s.before.any fun q => q.1 == i && q.2.2.contains k)

/-- An allocation's stamps: the new result slot `after` a new mark, every
listed field of the other slots no earlier `before` bounds `before` it, and
the old stamps shifted. An earlier `before` is at a smaller mark, so it is
the stronger. -/
def Stamps.alloc (s : Stamps) (others : List (Nat × PropKey)) : Stamps :=
  let M := s.next
  ⟨(0, M) :: s.shift.after, s.shift.before ++ (group others).filterMap fun (i, ks) =>
    if (s.unbounded i ks).isEmpty then none else some (i + 1, M, s.unbounded i ks)⟩

theorem mem_group {others : List (Nat × PropKey)} {i ks k} (hm : (i, ks) ∈ group others)
    (hk : k ∈ ks) : (i, k) ∈ others := by
  obtain ⟨j, -, hj⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at hj
  obtain ⟨rfl, rfl⟩ := hj
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  have hp := List.mem_filter.mp hp
  have : p.1 = j := by simpa using hp.2
  rw [← this]
  exact hp.1

/-- **Allocation stamps.** A result whose own locations are at least the
heap's length, beside slots whose listed fields lie below it, extends the
stamps at a new mark. -/
theorem alloc_holds {s : Stamps} {others : List (Nat × PropKey)} {ρ h h' v}
    (hs : s.Holds ρ h) (hv : ∀ l ∈ ownLocs v, h.length ≤ l)
    (ho : ∀ p ∈ others, ∀ l, fieldLoc (ρ p.1) p.2 = some l → l < h.length)
    (hl : h.length ≤ h'.length) : (s.alloc others).Holds (push v ρ) h' := by
  obtain ⟨μ, hm, hb, hA, hB⟩ := hs
  refine ⟨fun i => if i < s.next then μ i else h.length, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i < s.next <;> by_cases hj : j < s.next <;> simp only [hi, hj, ite_true, ite_false]
    · exact hm i j hij
    · exact hb i
    · omega
    · exact Nat.le_refl _
  · intro i
    by_cases hi : i < s.next <;> simp only [hi, ite_true, ite_false]
    · exact Nat.le_trans (hb i) hl
    · exact hl
  · intro p hp l hl'
    simp only [Stamps.alloc, List.mem_cons] at hp
    rcases hp with rfl | hp
    · show (if s.next < s.next then _ else _) ≤ l
      rw [if_neg (Nat.lt_irrefl _)]
      exact hv l (by simpa [push] using hl')
    · obtain ⟨a, ha, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      simp only [List.mem_singleton] at hj
      subst hj
      show (if a.2 < s.next then _ else _) ≤ l
      rw [if_pos (after_lt_next ha)]
      exact hA a ha l (by simpa [push] using hl')
  · intro q hq k hk l hl'
    simp only [Stamps.alloc, List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨b, hb', hq⟩ := List.mem_flatMap.mp hq
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_singleton] at hj
      subst hj
      show l < (if b.2.1 < s.next then _ else _)
      rw [if_pos (before_lt_next hb')]
      exact hB b hb' k hk l (by simpa [push] using hl')
    · obtain ⟨⟨i, ks⟩, hg, hq⟩ := List.mem_filterMap.mp hq
      split at hq
      · cases hq
      · cases hq
        have hk' : k ∈ ks := (List.mem_filter.mp hk).1
        show l < (if s.next < s.next then _ else _)
        rw [if_neg (Nat.lt_irrefl _)]
        exact ho (i, k) (mem_group hg hk') l (by simpa [push] using hl')

/-! ## The producer's meet -/

/-- What every one of several states stamps: the first's stamps that every
other states at the same slot and mark (for `before`, with the fields all
of them bound). Every edge is still checked. -/
def meet : List Stamps → Stamps
  | [] => {}
  | s :: ss =>
    ⟨s.after.filter fun p => ss.all (·.after.contains p),
     s.before.filterMap fun q =>
       let ks := q.2.2.filter fun k => ss.all fun o =>
         o.before.any fun r => r.1 == q.1 && r.2.1 == q.2.1 && r.2.2.contains k
       if ks.isEmpty then none else some (q.1, q.2.1, ks)⟩

end Verification.HeapStamps
