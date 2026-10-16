import Verification.Semantics.HeapFacts

/-! A read-to-cell relation is a current-heap fact, not a timeless alias of an
immutable value. It survives pure slot transfers and allocation, but is discarded
on writes and calls. This is the witness needed to refine a cell from a guard. -/
namespace Verification.HeapLinks
open ProgramTyping

/-- A read link names the field it was read through; an alias link relates two
slots holding the same value and ignores it. A distinct link relates a field of
the object in `cell` to a field `other` of the object in `value`: they are
different locations, whatever either holds. Locations never move, so a distinct
link is timeless; it is what lets a write to one cell keep a fact about another.
A read link through an `optional` key also covers the object lacking the key,
where the read gave `undefined`: which one it was is what an observation of the
value tells. -/
structure Link where
  cell : Nat
  value : Nat
  alias : Bool := false
  field : PropKey := valueField
  distinct : Bool := false
  other : PropKey := valueField
  optional : Bool := false
  deriving DecidableEq, Repr

export HeapFacts (ReadGave)

abbrev Links := List Link

def Holds (ls : Links) (ρ : Env) (h : Heap) : Prop :=
  ∀ g ∈ ls,
    if g.distinct then
      ∀ flds c oid l flds' c' oid' l', ρ g.cell = .objAt flds c oid → flds.lookup g.field = some l →
        ρ g.value = .objAt flds' c' oid' → flds'.lookup g.other = some l' → l ≠ l'
    else if g.alias then ρ g.cell = ρ g.value
    else if g.optional then ∃ flds c oid, ρ g.cell = .objAt flds c oid ∧ ReadGave flds g.field h (ρ g.value)
    else ∃ flds c oid l, ρ g.cell = .objAt flds c oid ∧ flds.lookup g.field = some l ∧
      h[l]? = some (ρ g.value)

/-- Pull back through a finite selection of aliases for each old slot. -/
def pull (ls : Links) (pre : Nat → List Nat) : Links :=
  ls.flatMap fun g => (pre g.cell).flatMap fun c => (pre g.value).map fun v =>
    ⟨c,v,g.alias,g.field,g.distinct,g.other,g.optional⟩

theorem pull_holds {ls pre ρ τ h} (hh : Holds ls ρ h)
    (he : ∀ i j, j ∈ pre i → τ j = ρ i) : Holds (pull ls pre) τ h := by
  intro g hg
  obtain ⟨a,ha,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨c,hc,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  simpa [he _ _ hc,he _ _ hv] using hh a ha

/-- A distinct link is symmetric, so either orientation of the source justifies it. -/
def check (a b : Links) (m : PointClaims.Mapping) : Bool :=
  b.all fun g => a.any fun f =>
    (f.cell == PointClaims.slot m g.cell &&
      (f.value == PointClaims.slot m g.value && (f.field == g.field && (f.alias == g.alias &&
        (f.distinct == g.distinct && (f.other == g.other && f.optional == g.optional)))))) ||
    (g.distinct && f.distinct && (f.cell == PointClaims.slot m g.value &&
      (f.value == PointClaims.slot m g.cell && (f.field == g.other && f.other == g.field))))

theorem check_sound {a b m ρ h} (hc : check a b m = true) (hh : Holds a ρ h) :
    Holds b (PointClaims.mapEnv m ρ) h := by
  intro g hg
  obtain ⟨f,hf,hfg⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc g hg)
  simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at hfg
  rcases hfg with hfg | ⟨⟨hgd,hfd⟩,h1,h2,h3,h4⟩
  · simpa [PointClaims.mapEnv,← hfg.1,← hfg.2.1,← hfg.2.2.1,← hfg.2.2.2.1,← hfg.2.2.2.2.1,
      ← hfg.2.2.2.2.2.1,← hfg.2.2.2.2.2.2] using hh f hf
  · have hf := hh f hf
    simp only [hfd,ite_true] at hf
    simp only [hgd,ite_true,PointClaims.mapEnv,← h1,← h2,← h3,← h4]
    intro flds c oid l flds' c' oid' l' e1 e2 e3 e4 heq
    exact hf flds' c' oid' l' flds c oid l e3 e4 e1 e2 heq.symm

theorem alloc_frames {ls ρ h} (vs : List Val) (hh : Holds ls ρ h) : Holds ls ρ (h ++ vs) := by
  intro g hg
  have hh := hh g hg
  cases hd : g.distinct <;> cases ha : g.alias <;> cases ho : g.optional <;>
    simp only [hd,ha,ho,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
  · obtain ⟨flds,c,oid,l,hl,hfd,hv⟩ := hh
    exact ⟨flds,c,oid,l,hl,hfd,HeapObservations.alloc_frames vs hv⟩
  · obtain ⟨flds,c,oid,hl,hr⟩ := hh
    exact ⟨flds,c,oid,hl,hr.alloc_frames vs⟩
  all_goals exact hh

theorem alloc_frame {ls ρ h v} (hh : Holds ls ρ h) : Holds ls ρ (h ++ [v]) :=
  alloc_frames [v] hh

/-- Value equalities and distinct locations survive arbitrary heap changes;
read links do not. -/
def stable (ls : Links) := ls.filter (fun g => g.alias || g.distinct)

theorem stable_holds {ls ρ h h'} (hh : Holds ls ρ h) : Holds (stable ls) ρ h' := by
  intro g hg
  have hg := List.mem_filter.mp hg
  have hh := hh g hg.1
  by_cases hd : g.distinct = true
  · simp only [hd, ite_true] at hh ⊢
    exact hh
  · have ha : g.alias = true := by
      have := hg.2
      simp only [Bool.or_eq_true] at this
      exact this.resolve_right hd
    simp only [hd, ha, Bool.false_eq_true, ite_false, ite_true] at hh ⊢
    exact hh

/-- Only witnessed equalities extend a write to another slot. -/
def aliases (ls : Links) (i : Nat) : List Nat := i ::
  ls.filterMap (fun g => if g.alias && !g.distinct then
    if g.cell == i then some g.value else if g.value == i then some g.cell else none
    else none)

/-- The fields of other slots known to sit at locations other than field `fld`
of the object in slot `i`, in either orientation. -/
def distinctFrom (ls : Links) (i : Nat) (fld : PropKey) : List (Nat × PropKey) :=
  ls.filterMap fun g =>
    if g.distinct then
      if g.cell == i && g.field == fld then some (g.value, g.other)
      else if g.value == i && g.other == fld then some (g.cell, g.field)
      else none
    else none

theorem distinct_sound {ls ρ h i fld s f'} (hh : Holds ls ρ h) (hm : (s, f') ∈ distinctFrom ls i fld)
    {flds c oid l flds' c' oid' l'} (hi : ρ i = .objAt flds c oid) (hl : flds.lookup fld = some l)
    (hs : ρ s = .objAt flds' c' oid') (hl' : flds'.lookup f' = some l') : l ≠ l' := by
  obtain ⟨g,hg,hsel⟩ := List.mem_filterMap.mp hm
  have hh := hh g hg
  split at hsel
  · rename_i hd
    simp only [hd,ite_true] at hh
    split at hsel
    · rename_i hc
      simp only [Bool.and_eq_true,beq_iff_eq] at hc
      cases hsel
      exact hh flds c oid l flds' c' oid' l' (by rw [hc.1]; exact hi) (by rw [hc.2]; exact hl) hs hl'
    · split at hsel
      · rename_i hv
        simp only [Bool.and_eq_true,beq_iff_eq] at hv
        cases hsel
        exact fun heq => hh flds' c' oid' l' flds c oid l hs hl' (by rw [hv.1]; exact hi) (by rw [hv.2]; exact hl) heq.symm
      · contradiction
  · contradiction

theorem aliases_eq {ls i j ρ h} (hh : Holds ls ρ h) (hj : j ∈ aliases ls i) : ρ j = ρ i := by
  rcases List.mem_cons.mp hj with rfl | hj
  · rfl
  · obtain ⟨g,hg,hj⟩ := List.mem_filterMap.mp hj
    split at hj
    · rename_i ha
      simp only [Bool.and_eq_true,Bool.not_eq_eq_eq_not,Bool.not_true] at ha
      have he : ρ g.cell = ρ g.value := by simpa [ha.1,ha.2] using hh g hg
      split at hj
      · rename_i hc
        simp only [beq_iff_eq] at hc
        cases hj
        simpa [hc] using he.symm
      · split at hj
        · rename_i hv
          simp only [beq_iff_eq] at hv
          cases hj
          simpa [hv] using he
        · contradiction
    · contradiction

end Verification.HeapLinks
