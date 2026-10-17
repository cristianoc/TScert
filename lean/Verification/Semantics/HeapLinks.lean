import Verification.Semantics.HeapFacts
import Std.Data.HashSet.Lemmas

/-! A read-to-cell relation is a current-heap fact, not a timeless alias of an
immutable value. It survives pure slot transfers and allocation, but is discarded
on writes and calls. This is the witness needed to refine a cell from a guard. -/
namespace Verification.HeapLinks
open ProgramTyping

instance : Hashable PropKey where
  hash | .str s => mixHash 0 (hash s) | .sym n => mixHash 1 (hash n)

/-- A read link names the field it was read through; an alias link relates two
slots holding the same value and ignores it. Which fields sit at different
locations is what provenance stamps say (`HeapStamps`). A read link through an `optional` key also covers the object lacking the key,
where the read gave `undefined`: which one it was is what an observation of the
value tells. -/
structure Link where
  cell : Nat
  value : Nat
  alias : Bool := false
  field : PropKey := valueField
  optional : Bool := false
  deriving DecidableEq, Hashable, Repr

export HeapFacts (ReadGave)

abbrev Links := List Link

def Holds (ls : Links) (ρ : Env) (h : Heap) : Prop :=
  ∀ g ∈ ls,
    if g.alias then ρ g.cell = ρ g.value
    else if g.optional then ∃ flds c oid, ρ g.cell = .objAt flds c oid ∧ ReadGave flds g.field h (ρ g.value)
    else ∃ flds c oid l, ρ g.cell = .objAt flds c oid ∧ flds.lookup g.field = some l ∧
      h[l]? = some (ρ g.value)

/-- Pull back through a finite selection of aliases for each old slot. -/
def pull (ls : Links) (pre : Nat → List Nat) : Links :=
  ls.flatMap fun g => (pre g.cell).flatMap fun c => (pre g.value).map fun v =>
    ⟨c,v,g.alias,g.field,g.optional⟩

theorem pull_holds {ls pre ρ τ h} (hh : Holds ls ρ h)
    (he : ∀ i j, j ∈ pre i → τ j = ρ i) : Holds (pull ls pre) τ h := by
  intro g hg
  obtain ⟨a,ha,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨c,hc,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  simpa [he _ _ hc,he _ _ hv] using hh a ha

/-- Each target link must be a source link under the mapping. The source
links are hashed once, so the check is linear in the two lists. -/
def check (a b : Links) (m : PointClaims.Mapping) : Bool :=
  let same : Std.HashSet Link := Std.HashSet.ofList a
  b.all fun g => same.contains ⟨PointClaims.slot m g.cell, PointClaims.slot m g.value, g.alias, g.field, g.optional⟩

theorem check_sound {a b m ρ h} (hc : check a b m = true) (hh : Holds a ρ h) :
    Holds b (PointClaims.mapEnv m ρ) h := by
  intro g hg
  have hcg := List.all_eq_true.mp hc g hg
  simp only [Std.HashSet.contains_ofList, List.contains_iff_mem] at hcg
  simpa [PointClaims.mapEnv] using hh _ hcg

/-- The links without repetitions, each at its first occurrence. -/
def dedup (ls : Links) : Links :=
  (ls.foldl (fun (acc : Std.HashSet Link × Links) g =>
    if acc.1.contains g then acc else (acc.1.insert g, g :: acc.2)) (∅, [])).2.reverse

theorem alloc_frames {ls ρ h} (vs : List Val) (hh : Holds ls ρ h) : Holds ls ρ (h ++ vs) := by
  intro g hg
  have hh := hh g hg
  cases ha : g.alias <;> cases ho : g.optional <;>
    simp only [ha,ho,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
  · obtain ⟨flds,c,oid,l,hl,hfd,hv⟩ := hh
    exact ⟨flds,c,oid,l,hl,hfd,HeapObservations.alloc_frames vs hv⟩
  · obtain ⟨flds,c,oid,hl,hr⟩ := hh
    exact ⟨flds,c,oid,hl,hr.alloc_frames vs⟩
  all_goals exact hh

theorem alloc_frame {ls ρ h v} (hh : Holds ls ρ h) : Holds ls ρ (h ++ [v]) :=
  alloc_frames [v] hh

/-- Value equalities survive arbitrary heap changes; read links do not. -/
def stable (ls : Links) := ls.filter (·.alias)

theorem stable_holds {ls ρ h h'} (hh : Holds ls ρ h) : Holds (stable ls) ρ h' := by
  intro g hg
  have hg := List.mem_filter.mp hg
  have hh := hh g hg.1
  simp only [hg.2, ite_true] at hh ⊢
  exact hh

/-- Only witnessed equalities extend a write to another slot. -/
def aliases (ls : Links) (i : Nat) : List Nat := i ::
  ls.filterMap (fun g => if g.alias then
    if g.cell == i then some g.value else if g.value == i then some g.cell else none
    else none)

theorem aliases_eq {ls i j ρ h} (hh : Holds ls ρ h) (hj : j ∈ aliases ls i) : ρ j = ρ i := by
  rcases List.mem_cons.mp hj with rfl | hj
  · rfl
  · obtain ⟨g,hg,hj⟩ := List.mem_filterMap.mp hj
    split at hj
    · rename_i ha
      have he : ρ g.cell = ρ g.value := by simpa [ha] using hh g hg
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
