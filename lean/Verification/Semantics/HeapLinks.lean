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
slots holding the same value and ignores it. A read link through an `optional`
key also covers the object lacking the key, where the read gave `undefined`:
which one it was is what an observation of the value tells. Separation of
locations is the knowledge's separation (`HeapSeparation`). -/
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

/-- The alias classes of the links: an alias link merges the classes of its
two slots, so each class's slots hold one value. -/
def classes (ls : Links) : List (List Nat) :=
  ls.foldl (fun cs g => if g.alias then
    let touches := fun (k : List Nat) => k.contains g.cell || k.contains g.value
    (g.cell :: g.value :: (cs.filter touches).flatten) :: cs.filter (!touches ·)
    else cs) []

/-- A slot's representative: the first slot of its class. -/
def rep (cs : List (List Nat)) (i : Nat) : Nat :=
  match cs.find? (·.contains i) with
  | some (r :: _) => r
  | _ => i

abbrev OneValue (ρ : Env) (cs : List (List Nat)) : Prop :=
  ∀ k ∈ cs, ∀ x ∈ k, ∀ y ∈ k, ρ x = ρ y

theorem classes_step {ρ cs a b} (hcs : OneValue ρ cs) (hab : ρ a = ρ b) :
    let touches := fun (k : List Nat) => k.contains a || k.contains b
    OneValue ρ ((a :: b :: (cs.filter touches).flatten) :: cs.filter (!touches ·)) := by
  intro touches
  have toA : ∀ x ∈ a :: b :: (cs.filter touches).flatten, ρ x = ρ a := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hab.symm
    obtain ⟨k, hk, hxk⟩ := List.mem_flatten.mp hx
    have hk := List.mem_filter.mp hk
    rcases Bool.or_eq_true _ _ ▸ hk.2 with ha | hb
    · exact hcs k hk.1 x hxk a (List.contains_iff_mem.mp ha)
    · exact (hcs k hk.1 x hxk b (List.contains_iff_mem.mp hb)).trans hab.symm
  intro k hk x hx y hy
  rcases List.mem_cons.mp hk with rfl | hk
  · exact (toA x hx).trans (toA y hy).symm
  · exact hcs k (List.mem_filter.mp hk).1 x hx y hy

theorem classes_one {ls ρ h} (hh : Holds ls ρ h) : OneValue ρ (classes ls) := by
  suffices ∀ cs, OneValue ρ cs → OneValue ρ (ls.foldl (fun cs g => if g.alias then
      let touches := fun (k : List Nat) => k.contains g.cell || k.contains g.value
      (g.cell :: g.value :: (cs.filter touches).flatten) :: cs.filter (!touches ·)
      else cs) cs) from this [] (by simp [OneValue])
  induction ls with
  | nil => intro cs hcs; exact hcs
  | cons g ls ih =>
    intro cs hcs
    have hrest : Holds ls ρ h := fun g' hg' => hh g' (List.mem_cons_of_mem _ hg')
    refine ih hrest _ ?_
    by_cases ha : g.alias
    · have hab : ρ g.cell = ρ g.value := by simpa [ha] using hh g (List.mem_cons_self ..)
      simpa [ha] using classes_step hcs hab
    · simpa [ha] using hcs

theorem rep_eq {ρ cs} (hcs : OneValue ρ cs) (i : Nat) : ρ (rep cs i) = ρ i := by
  unfold rep
  split
  · rename_i r t hf
    have hk := List.mem_of_find?_eq_some hf
    have hi := List.find?_some hf
    exact hcs _ hk r (List.mem_cons_self ..) i (List.contains_iff_mem.mp hi)
  · rfl

/-- Each target link must hold of the source links under the mapping, up to
the source's alias classes: a target alias relates two slots of one class,
and a target read is a source read between the same classes. The source reads
are hashed once. -/
def check (a b : Links) (m : PointClaims.Mapping) : Bool :=
  let cs := classes a
  let reads : Std.HashSet Link := Std.HashSet.ofList (a.filterMap fun g =>
    if g.alias then none else some ⟨rep cs g.cell, rep cs g.value, false, g.field, g.optional⟩)
  b.all fun g =>
    let c := rep cs (PointClaims.slot m g.cell)
    let v := rep cs (PointClaims.slot m g.value)
    if g.alias then c == v else reads.contains ⟨c, v, false, g.field, g.optional⟩

theorem check_sound {a b m ρ h} (hc : check a b m = true) (hh : Holds a ρ h) :
    Holds b (PointClaims.mapEnv m ρ) h := by
  have hcs := classes_one hh
  intro g hg
  have hcg := List.all_eq_true.mp hc g hg
  by_cases hga : g.alias
  · simp only [hga, ite_true, beq_iff_eq] at hcg ⊢
    simp only [PointClaims.mapEnv]
    rw [← rep_eq hcs (PointClaims.slot m g.cell), hcg, rep_eq hcs]
  · simp only [hga, Bool.false_eq_true, ite_false, Std.HashSet.contains_ofList,
      List.contains_iff_mem, List.mem_filterMap] at hcg ⊢
    obtain ⟨s, hs, hse⟩ := hcg
    by_cases hsa : s.alias
    · simp [hsa] at hse
    simp only [hsa, Bool.false_eq_true, ite_false, Option.some.injEq, Link.mk.injEq] at hse
    obtain ⟨ec, ev, -, ef, eo⟩ := hse
    have hsh := hh s hs
    simp only [hsa, Bool.false_eq_true, ite_false] at hsh
    have c' : PointClaims.mapEnv m ρ g.cell = ρ s.cell := by
      simp only [PointClaims.mapEnv]
      rw [← rep_eq hcs (PointClaims.slot m g.cell), ← ec, rep_eq hcs]
    have v' : PointClaims.mapEnv m ρ g.value = ρ s.value := by
      simp only [PointClaims.mapEnv]
      rw [← rep_eq hcs (PointClaims.slot m g.value), ← ev, rep_eq hcs]
    rw [c', v', ← ef, ← eo]
    exact hsh

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
def stable (ls : Links) := ls.filter (fun g => g.alias)

theorem stable_holds {ls ρ h h'} (hh : Holds ls ρ h) : Holds (stable ls) ρ h' := by
  intro g hg
  have hg := List.mem_filter.mp hg
  have hh := hh g hg.1
  have ha : g.alias = true := hg.2
  simp only [ha, ite_true] at hh ⊢
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
