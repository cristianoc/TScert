import Verification.Semantics.HeapFacts
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas

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

/-- Hash-indexed representative table for `cs`: maps every slot of each class
to the class's head slot in `O(1)` lookup time. -/
def repMap (cs : List (List Nat)) : Std.HashMap Nat Nat :=
  cs.foldl (fun m k => match k with
    | r :: _ => k.foldl (fun m x => m.insert x r) m
    | [] => m) {}

/-- `O(1)` slot representative lookup in a precomputed `repMap`. Callers bind
`let rm := repMap cs` once (a concrete `HashMap`, not a curried function) and
pass `repOf rm` so Lean's arity flattening does not rebuild the table. -/
def repOf (m : Std.HashMap Nat Nat) (i : Nat) : Nat :=
  m.getD i i

theorem repMap_eq {ρ cs} (hcs : OneValue ρ cs) :
    ∀ {i r}, (repMap cs)[i]? = some r → ρ r = ρ i := by
  have hstep : ∀ (xs : List (List Nat)) (m : Std.HashMap Nat Nat),
      (∀ k ∈ xs, ∀ x ∈ k, ∀ y ∈ k, ρ x = ρ y) →
      (∀ {i r}, m[i]? = some r → ρ r = ρ i) →
      ∀ {i r}, (xs.foldl (fun m k => match k with
        | r :: _ => k.foldl (fun m x => m.insert x r) m
        | [] => m) m)[i]? = some r → ρ r = ρ i := by
    intro xs
    induction xs with
    | nil => intro m _ hm i r h; exact hm h
    | cons k xs ih =>
      intro m hxs hm
      apply ih _ (fun k' hk' => hxs k' (List.mem_cons_of_mem _ hk'))
      cases k with
      | nil => exact hm
      | cons r0 t =>
        have hk := hxs (r0 :: t) (List.mem_cons_self ..)
        have hinner : ∀ (ys : List Nat) (m' : Std.HashMap Nat Nat),
            (∀ y ∈ ys, ρ r0 = ρ y) →
            (∀ {i r}, m'[i]? = some r → ρ r = ρ i) →
            ∀ {i r}, (ys.foldl (fun m x => m.insert x r0) m')[i]? = some r → ρ r = ρ i := by
          intro ys
          induction ys with
          | nil => intro m' _ hm' i r h; exact hm' h
          | cons y ys ihy =>
            intro m' hys hm'
            apply ihy _ (fun z hz => hys z (List.mem_cons_of_mem _ hz))
            intro i r h
            rw [Std.HashMap.getElem?_insert] at h
            split at h
            · rename_i hyi
              simp only [Option.some.injEq] at h
              subst h
              have hyi : y = i := by simpa using hyi
              subst hyi
              exact hys y (List.mem_cons_self ..)
            · exact hm' h
        exact fun {i r} => hinner (r0 :: t) m (fun y hy => hk r0 (List.mem_cons_self ..) y hy) hm
  exact fun {i r} => hstep cs {} hcs (by intro i r h; simp at h)

theorem repOf_eq {ρ cs} (hcs : OneValue ρ cs) (i : Nat) : ρ (repOf (repMap cs) i) = ρ i := by
  unfold repOf
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases h : (repMap cs)[i]? with
  | none => rfl
  | some r => exact repMap_eq hcs h

/-- Each target link must hold of the source links under the mapping, up to
the source's alias classes: a target alias relates two slots of one class,
and a target read is a source read between the same classes, one that found
the field also justifying one that may not. The source reads are hashed
once. -/
def checkWith (r : Nat → Nat) (a b : Links) (m : PointClaims.Mapping) : Bool :=
  let reads : Std.HashSet Link := Std.HashSet.ofList (a.filterMap fun g =>
    if g.alias then none else some ⟨r g.cell, r g.value, false, g.field, g.optional⟩)
  b.all fun g =>
    let c := r (PointClaims.slot m g.cell)
    let v := r (PointClaims.slot m g.value)
    if g.alias then c == v
    else reads.contains ⟨c, v, false, g.field, g.optional⟩ || (g.optional && reads.contains ⟨c, v, false, g.field, false⟩)

def check (a b : Links) (m : PointClaims.Mapping) : Bool :=
  let rm := repMap (classes a)
  checkWith (repOf rm) a b m

/-- The check by any representatives of slots holding one value. -/
theorem checkWith_sound {r a b m ρ h} (hr : ∀ x, ρ (r x) = ρ x) (hc : checkWith r a b m = true) (hh : Holds a ρ h) :
    Holds b (PointClaims.mapEnv m ρ) h := by
  intro g hg
  have hcg := List.all_eq_true.mp hc g hg
  by_cases hga : g.alias
  · simp only [hga, ite_true, beq_iff_eq] at hcg ⊢
    simp only [PointClaims.mapEnv]
    rw [← hr (PointClaims.slot m g.cell), hcg, hr]
  · simp only [hga, Bool.false_eq_true, ite_false] at hcg ⊢
    -- The source read justifying the target, as found in the hashed reads.
    have found : ∀ {o : Bool}, (Std.HashSet.ofList (a.filterMap fun g =>
        if g.alias then none else some (⟨r g.cell, r g.value, false, g.field,
          g.optional⟩ : Link))).contains ⟨r (PointClaims.slot m g.cell),
          r (PointClaims.slot m g.value), false, g.field, o⟩ = true →
        ∃ s ∈ a, s.alias = false ∧ s.optional = o ∧ s.field = g.field ∧
          PointClaims.mapEnv m ρ g.cell = ρ s.cell ∧ PointClaims.mapEnv m ρ g.value = ρ s.value := by
      intro o hcon
      simp only [Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_filterMap] at hcon
      obtain ⟨s, hs, hse⟩ := hcon
      by_cases hsa : s.alias
      · simp [hsa] at hse
      simp only [hsa, Bool.false_eq_true, ite_false, Option.some.injEq, Link.mk.injEq] at hse
      obtain ⟨ec, ev, -, ef, eo⟩ := hse
      refine ⟨s, hs, by simpa using hsa, eo, ef, ?_, ?_⟩
      · simp only [PointClaims.mapEnv]
        rw [← hr (PointClaims.slot m g.cell), ← ec, hr]
      · simp only [PointClaims.mapEnv]
        rw [← hr (PointClaims.slot m g.value), ← ev, hr]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hcg
    rcases hcg with hcon | ⟨ho, hcon⟩
    · obtain ⟨s, hs, hsa, eo, ef, c', v'⟩ := found hcon
      have hsh := hh s hs
      simp only [hsa, Bool.false_eq_true, ite_false] at hsh
      rw [c', v', ← ef, ← eo]
      exact hsh
    · obtain ⟨s, hs, hsa, eo, ef, c', v'⟩ := found hcon
      have hsh := hh s hs
      simp only [hsa, eo, Bool.false_eq_true, ite_false] at hsh
      obtain ⟨flds, c, oid, l, he, hl, hv⟩ := hsh
      simp only [ho, ite_true]
      rw [c', v', ← ef]
      exact ⟨flds, c, oid, he, HeapFacts.ReadGave.present hl hv⟩

theorem check_sound {a b m ρ h} (hc : check a b m = true) (hh : Holds a ρ h) :
    Holds b (PointClaims.mapEnv m ρ) h :=
  checkWith_sound (repOf_eq (classes_one hh)) hc hh

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

/-- The alias links: the links of the empty support (`FactKind.link`,
`Footprints.stableLinks_holds`). -/
def stable (ls : Links) := ls.filter (fun g => g.alias)

/-- The slots one alias link relates to `i`. -/
def neighbors (ls : Links) (i : Nat) : List Nat :=
  ls.filterMap (fun g => if g.alias then
    if g.cell == i then some g.value else if g.value == i then some g.cell else none
    else none)

/-- Only witnessed equalities extend a write to another slot: the slots one
or two alias links relate to `i`, which reach a class's every slot where its
links join each slot to one representative. -/
def aliases (ls : Links) (i : Nat) : List Nat :=
  let near := neighbors ls i
  i :: near ++ near.flatMap (neighbors ls)

theorem neighbors_eq {ls i j ρ h} (hh : Holds ls ρ h) (hj : j ∈ neighbors ls i) : ρ j = ρ i := by
  obtain ⟨g,hg,hj⟩ := List.mem_filterMap.mp hj
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

theorem aliases_eq {ls i j ρ h} (hh : Holds ls ρ h) (hj : j ∈ aliases ls i) : ρ j = ρ i := by
  simp only [aliases, List.cons_append, List.mem_cons, List.mem_append, List.mem_flatMap] at hj
  rcases hj with rfl | hj | ⟨k, hk, hj⟩
  · rfl
  · exact neighbors_eq hh hj
  · exact (neighbors_eq hh hj).trans (neighbors_eq hh hk)

/-- Hash-indexed alias adjacency map for `ls`: built in one `O(|ls|)` pass so
`m.getD i [] = neighbors ls i` in `O(1)`. -/
def aliasesMap (ls : Links) : Std.HashMap Nat (List Nat) :=
  ls.reverse.foldl (fun m g =>
    if g.alias then
      let m := m.insert g.cell (g.value :: m.getD g.cell [])
      if g.cell == g.value then m else m.insert g.value (g.cell :: m.getD g.value [])
    else m) {}

/-- `O(1)` alias lookup backed by `aliasesMap`, matching `aliases ls` exactly. -/
def aliasesOf (m : Std.HashMap Nat (List Nat)) (i : Nat) : List Nat :=
  let near := m.getD i []
  i :: near ++ near.flatMap (m.getD · [])

theorem aliasesMap_getD (ls : Links) (i : Nat) : (aliasesMap ls).getD i [] = neighbors ls i := by
  unfold aliasesMap neighbors
  have hgo : ∀ (xs : Links),
      (xs.reverse.foldl (fun (m : Std.HashMap Nat (List Nat)) g =>
        if g.alias then
          let m := m.insert g.cell (g.value :: m.getD g.cell [])
          if g.cell == g.value then m else m.insert g.value (g.cell :: m.getD g.value [])
        else m) {}).getD i [] =
      xs.filterMap (fun g => if g.alias then
        if g.cell == i then some g.value else if g.value == i then some g.cell else none
        else none) := by
    intro xs
    induction xs with
    | nil => simp
    | cons g xs ih =>
      rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, List.filterMap_cons]
      dsimp only
      cases ha : g.alias
      · simp only [Bool.false_eq_true, ↓reduceIte, ih]
      · simp only [↓reduceIte]
        by_cases hcv : g.cell == g.value
        · simp only [hcv, ↓reduceIte]
          rw [Std.HashMap.getD_insert]
          by_cases hci : g.cell == i
          · have hce : g.cell = i := beq_iff_eq.mp hci
            simp only [hce, beq_self_eq_true, ↓reduceIte, ih]
          · have hvi : (g.value == i) = false := by
              have h1 : g.cell = g.value := beq_iff_eq.mp hcv
              rw [← h1]; simpa using hci
            simp only [hci, hvi, Bool.false_eq_true, ↓reduceIte, ih]
        · simp only [hcv, Bool.false_eq_true, ↓reduceIte]
          rw [Std.HashMap.getD_insert]
          by_cases hvi : g.value == i
          · have hve : g.value = i := beq_iff_eq.mp hvi
            have hci : (g.cell == i) = false := by
              cases h2 : (g.cell == i)
              · rfl
              · exfalso; exact hcv (beq_iff_eq.mpr ((beq_iff_eq.mp h2).trans hve.symm))
            simp only [hvi, hci, Bool.false_eq_true, ↓reduceIte]
            rw [Std.HashMap.getD_insert]
            simp only [hve, hci, Bool.false_eq_true, ↓reduceIte, ih]
          · simp only [hvi, Bool.false_eq_true, ↓reduceIte]
            rw [Std.HashMap.getD_insert]
            by_cases hci : g.cell == i
            · have hce : g.cell = i := beq_iff_eq.mp hci
              simp only [hce, beq_self_eq_true, ↓reduceIte, ih]
            · simp only [hci, Bool.false_eq_true, ↓reduceIte, ih]
  exact hgo ls

theorem aliasesOf_eq_aliases (ls : Links) (i : Nat) : aliasesOf (aliasesMap ls) i = aliases ls i := by
  unfold aliasesOf aliases
  simp only [aliasesMap_getD]

theorem aliasesOf_eq {ls i j ρ h} (hh : Holds ls ρ h) (hj : j ∈ aliasesOf (aliasesMap ls) i) : ρ j = ρ i := by
  rw [aliasesOf_eq_aliases] at hj
  exact aliases_eq hh hj

/-- Each read link restated between the slots one or two alias links relate
to its cell and to its value (`aliases`): a read between two classes holds
of every pair of their slots, so a read whose slots are dropped survives in
the slots of their classes that are kept. -/
def aliasReads (ls : Links) : Links :=
  ls ++ (ls.filter (!·.alias)).flatMap fun g =>
    (aliases ls g.cell).flatMap fun c => (aliases ls g.value).filterMap fun v =>
      if c == g.cell && v == g.value then none else some { g with cell := c, value := v }

/-- Before slots are dropped, each dropped slot's alias neighbours linked
to one of them: a class keeps its equalities when the slot joining them
goes. -/
def bridge (ls : Links) (dropped : Nat → Bool) : Links :=
  ls ++ ((ls.flatMap fun g => [g.cell, g.value]).eraseDups.filter dropped).flatMap fun d =>
    match neighbors ls d with
    | n :: rest => rest.map fun m => { cell := n, value := m, alias := true }
    | [] => []

theorem bridge_holds {ls : Links} {dropped : Nat → Bool} {ρ h} (hh : Holds ls ρ h) :
    Holds (bridge ls dropped) ρ h := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hh g hg
  · obtain ⟨d, -, hg⟩ := List.mem_flatMap.mp hg
    split at hg
    · rename_i n rest hn
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg
      have e₁ := neighbors_eq hh (hn ▸ List.mem_cons_self .. : n ∈ neighbors ls d)
      have e₂ := neighbors_eq hh (hn ▸ List.mem_cons_of_mem n hm : m ∈ neighbors ls d)
      simp only [ite_true]
      exact e₁.trans e₂.symm
    · cases hg

end Verification.HeapLinks
