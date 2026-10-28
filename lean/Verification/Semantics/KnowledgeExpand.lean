import Verification.Semantics.KnowledgeNormal

/-! The expansion of heap knowledge (heap-knowledge draft, §6.2): what the
normal form leaves implicit, restated for readers that look a fact up by its
slot. Each value fact holds on every slot of its class, restricted to that
slot's context; each cell fact on every slot of its receiver's class; behind
each read link, the value facts of its value as cell facts; each link and
each atomic separation pair between every two slots of its classes. -/
namespace Verification.KnowledgeExpand
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower HeapFacts HeapKnowledge ValueSets
  KnowledgeNormal SeparationNormal CanonicalLists

/-- The context of each slot of an environment typed by `Γ`: the values its
type admits, where the type is of finitely many primitive predicates. -/
@[inline] def ctxOf {ι : Type} (G : NormalGraph ι) (Γ : List (Ty ι)) : Ctx :=
  HeapKnowledge.setsCtx (HeapKnowledge.typeSets G Γ) 0

theorem ctxOf_ok {ι : Type} {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ n W} (he : EnvOk G Γ ρ n W) :
    CtxOk (ctxOf G Γ) ρ := by
  intro i C hC
  simp only [ctxOf, HeapKnowledge.setsCtx, Nat.not_lt_zero, if_false, Nat.sub_zero] at hC
  exact HeapKnowledge.typeSets_mem he hC

section
variable (ctx : Ctx) (k : Knowledge) (cs : Partitions.Partition)

/-- The slots of `x`'s alias class, in the knowledge's closure `cs`. -/
def members (x : Nat) : List Nat := Partitions.cls cs x

/-- The context of `x`'s class in the closure `cs`: the meet of its slots'
contexts, where any has one (`KnowledgeNormal.classCtx`, in any order). -/
def classCtxIn (x : Nat) : Option ValueSet :=
  match (Partitions.cls cs x).filterMap ctx with
  | [] => none
  | C :: Cs => some (meetAll C Cs)

/-- A value set restricted to a context, where there is one. -/
def restrict (C : Option ValueSet) (V : ValueSet) : ValueSet :=
  match C with
  | none => V
  | some C => V.meet C

/-- Each value fact on every slot of its class, at the class's context; and
the context of every read's value, which a normal form leaves unstated where
it is all that is known. -/
def values : Facts :=
  (k.values.flatMap fun f =>
    let C := classCtxIn ctx cs f.slot
    (members cs f.slot).map fun y => ⟨y, restrict C f.contents, f.field⟩) ++
  (k.links.filter fun g => !g.alias).flatMap fun g => match classCtxIn ctx cs g.value with
    | some C => (members cs g.value).map fun y => ⟨y, C, valueField⟩
    | none => []

def links : HeapLinks.Links :=
  (LinkClasses.slots k.links).filterMap (fun x =>
    let r := LinkClasses.least x (members cs x)
    if r = x then none else some ⟨r, x, true, valueField, false⟩) ++
  k.links.flatMap fun g => if g.alias then [] else
    (members cs g.cell).flatMap fun c => (members cs g.value).map fun v => ⟨c, v, false, g.field, g.optional⟩

/-- The cell facts on every slot of their classes, and behind each read link
of `ls` the value facts `vs` of its value. -/
def cells (vs : Facts) (ls : HeapLinks.Links) : Facts :=
  (k.cells.flatMap fun f => (members cs f.slot).map fun y => { f with slot := y }) ++
  vs.flatMap fun F => linkFacts ⟨[], [], ls, {}⟩ F.slot F.contents

/-- An atomic pair between every two slots of its classes. -/
def spread : SepAtom → List SepAtom
  | .whole i j g => (members cs i).flatMap fun i' => (members cs j).map fun j' => .whole i' j' g
  | .field i f j g => (members cs i).flatMap fun i' => (members cs j).map fun j' => .field i' f j' g

def bounded (d : Nat) : SepAtom → Bool
  | .whole i j _ | .field i _ j _ => decide (i < d) && decide (j < d)

/-- The separation's facts, and each atomic pair on every two slots of its
classes not already among them. -/
def separation : HeapSeparation.Separation :=
  let S := k.separation
  let stated : Std.HashSet HeapSeparation.Fact := Std.HashSet.ofList S.facts
  ⟨S.depth, S.facts ++ ((((SeparationNormal.atoms S).flatMap (spread cs)).filter (bounded S.depth)).map
    (encode S.depth)).filter (!stated.contains ·)⟩

/-- The knowledge with what its normal form leaves implicit restated, its
alias closure computed once. -/
def expand : Knowledge :=
  let cs := LinkClasses.closure k.links
  let vs := values ctx k cs
  let ls := links k cs
  ⟨cells k cs vs ls, vs, ls, separation k cs⟩

end

section sound
variable {ctx : Ctx} {k : Knowledge} {ρ : Env} {h : Heap}

theorem members_eq (hl : HeapLinks.Holds k.links ρ h) {x y : Nat} (hy : y ∈ members (LinkClasses.closure k.links) x) :
    ρ y = ρ x :=
  (LinkClasses.gen_sound hl (LinkClasses.mem_cls_closure.mp hy)).symm

theorem classCtxIn_mem {cs : Partitions.Partition} (hc : CtxOk ctx ρ) {x : Nat}
    (hs : ∀ y ∈ Partitions.cls cs x, ρ y = ρ x) {C : ValueSet} (h : classCtxIn ctx cs x = some C) :
    C.mem (ρ x) = true := by
  have each : ∀ D ∈ (Partitions.cls cs x).filterMap ctx, D.mem (ρ x) = true := by
    intro D hD
    obtain ⟨y, hy, hyD⟩ := List.mem_filterMap.mp hD
    rw [← hs y hy]
    exact hc y D hyD
  unfold classCtxIn at h
  split at h
  · cases h
  · rename_i C' Cs e
    cases h
    rw [e] at each
    exact mem_meetAll.mpr ⟨each C' (List.mem_cons_self ..), fun x hx => each x (List.mem_cons_of_mem _ hx)⟩

theorem restrict_mem {o : Option ValueSet} {v : Tm} (ho : ∀ C, o = some C → C.mem v = true) {V : ValueSet}
    (hv : V.mem v = true) : (restrict o V).mem v = true := by
  unfold restrict
  split
  · exact hv
  · rename_i C
    rw [ValueSet.mem_meet, hv, ho C rfl]; rfl

theorem values_holds (hc : CtxOk ctx ρ) (hk : HeapKnowledge.Holds k ρ h) :
    ValueHolds (values ctx k (LinkClasses.closure k.links)) ρ := by
  have hs : ∀ x, ∀ y ∈ Partitions.cls (LinkClasses.closure k.links) x, ρ y = ρ x :=
    fun _ _ hy => members_eq hk.2.2.1 hy
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · obtain ⟨f, hf, hF⟩ := List.mem_flatMap.mp hF
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hF
    rw [members_eq hk.2.2.1 hy]
    exact restrict_mem (fun _ hC => classCtxIn_mem hc (hs f.slot) hC) (hk.2.1 f hf)
  · obtain ⟨g, -, hF⟩ := List.mem_flatMap.mp hF
    split at hF
    · rename_i C hC
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hF
      show C.mem (ρ y) = true
      rw [members_eq hk.2.2.1 hy]
      exact classCtxIn_mem hc (hs g.value) hC
    · cases hF

theorem links_holds (hk : HeapKnowledge.Holds k ρ h) : HeapLinks.Holds (links k (LinkClasses.closure k.links)) ρ h := by
  have hl := hk.2.2.1
  intro L hL
  rcases List.mem_append.mp hL with hL | hL
  · obtain ⟨x, _, hL⟩ := List.mem_filterMap.mp hL
    simp only at hL
    split at hL
    · cases hL
    · rename_i hne
      cases hL
      simp only [ite_true]
      have hr : LinkClasses.least x (members (LinkClasses.closure k.links) x) ∈
          members (LinkClasses.closure k.links) x :=
        (LinkClasses.least_mem (l := members (LinkClasses.closure k.links) x)).elim
          (fun e => absurd e hne) id
      exact members_eq hl hr
  · obtain ⟨g, hg, hL⟩ := List.mem_flatMap.mp hL
    split at hL
    · cases hL
    · rename_i ha
      obtain ⟨c, hcm, hL⟩ := List.mem_flatMap.mp hL
      obtain ⟨v, hvm, rfl⟩ := List.mem_map.mp hL
      have hgl := hl g hg
      simp only [ha, Bool.false_eq_true, ite_false] at hgl ⊢
      rw [members_eq hl hcm, members_eq hl hvm]
      exact hgl

theorem cells_holds (hk : HeapKnowledge.Holds k ρ h) {vs : Facts} {ls : HeapLinks.Links} (hv : ValueHolds vs ρ)
    (hl : HeapLinks.Holds ls ρ h) : HeapFacts.Holds (cells k (LinkClasses.closure k.links) vs ls) ρ h := by
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · obtain ⟨f, hf, hF⟩ := List.mem_flatMap.mp hF
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hF
    obtain ⟨flds, c, oid, u, he, hr, hm⟩ := hk.1 f hf
    exact ⟨flds, c, oid, u, by rw [members_eq hk.2.2.1 hy]; exact he, hr, hm⟩
  · obtain ⟨V, hV, hF⟩ := List.mem_flatMap.mp hF
    have hk' : HeapKnowledge.Holds ⟨[], [], ls, {}⟩ ρ h :=
      ⟨holds_nil ρ h, by simp [ValueHolds], hl, HeapSeparation.empty_holds ρ⟩
    exact linkFacts_holds hk' (hv V hV) F hF

theorem atoms_of_holds {S : HeapSeparation.Separation} (hS : HeapSeparation.Holds S ρ) :
    ∀ x ∈ SeparationNormal.atoms S, x.Holds ρ := by
  intro x hx
  simp only [SeparationNormal.atoms, List.mem_flatMap] at hx
  obtain ⟨a, ha, p, hp, g, hg, hx⟩ := hx
  have hap := ((hS a ha).2 p hp).2 g hg
  cases hf : a.fields with
  | none => rw [hf] at hx hap; simp at hx; subst hx; exact hap
  | some fs =>
    rw [hf] at hx hap
    obtain ⟨f, hf', rfl⟩ := List.mem_map.mp hx
    exact hap.single (by simp [HeapSeparation.covers, hf'])

theorem spread_holds (hl : HeapLinks.Holds k.links ρ h) {x : SepAtom} (hx : x.Holds ρ) :
    ∀ y ∈ spread (LinkClasses.closure k.links) x, y.Holds ρ := by
  intro y hy
  cases x with
  | whole i j g =>
    obtain ⟨i', hi, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨j', hj, rfl⟩ := List.mem_map.mp hy
    exact (hx : HeapSeparation.Apart ρ i none j g).congr (members_eq hl hi) (members_eq hl hj)
  | field i f j g =>
    obtain ⟨i', hi, hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨j', hj, rfl⟩ := List.mem_map.mp hy
    exact (hx : HeapSeparation.Apart ρ i (some [f]) j g).congr (members_eq hl hi) (members_eq hl hj)

theorem separation_holds (hk : HeapKnowledge.Holds k ρ h) :
    HeapSeparation.Holds (separation k (LinkClasses.closure k.links)) ρ := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hk.2.2.2 a ha
  obtain ⟨ha, -⟩ := List.mem_filter.mp ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hy, hb⟩ := List.mem_filter.mp hy
  obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
  have hyh := spread_holds hk.2.2.1 (atoms_of_holds hk.2.2.2 x hx) y hy
  cases y with
  | whole i j g =>
    simp only [bounded, Bool.and_eq_true, decide_eq_true_eq] at hb
    exact (encode_holds (x := .whole i j g) hb).mpr hyh
  | field i f j g =>
    simp only [bounded, Bool.and_eq_true, decide_eq_true_eq] at hb
    exact (encode_holds (x := .field i f j g) hb).mpr hyh

/-- What readers need of a knowledge whose facts are stored once per class:
its value facts restricted to their classes' contexts, and each read's value
class's context as a value fact; behind each stored read link
the value facts of its value as cell facts; each class's slots linked to its
least slot, and reads and separation pairs restated on every slot of their
classes. Facts are gathered by class
where they are read (`HeapKnowledge.valueBy`, `HeapKnowledge.cellBy`). -/
def expandLinks (ctx : Ctx) (k : Knowledge) : Knowledge :=
  let cs := LinkClasses.closure k.links
  let ls := links k cs
  let vs := (k.values.map fun F => { F with contents := restrict (classCtxIn ctx cs F.slot) F.contents }) ++
    (k.links.filter fun g => !g.alias).filterMap fun g =>
      (classCtxIn ctx cs g.value).map fun C => ⟨g.value, C, valueField⟩
  ⟨k.cells ++ vs.flatMap (fun F => linkFacts ⟨[], [], k.links, {}⟩ F.slot F.contents), vs, ls, k.separation⟩

theorem expandLinks_holds {ctx : Ctx} {k : Knowledge} {ρ : Env} {h : Heap} (hc : CtxOk ctx ρ)
    (hk : HeapKnowledge.Holds k ρ h) : HeapKnowledge.Holds (expandLinks ctx k) ρ h := by
  have hs : ∀ x, ∀ y ∈ Partitions.cls (LinkClasses.closure k.links) x, ρ y = ρ x :=
    fun _ _ hy => members_eq hk.2.2.1 hy
  have hv : ValueHolds ((k.values.map fun F =>
      { F with contents := restrict (classCtxIn ctx (LinkClasses.closure k.links) F.slot) F.contents }) ++
      (k.links.filter fun g => !g.alias).filterMap fun g =>
        (classCtxIn ctx (LinkClasses.closure k.links) g.value).map fun C => ⟨g.value, C, valueField⟩) ρ := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
      exact restrict_mem (fun _ hC => classCtxIn_mem hc (hs G.slot) hC) (hk.2.1 G hG)
    · obtain ⟨g, -, hF⟩ := List.mem_filterMap.mp hF
      obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.mp hF
      exact classCtxIn_mem hc (hs g.value) hC
  have hl := links_holds hk
  refine ⟨fun F hF => ?_, hv, hl, hk.2.2.2⟩
  rcases List.mem_append.mp hF with hF | hF
  · exact hk.1 F hF
  · obtain ⟨V, hV, hF⟩ := List.mem_flatMap.mp hF
    have hk' : HeapKnowledge.Holds ⟨[], [], k.links, {}⟩ ρ h :=
      ⟨holds_nil ρ h, by simp [ValueHolds], hk.2.2.1, HeapSeparation.empty_holds ρ⟩
    exact linkFacts_holds hk' (hv V hV) F hF

/-- The expansion holds wherever the knowledge does, at environments meeting
the contexts. -/
theorem expand_holds (hc : CtxOk ctx ρ) (hk : HeapKnowledge.Holds k ρ h) :
    HeapKnowledge.Holds (expand ctx k) ρ h :=
  ⟨cells_holds hk (values_holds hc hk) (links_holds hk), values_holds hc hk, links_holds hk, separation_holds hk⟩

end sound

/-! ## The check against a stored normal form -/

/-- Each target fact is justified by what the source states of its mapped
slot's class (`HeapKnowledge.cellBy`, `HeapKnowledge.valueBy`), a value read through the target class's
context: a normal form states a class's facts once, met, and a value fact
only at its context. Links are compared by the source's classes, and
separation against the source's pairs on every two slots of their classes. -/
def cellsCheck (a : Knowledge) (cs : Partitions.Partition) (target : Facts) (m : PointClaims.Mapping) : Bool :=
  target.all fun f => match HeapKnowledge.cellBy a (Partitions.cls cs) (PointClaims.slot m f.slot) f.field with
    | some V => V.le f.contents
    | none => false

def valuesCheck (ctx : Ctx) (a : Knowledge) (cs : Partitions.Partition) (b : Knowledge) (m : PointClaims.Mapping) : Bool :=
  let cb := LinkClasses.closure b.links
  b.values.all fun f => match HeapKnowledge.valueBy a (Partitions.cls cs) (PointClaims.slot m f.slot) with
    | some V => (restrict (classCtxIn ctx cb f.slot) V).le f.contents
    | none => false

def checkIn (ctx : Ctx) (a b : Knowledge) (m : PointClaims.Mapping) : Bool :=
  let cs := LinkClasses.closure a.links
  cellsCheck a cs b.cells m && (valuesCheck ctx a cs b m &&
  (HeapLinks.checkWith (LinkClasses.repIn cs) a.links b.links m &&
    HeapSeparation.checkWithTable (SeparationNormal.levelTable (LinkClasses.repIn cs) a.separation.depth)
      a.separation b.separation m))

theorem checkIn_sound {ctx a b m ρ h} (hc : checkIn ctx a b m = true)
    (hctx : CtxOk ctx (PointClaims.mapEnv m ρ)) (ha : HeapKnowledge.Holds a ρ h) :
    HeapKnowledge.Holds b (PointClaims.mapEnv m ρ) h := by
  have hs : ∀ x, ∀ y ∈ Partitions.cls (LinkClasses.closure a.links) x, ρ y = ρ x :=
    fun _ _ hy => members_eq ha.2.2.1 hy
  simp only [checkIn, cellsCheck, valuesCheck, Bool.and_eq_true] at hc
  have hl := HeapLinks.checkWith_sound (fun x => (LinkClasses.gen_sound ha.2.2.1 (LinkClasses.rep_gen _ x)).symm) hc.2.2.1 ha.2.2.1
  have hrn : ∀ ℓ, ℓ < a.separation.depth →
      SeparationNormal.levelRep (LinkClasses.repIn (LinkClasses.closure a.links)) a.separation.depth ℓ <
        a.separation.depth ∧
      ρ (a.separation.depth - 1 -
        SeparationNormal.levelRep (LinkClasses.repIn (LinkClasses.closure a.links)) a.separation.depth ℓ) =
        ρ (a.separation.depth - 1 - ℓ) := by
    intro ℓ hℓ
    have hle := (LinkClasses.least_le (d := a.separation.depth - 1 - ℓ)
      (l := Partitions.cls (LinkClasses.closure a.links) (a.separation.depth - 1 - ℓ))).1
    simp only [SeparationNormal.levelRep, hℓ, if_true, LinkClasses.repIn]
    refine ⟨by omega, ?_⟩
    have e : a.separation.depth - 1 - (a.separation.depth - 1 -
        LinkClasses.least (a.separation.depth - 1 - ℓ)
          (Partitions.cls (LinkClasses.closure a.links) (a.separation.depth - 1 - ℓ))) =
        LinkClasses.least (a.separation.depth - 1 - ℓ)
          (Partitions.cls (LinkClasses.closure a.links) (a.separation.depth - 1 - ℓ)) := by omega
    rw [e]
    exact (LinkClasses.gen_sound ha.2.2.1 (LinkClasses.rep_gen a.links _)).symm
  have hrn' : ∀ ℓ, ℓ < a.separation.depth →
      (SeparationNormal.levelTable (LinkClasses.repIn (LinkClasses.closure a.links)) a.separation.depth).getD ℓ ℓ <
        a.separation.depth ∧
      ρ (a.separation.depth - 1 -
        (SeparationNormal.levelTable (LinkClasses.repIn (LinkClasses.closure a.links)) a.separation.depth).getD ℓ ℓ) =
        ρ (a.separation.depth - 1 - ℓ) := fun ℓ hℓ => by
    rw [SeparationNormal.levelTable_eq]; exact hrn ℓ hℓ
  refine ⟨?_, ?_, hl, HeapSeparation.checkBy_sound hrn' hc.2.2.2 ha.2.2.2⟩
  · intro f hf
    have hf := List.all_eq_true.mp hc.1 f hf
    split at hf
    · rename_i V hV
      obtain ⟨flds, c, oid, u, he, hr, hm⟩ := HeapKnowledge.cellBy_holds ha hs hV
      exact ⟨flds, c, oid, u, by simpa [PointClaims.mapEnv] using he, hr, ValueSet.le_sound hf hm⟩
    · cases hf
  · intro f hf
    have hf := List.all_eq_true.mp hc.2.1 f hf
    split at hf
    · rename_i V hV
      have hv : V.mem (PointClaims.mapEnv m ρ f.slot) = true := by
        simpa [PointClaims.mapEnv] using HeapKnowledge.valueBy_mem ha hs hV
      have hsb : ∀ y ∈ Partitions.cls (LinkClasses.closure b.links) f.slot,
          PointClaims.mapEnv m ρ y = PointClaims.mapEnv m ρ f.slot :=
        fun _ hy => (LinkClasses.gen_sound hl (LinkClasses.mem_cls_closure.mp hy)).symm
      exact ValueSet.le_sound hf (restrict_mem (fun _ hC => classCtxIn_mem hctx hsb hC) hv)
    · cases hf

end Verification.KnowledgeExpand
