import Verification.Semantics.HeapLinks
import Verification.Programs.BranchRefinement

/-! Primitive heap and immutable-value facts for expression postconditions. Facts
are execution-state assertions, not extra world contracts or source type labels. -/
namespace Verification.HeapKnowledge
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower HeapFacts

structure Knowledge where
  cells : Facts := []
  values : Facts := []
  links : HeapLinks.Links := []
  deriving DecidableEq, Repr

def ValueHolds (facts : Facts) (ρ : Env) : Prop :=
  ∀ f ∈ facts, ∃ a ∈ f.contents, a.holds (ρ f.slot)

def Holds (k : Knowledge) (ρ : Env) (h : Heap) : Prop :=
  HeapFacts.Holds k.cells ρ h ∧ ValueHolds k.values ρ ∧ HeapLinks.Holds k.links ρ h

theorem empty (ρ h) : Holds ⟨[],[],[]⟩ ρ h := ⟨holds_nil ρ h,by simp [ValueHolds],by simp [HeapLinks.Holds]⟩

/-- A fresh allocation preserves every assertion about existing cells and aliases. -/
theorem alloc_frame {k ρ h v} (hk : Holds k ρ h) : Holds k ρ (h ++ [v]) := by
  refine ⟨?_, hk.2.1, HeapLinks.alloc_frame hk.2.2⟩
  intro f hf
  obtain ⟨flds,c,oid,u,he,hr,a,ha,hv⟩ := hk.1 f hf
  exact ⟨flds,c,oid,u,he,hr.alloc_frames [v],a,ha,hv⟩

/-- The same across a whole object's worth of fresh locations. -/
theorem alloc_frames {k ρ h} (vs : List Val) (hk : Holds k ρ h) : Holds k ρ (h ++ vs) := by
  refine ⟨?_, hk.2.1, HeapLinks.alloc_frames vs hk.2.2⟩
  intro f hf
  obtain ⟨flds,c,oid,u,he,hr,a,ha,hv⟩ := hk.1 f hf
  exact ⟨flds,c,oid,u,he,hr.alloc_frames vs,a,ha,hv⟩

/-- What every one of several states establishes: a fact about a slot and
field each of them states, holding what any of them says it holds; the first's
links that appear verbatim in all the others. Used by the producer at a merge
that is not a cut, where no requirement is stated; every edge is still
checked, and each state's fact covers the union. -/
def meet : List Knowledge → Knowledge
  | [] => ⟨[],[],[]⟩
  | k :: ks =>
    let joined := fun (pick : Knowledge → Facts) =>
      (pick k).filterMap fun f =>
        let others := ks.map fun o => (pick o).filter fun g => g.slot == f.slot && g.field == f.field
        if others.all (!·.isEmpty) then
          some { f with contents := (f.contents ++ others.flatten.flatMap (·.contents)).eraseDups }
        else none
    ⟨(joined (·.cells)).eraseDups, (joined (·.values)).eraseDups,
     let others := ks.map fun o => (Std.HashSet.ofList o.links : Std.HashSet HeapLinks.Link)
     k.links.filter (fun g => others.all (·.contains g))⟩

def check (a b : Knowledge) (m : PointClaims.Mapping) : Bool :=
  HeapFacts.check a.cells b.cells m && (HeapFacts.check a.values b.values m && HeapLinks.check a.links b.links m)

theorem check_sound {a b m ρ h} (hc : check a b m = true) (ha : Holds a ρ h) :
    Holds b (PointClaims.mapEnv m ρ) h := by
  simp only [check,Bool.and_eq_true] at hc
  refine ⟨HeapFacts.check_sound hc.1 ha.1,?_,HeapLinks.check_sound hc.2.2 ha.2.2⟩
  intro f hf
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc.2.1 f hf)
  simp only [Bool.and_eq_true,beq_iff_eq] at hc
  obtain ⟨a,ham,he⟩ := ha.2.1 g hg
  simpa [PointClaims.mapEnv,hc.1] using covers_sound hc.2 ⟨a,ham,he⟩

def shift (k : Knowledge) : Knowledge := ⟨HeapFacts.shift k.cells,HeapFacts.shift k.values,HeapLinks.pull k.links (fun i => [i+1])⟩

theorem shift_holds {k ρ h v} (hk : Holds k ρ h) : Holds (shift k) (push v ρ) h := by
  refine ⟨HeapFacts.shift_holds hk.1,?_,?_⟩
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    exact hk.2.1 g hg
  · apply HeapLinks.pull_holds (pre := fun i => [i+1]) hk.2.2
    intro i j hj
    have hj := List.mem_singleton.mp hj
    subst j
    rfl
/-- Effect-only continuations discard the result slot. Facts about it cannot
be transferred into the old environment. -/
def dropFacts (fs : Facts) : Facts :=
  (fs.filter fun f => 0 < f.slot).map fun f => {f with slot := f.slot - 1}

def dropResult (k : Knowledge) : Knowledge := ⟨dropFacts k.cells,dropFacts k.values,HeapLinks.pull k.links (fun i => if i = 0 then [] else [i-1])⟩

theorem dropResult_holds {k ρ h v} (hk : Holds k (push v ρ) h) :
    Holds (dropResult k) ρ h := by
  constructor
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    have hg := List.mem_filter.mp hg
    have hp : 0 < g.slot := of_decide_eq_true hg.2
    have he : push v ρ g.slot = ρ (g.slot - 1) := by
      cases hs : g.slot with
      | zero => omega
      | succ i => rfl
    simpa [he] using hk.1 g hg.1
  · constructor
    · intro f hf
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      have hg := List.mem_filter.mp hg
      have hp : 0 < g.slot := of_decide_eq_true hg.2
      have he : push v ρ g.slot = ρ (g.slot - 1) := by
        cases hs : g.slot with
        | zero => omega
        | succ i => rfl
      simpa [he] using hk.2.1 g hg.1
    · apply HeapLinks.pull_holds (pre := fun i => if i = 0 then [] else [i-1]) hk.2.2
      intro i j hj
      split at hj
      · simp at hj
      · have hj := List.mem_singleton.mp hj
        subst j
        cases i with
        | zero => contradiction
        | succ i => rfl

/-- Project facts along an executable slot map. All runtime aliases selected by
that map are retained; facts about unselected slots are forgotten. -/
def projectFacts (facts : Facts) (m : PointClaims.Mapping) (count : Nat) : Facts :=
  (List.range count).flatMap fun i =>
    (facts.filter fun f => f.slot == PointClaims.slot m i).map fun f => { f with slot := i }

def project (k : Knowledge) (m : PointClaims.Mapping) (count : Nat) : Knowledge :=
  -- The target slots each source slot is mapped to, in increasing order.
  let preimages : Std.HashMap Nat (List Nat) := (List.range count).foldr
    (fun j acc => acc.alter (PointClaims.slot m j) fun js => some (j :: js.getD [])) ∅
  ⟨projectFacts k.cells m count,projectFacts k.values m count,
    HeapLinks.pull k.links (fun i => preimages.getD i [])⟩

/-- Every live property-read link transfers the observed result predicate,
including observations admitting undefined. -/
def linkFacts (k : Knowledge) (slot : Nat) (R : List Atom) : Facts :=
  (k.links.filter (fun g => (!g.alias && !g.distinct) && g.value == slot)).map
    (fun g => ⟨g.cell,R,g.field⟩)

theorem linkFacts_holds {k slot R ρ h} (hk : Holds k ρ h) (hv : ∃ a ∈ R, a.holds (ρ slot)) :
    HeapFacts.Holds (linkFacts k slot R) ρ h := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  have hg := List.mem_filter.mp hg
  have hg2 := hg.2
  simp only [Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq] at hg2
  have hl := hk.2.2 g hg.1
  simp only [hg2.1.1,hg2.1.2,Bool.false_eq_true,ite_false] at hl
  cases ho : g.optional
  · simp only [ho,Bool.false_eq_true,ite_false] at hl
    obtain ⟨flds,c,oid,l,hl,hfd,hh⟩ := hl
    exact ⟨flds,c,oid,ρ g.value,hl,ReadGave.present hfd hh,by simpa [hg2.2] using hv⟩
  · simp only [ho,ite_true] at hl
    obtain ⟨flds,c,oid,hl,hr⟩ := hl
    exact ⟨flds,c,oid,ρ g.value,hl,hr,by simpa [hg2.2] using hv⟩

/-- An observed Boolean outcome refines cells only through current read links.
The ordinary value fact is useful even when no cell link exists. -/
def observeBoolean (k : Knowledge) (slot : Nat) (q : Bool) : Knowledge :=
  let R := [if q then HeapFacts.Atom.tru else .fls]
  ⟨linkFacts k slot R ++ k.cells,⟨slot,R,valueField⟩ :: k.values,k.links⟩

theorem observeBoolean_holds {k slot q ρ h} (hk : Holds k ρ h)
    (hq : ρ slot = if q then .tru else .fls) : Holds (observeBoolean k slot q) ρ h := by
  have hv : ∃ a ∈ [if q then HeapFacts.Atom.tru else .fls], a.holds (ρ slot) :=
    ⟨(if q then .tru else .fls), by simp, by cases q <;> simpa [HeapFacts.Atom.holds] using hq⟩
  refine ⟨?_,?_,hk.2.2⟩
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact linkFacts_holds hk hv f hf
    · exact hk.1 f hf
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hv
    · exact hk.2.1 f hf

/-- Refine the three broad predicates by a nullish test. Other tests
retain the predicate, including tests whose answer can depend on a prototype. -/
def observeBroad (tag : Tag) (q : Bool) (a : Atom) : List Atom :=
  if a.excludes tag && q then [] else
  match tag, q with
  | .isNul, true => [.nul]
  | .isUndef, true => [.undef]
  | .isNullish, true => [if a.excludes .isUndef then .nul else .undef]
  | .isNul, false => [if a.excludes .isUndef then .nonNullish else .nonNull]
  | .isUndef, false => [if a.excludes .isNul then .nonNullish else .defined]
  | .isNullish, false => [.nonNullish]
  | _, _ => [a]

theorem observeBroad_holds {tag q a v}
    (hb : a = .defined ∨ a = .nonNull ∨ a = .nonNullish)
    (hv : a.holds v) (hq : tagHolds tag v = q ∨ protoFree tag v = false) :
    ∃ b ∈ observeBroad tag q a, b.holds v := by
  rcases hb with rfl | rfl | rfl
  all_goals
    cases tag <;> cases q <;> simp only [observeBroad, Atom.excludes, Bool.and_false,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte, List.mem_singleton, exists_eq_left]
    all_goals first
      | exact hv
      | (cases v <;> simp_all [Atom.holds, tagHolds, protoFree, isVal])

/-- What of a predicate remains where a tag answered `q`: nothing where the
predicate's values all answer the other way; where the tag is equality with
one number or string and holds of a value of its family, that value, a
singleton (equality with a zero holds of both zeros, which stay the family);
the predicate otherwise. -/
def observeAtom (tag : Tag) (q : Bool) (a : Atom) : List Atom :=
  if a == .defined || a == .nonNull || a == .nonNullish then observeBroad tag q a else
  if tagClause tag (a.clause (α := Ty Nat)) == some (!q) then [] else
  match tag, q, a with
  | .numEq b, true, .num => if b &&& 0x7fffffffffffffff == 0 then [.num] else [.numLit b]
  | .strEq t, true, .str => [.strLit t]
  | _, _, a => [a]

/-- A primitive reads no prototype. -/
theorem atom_protoFree {a : Atom} {v : Tm} (h : a.holds v)
    (hd : a ≠ .defined) (hn : a ≠ .nonNull) (hb : a ≠ .nonNullish) (t : Tag) :
    protoFree t v = true := by
  cases v with
  | objAt fs c =>
    cases a <;> simp [Atom.holds] at h
    all_goals first | exact absurd rfl hd | exact absurd rfl hn | exact absurd rfl hb
  | _ => cases t <;> rfl

theorem observeAtom_holds {tag : Tag} {q : Bool} {a : Atom} {v : Tm}
    (hv : a.holds v) (hq0 : tagHolds tag v = q ∨ protoFree tag v = false) :
    ∃ a' ∈ observeAtom tag q a, a'.holds v := by
  by_cases hbroad : a = .defined ∨ a = .nonNull ∨ a = .nonNullish
  · have htest : (a == .defined || a == .nonNull || a == .nonNullish) = true := by
      simpa only [Bool.or_eq_true, beq_iff_eq, or_assoc] using hbroad
    simp only [observeAtom, htest, ↓reduceIte]
    exact observeBroad_holds hbroad hv hq0
  have hd : a ≠ .defined := fun h => hbroad (Or.inl h)
  have hn : a ≠ .nonNull := fun h => hbroad (Or.inr (Or.inl h))
  have hb : a ≠ .nonNullish := fun h => hbroad (Or.inr (Or.inr h))
  have hq : tagHolds tag v = q := hq0.resolve_right (by rw [atom_protoFree hv hd hn hb tag]; simp)
  have hnd : (a == .defined) = false := by simpa using hd
  have hnn : (a == .nonNull) = false := by simpa using hn
  have hnb : (a == .nonNullish) = false := by simpa using hb
  unfold observeAtom
  rw [hnd, hnn, hnb]
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i hbad
    have hanswer := tagClause_sound (Ξ := topF) (S := fun (_ : Ty Nat) => nulT) (P := fun _ _ _ _ => False)
      (n := 0) (W := ofList []) (beq_iff_eq.mp hbad) ((Atom.sem hd hn hb).mpr hv)
    rw [hq] at hanswer
    cases q <;> contradiction
  · split
    · rename_i b _
      split
      · exact ⟨.num, by simp, hv⟩
      · rename_i hb
        obtain ⟨bits, rfl⟩ := hv
        refine ⟨.numLit b, by simp, ?_⟩
        simp only [tagHolds, numberEqual, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hq
        simp only [Atom.holds]
        rcases hq.2 with h | h
        · rw [h]
        · exact absurd (beq_iff_eq.mpr h.2) hb
    · rename_i t _
      obtain ⟨s', rfl⟩ := hv
      refine ⟨.strLit t, by simp, ?_⟩
      simp only [tagHolds, beq_iff_eq] at hq
      simp [Atom.holds, hq]
    · exact ⟨a, by simp, hv⟩

/-- A tag narrows a saved primitive predicate, and its still-live read links transfer
that observation to the heap. No link means no assertion about a mutable cell. -/
def observeTag (k : Knowledge) (slot : Nat) (tag : Tag) (q : Bool) : Knowledge :=
  match k.values.find? (fun f => f.slot == slot) with
  | none => k
  | some f =>
    let R := f.contents.flatMap (observeAtom tag q)
    ⟨linkFacts k slot R ++ k.cells,⟨slot,R,valueField⟩ :: k.values,k.links⟩

theorem observeTag_holds {k slot tag q ρ h} (hk : Holds k ρ h)
    (hq' : tagHolds tag (ρ slot) = q ∨ protoFree tag (ρ slot) = false) :
    Holds (observeTag k slot tag q) ρ h := by
  unfold observeTag
  split
  · exact hk
  · rename_i f hf
    have hm := List.mem_of_find?_eq_some hf
    have hs : f.slot = slot := by simpa using List.find?_some hf
    obtain ⟨a,ha,hv⟩ := hk.2.1 f hm
    have hv : a.holds (ρ slot) := by simpa [hs] using hv
    obtain ⟨a',ha',hv'⟩ := observeAtom_holds hv hq'
    have hR : ∃ b ∈ f.contents.flatMap (observeAtom tag q), b.holds (ρ slot) :=
      ⟨a', List.mem_flatMap.mpr ⟨a,ha,ha'⟩, hv'⟩
    refine ⟨?_,?_,hk.2.2⟩
    · intro f' hf'
      rcases List.mem_append.mp hf' with hf' | hf'
      · exact linkFacts_holds hk hR f' hf'
      · exact hk.1 f' hf'
    · intro f' hf'
      rcases List.mem_cons.mp hf' with rfl | hf'
      · exact hR
      · exact hk.2.1 f' hf'

def observe (k : Knowledge) (slot : Nat) : BranchRefinement.Observation → Knowledge
  | .boolean q => observeBoolean k slot q
  | .tag t q => observeTag k slot t q

theorem observe_holds {k slot o ρ h} (hk : Holds k ρ h)
    (ho : o.holds (ρ slot)) : Holds (observe k slot o) ρ h := by
  cases o with
  | boolean q => exact observeBoolean_holds hk ho
  | tag t q => exact observeTag_holds hk ho

/-- A finite predicate vocabulary exactly interprets supported primitive clauses. -/
def primitive : List (Clause (Ty ι)) → Option (List Atom)
  | [] => some []
  | .nul :: cs => (primitive cs).map ([.nul] ++ ·)
  | .undef :: cs => (primitive cs).map ([.undef] ++ ·)
  | .bool :: cs => (primitive cs).map ([.tru,.fls] ++ ·)
  | .boolLit b :: cs => (primitive cs).map ([if b then .tru else .fls] ++ ·)
  | .num :: cs => (primitive cs).map ([.num] ++ ·)
  | .numLit b :: cs => (primitive cs).map ([.numLit b] ++ ·)
  | .str :: cs => (primitive cs).map ([.str] ++ ·)
  | .strLit s :: cs => (primitive cs).map ([.strLit s] ++ ·)
  | _ => none

/-- A type's members as atoms, when it is of clause rows. -/
def atoms (G : NormalGraph ι) (A : Ty ι) : Option (List Atom) :=
  if G.plainTy A then primitive (expand G A) else none

theorem primitive_sem {G : NormalGraph ι} {cs R} (hc : primitive cs = some R) (n W v) :
    semList (excOf G) (meaning G) (argMeaning G) cs n W v ↔ ∃ a ∈ R, a.holds v := by
  induction cs generalizing R with
  | nil => simp [primitive] at hc; subst R; simp [semList,setSem]
  | cons c cs ih =>
    cases c <;> simp only [primitive] at hc
    all_goals try contradiction
    all_goals
      cases hr : primitive cs with
      | none => simp [hr] at hc
      | some rs =>
        simp only [hr,Option.map_some,Option.some.injEq] at hc
        subst R
        have hi := ih hr
        simp only [semList,setSem,List.mem_cons,exists_eq_or_imp] at hi ⊢
        rw [hi]
        simp [semWithArgs,nulT,undefT,boolT,numT,strT,Atom.holds,apply_ite,or_assoc]
        all_goals try (split <;> simp_all [Atom.holds])

/-- The built-ins asks nothing of primitive clauses. -/
theorem primitive_plain : ∀ {cs : List (Clause (Ty ι))} {R}, primitive cs = some R →
    ∀ c ∈ cs, c.carriesInvariant = false
  | [], _, _ => by simp
  | c :: cs, R, hc => by
    intro d hd
    cases c <;> simp only [primitive] at hc
    all_goals try contradiction
    all_goals
      cases hr : primitive cs with
      | none => simp [hr] at hc
      | some rs =>
        rcases List.mem_cons.mp hd with rfl | hd
        · rfl
        · exact primitive_plain hr d hd

theorem atoms_sem {G : NormalGraph ι} {A R} (h : atoms G A = some R) (n W v) :
    meaning G A n W v ↔ ∃ a ∈ R, a.holds v := by
  unfold atoms at h
  split at h
  · rw [expand_sem G A (by assumption), setSem_row_plain (primitive_plain h)]
    exact primitive_sem h n W v
  · cases h

/-- A tag observation combines the saved predicate with the tested value's
ordinary type. This retains facts such as a falsy object-or-undefined being
undefined, whose broad saved nullish predicate alone is insufficient. -/
@[nospecialize] def observeTyped (G : NormalGraph ι) (Γ : List (Ty ι))
    (k : Knowledge) (slot : Nat) (o : BranchRefinement.Observation) : Knowledge :=
  let out := observe k slot o
  match o, Γ[slot]? with
  | .tag tag q, some A =>
    match atoms G (BranchRefinement.tagSlice G A tag q) with
    | some R => ⟨linkFacts k slot R ++ out.cells, ⟨slot,R,valueField⟩ :: out.values, out.links⟩
    -- A slice of objects a test leaves, `x` truthy where `x` is an object or
    -- undefined: its values are neither null nor undefined.
    | none =>
      if G.plainTy (BranchRefinement.tagSlice G A tag q) && (expand G (BranchRefinement.tagSlice G A tag q)).all
          (fun c => tagClause .isNullish c == some false) then
        ⟨linkFacts k slot [.nonNullish] ++ out.cells, ⟨slot,[.nonNullish],valueField⟩ :: out.values, out.links⟩
      else out
  | _, _ => out

theorem observeTyped_holds {G : NormalGraph ι} {Γ k slot o ρ n W h}
    (he : EnvOk G Γ ρ n W) (hk : Holds k ρ h) (ho : o.holds (ρ slot)) :
    Holds (observeTyped G Γ k slot o) ρ h := by
  have hout := observe_holds hk ho
  unfold observeTyped
  split
  · rename_i tag q A hi
    split
    · rename_i R hr
      have hv := (atoms_sem hr n W (ρ slot)).mp
        (BranchRefinement.tagSlice_sound (he.2 slot A hi) ho)
      refine ⟨?_, ?_, hout.2.2⟩
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact linkFacts_holds hk hv f hf
        · exact hout.1 f hf
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hf
        · exact hv
        · exact hout.2.1 f hf
    · by_cases hn : (G.plainTy (BranchRefinement.tagSlice G A tag q) && (expand G (BranchRefinement.tagSlice G A tag q)).all
          (fun c => tagClause .isNullish c == some false)) = true
      · rw [if_pos hn]
        have hm := BranchRefinement.tagSlice_sound (he.2 slot A hi) ho
        simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hn
        have hq := answers_sound (show Answers G _ .isNullish false from ⟨hn.1, hn.2⟩) hm
        have hval := (meaning_value hm).1
        have hv : ∃ a ∈ [Atom.nonNullish], a.holds (ρ slot) := by
          refine ⟨.nonNullish, by simp, hval, ?_, ?_⟩
          · intro h; rw [h] at hq; simp [tagHolds] at hq
          · intro h; rw [h] at hq; simp [tagHolds] at hq
        refine ⟨?_, ?_, hout.2.2⟩
        · intro f hf
          rcases List.mem_append.mp hf with hf | hf
          · exact linkFacts_holds hk hv f hf
          · exact hout.1 f hf
        · intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact hv
          · exact hout.2.1 f hf
      · rw [if_neg hn]; exact hout
  · exact hout

end Verification.HeapKnowledge
