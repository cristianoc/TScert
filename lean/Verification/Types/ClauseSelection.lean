import Verification.Types.PositiveRules

/-! Selection of the target clauses that can cover a source clause
(docs/UNION-SHAPES.md, rules R1–R5). A target clause the selection excludes
covers the source under no sound table: by its outer shape (R1), its
primitive cell (R2), a literal discriminant (R3), a key it requires that the
source lacks (R4), or the bound a dictionary needs of a record (R5). The
engine reads candidates only where that is sound by inclusion: a candidate is
a target clause, so a covering found among them is one of the general rule's.
-/
namespace Verification.ClauseSelection
open PositiveNormalization PositiveGraphs PositiveRules

/-! ### The literal a clause denotes, and the clauses admitting a value -/

/-- The one value of a singleton clause. -/
def litVal : Clause α → Option Val
  | .strLit s => some (.str s)
  | .numLit b => some (.num b)
  | .boolLit b => some (if b then .tru else .fls)
  | .bigintLit i => some (.bigint i)
  | .symbolLit i => some (.sym i)
  | .nul => some .nul
  | .undef => some .undef
  | _ => none

/-- Whether a clause may hold a primitive value: the universes, its family,
or its own literal. Every other clause holds no such value. -/
def admitsVal (c : Clause α) (v : Val) : Bool :=
  match c, v with
  | .top, _ | .source, _ => true
  | .str, .str _ | .num, .num _ | .bigint, .bigint _ | .symbol, .sym _ => true
  | .bool, .tru | .bool, .fls => true
  | .strLit t, .str s => t == s
  | .numLit a, .num b => a == b
  | .numIn S, .num b => S.contains b
  | .strIn S, .str s => S.contains s
  | .boolLit true, .tru | .boolLit false, .fls => true
  | .bigintLit i, .bigint j => i == j
  | .symbolLit i, .sym j => i == j
  | .nul, .nul | .undef, .undef => true
  | _, _ => false

theorem litVal_sem {Ξ : Fam} {X : α → Fam} {P : α → ArgFam} {c : Clause α} {v : Val}
    (h : litVal c = some v) (n W) : semWithArgs Ξ X P c n W v := by
  cases c <;> simp only [litVal, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem litVal_plain {c : Clause α} {v : Val} (h : litVal c = some v) :
    c.carriesInvariant = false := by
  cases c <;> simp_all [litVal, Clause.carriesInvariant]

/-- A clause that does not admit a singleton's value does not hold it. -/
theorem not_admits {Ξ : Fam} {X : α → Fam} {P : α → ArgFam} {a : Clause β} {b : Clause α}
    {v : Val} (hl : litVal a = some v) (hb : admitsVal b v = false) {n W}
    (h : semWithArgs Ξ X P b n W v) : False := by
  by_cases ht : b = .top
  · subst ht; cases a <;> simp_all [admitsVal]
  by_cases hj : b = .source
  · subst hj; cases a <;> simp_all [admitsVal]
  have hsh := semWithArgs_shape ht hj h
  cases a
  case boolLit bv =>
    cases bv <;> simp only [litVal, Option.some.injEq, Bool.false_eq_true,
      ↓reduceIte] at hl <;> subst hl <;>
      cases b <;> simp_all [admitsVal, valueShape, shape, semWithArgs, nulT, undefT, numT,
        strT, bigintT, symbolT]
  all_goals (simp only [litVal, Option.some.injEq, reduceCtorEq] at hl <;> subst hl <;>
    cases b <;> simp_all [admitsVal, valueShape, shape, semWithArgs, nulT, undefT, boolT, numT,
      strT, bigintT, symbolT])

/-! ### R1, R2: shapes and primitive cells -/

/-- **R1.** Coverage relates a clause only to `top`, `source`, or a clause of
its own outer shape, under every table. -/
theorem covers_shape [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} {known : Known ι} {arrows self} {a b : Clause (List ι)}
    (h : CoversWith G sub R known arrows self a b) :
    b = .top ∨ b = .source ∨ shape a = shape b := by
  cases b <;> simp only [reduceCtorEq, true_or, or_true] <;>
    cases a <;> simp_all [CoversWith, shape]

/-- The universes. -/
def isUniverse : Clause α → Bool
  | .top | .source => true
  | _ => false

/-- **R2.** A primitive target that cannot cover a primitive source: one not
admitting the source's literal, a literal or a tag set under a family source,
and a literal or a tag set not holding every element of a source tag set. -/
def primExcl (a b : Clause α) : Bool :=
  match litVal a with
  | some v => !isUniverse b && !admitsVal b v
  | none => match a, b with
    | .str, .strLit _ | .num, .numLit _ | .bool, .boolLit _ | .bigint, .bigintLit _
    | .symbol, .symbolLit _ | .num, .numIn _ | .str, .strIn _ => true
    | .numIn _, .numLit _ | .strIn _, .strLit _ => true
    | .numIn S, .numIn T => !S.all T.contains
    | .strIn S, .strIn T => !S.all T.contains
    | _, _ => false

theorem covers_prim [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} {known : Known ι} {arrows self} {a b : Clause (List ι)}
    (h : CoversWith G sub R known arrows self a b) : primExcl a b = false := by
  cases a <;> cases b <;> simp_all [CoversWith, primExcl, litVal, admitsVal, isUniverse] <;>
    (try split) <;> simp_all

/-! ### R3, R4: discriminants and required keys of object clauses -/

/-- The record operands and views of a plain-object clause. -/
def objParts : Clause α → Option (List (List (Stored α)) × List (PropKey × α))
  | .refs a bs vs .. | .dict a bs vs .. => some (a :: bs, vs)
  | _ => none

/-- The keys a target object clause requires: its fields, and its views but
`length`, which the array store also meets. -/
def fixedOf (c : Clause α) : List (PropKey × α) :=
  match objParts c with
  | some (F, V) => Stored.views F.flatten ++ V.filter (·.1 != lengthKey)
  | none => []

/-- A source object clause's entries: its fields and all its views. -/
def entriesOf (c : Clause α) : List (PropKey × α) :=
  match objParts c with
  | some (F, V) => Stored.views F.flatten ++ V
  | none => []

theorem covers_obj [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} {known : Known ι} {arrows self} {a b : Clause (List ι)}
    (h : CoversWith G sub R known arrows self a b) {Fa Va Fb Vb}
    (ha : objParts a = some (Fa, Va)) (hb : objParts b = some (Fb, Vb)) :
    CoversFields R Fa Fb ∧ CoversViews G R Fa Va Vb := by
  cases a <;> simp only [objParts, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at ha <;>
    cases b <;> simp only [objParts, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hb <;>
    obtain ⟨rfl, rfl⟩ := ha <;> obtain ⟨rfl, rfl⟩ := hb <;> unfold CoversWith at h
  · exact ⟨h.1, h.2.1⟩
  · exact ⟨h.2.1, h.2.2.1⟩
  · exact ⟨h.1, h.2.1⟩
  · exact ⟨h.1, h.2.1⟩

/-- A required target key is matched by a source entry at that key. -/
theorem covers_fixed [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} {known : Known ι} {arrows self} {a b : Clause (List ι)}
    (h : CoversWith G sub R known arrows self a b) {f : PropKey} {B : List ι}
    (hq : (f, B) ∈ fixedOf b) : ∃ p ∈ entriesOf a, p.1 = f ∧ R p.2 B := by
  unfold fixedOf at hq
  split at hq
  · rename_i Fb Vb hb
    cases ha : objParts a with
    | none =>
      exfalso
      cases a <;> simp only [objParts, reduceCtorEq] at ha <;>
        cases b <;> simp only [objParts, reduceCtorEq, Option.some.injEq] at hb <;> unfold CoversWith at h <;>
        simp_all
    | some s =>
      obtain ⟨Fa, Va⟩ := s
      obtain ⟨hfl, hvw⟩ := covers_obj h ha hb
      have he : entriesOf a = Stored.views Fa.flatten ++ Va := by simp [entriesOf, ha]
      rw [he]
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨s, hq⟩ := Stored.mem_views.mp hq
        obtain ⟨g, hg, hqg⟩ := List.mem_flatten.mp hq
        obtain ⟨p, hp, hpf, -, hpB, -⟩ := hfl g hg (f, s, B) hqg
        exact ⟨(p.1, p.2.2), List.mem_append_left _ (Stored.mem_views.mpr ⟨p.2.1, hp⟩), hpf, hpB⟩
      · obtain ⟨hq, hl⟩ := List.mem_filter.mp hq
        rcases hvw (f, B) hq with ⟨p, hp, hpf, hpB⟩ | ⟨hlk, -⟩
        · exact ⟨p, hp, hpf, hpB⟩
        · simp_all
  · simp at hq

variable [DecidableEq ι] (G : NormalGraph ι)

/-- **R4.** The target requires a key at which the source has no entry. -/
@[nospecialize] def keyExcl (a b : Clause (List ι)) : Bool :=
  (objParts a).isSome && (fixedOf b).any fun q => !(entriesOf a).any (·.1 == q.1)

/-- **R3.** The target fixes a key at a plain type, and every source entry at
that key holds a literal the type does not admit. -/
@[nospecialize] def litExcl (a b : Clause (List ι)) : Bool :=
  (fixedOf b).any fun (f, B) => G.plainTy B &&
    let src := (entriesOf a).filter (·.1 == f)
    let ds := clausesOf G B
    !src.isEmpty && src.all fun (_, A) => (clausesOf G A).any fun c =>
      -- A tag set's elements are literals of the entry too.
      c.elements.any fun e => match litVal e with
      | some v => ds.all fun d => !admitsVal d v
      | none => false

/-- **R5.** A record source and a dictionary target, the source with no bound
listing its own keys without the prototype key. -/
def boundExcl : Clause α → Clause α → Bool
  | .refs _ _ _ _ _ ks _, .dict .. => !ks.any fun K => K.among && !K.keys.contains CallArguments.protoField
  | _, _ => false

/-- The target clauses R1–R5 exclude for a source clause. -/
@[nospecialize] def excludes (a b : Clause (List ι)) : Bool :=
  (!isUniverse b && shape a != shape b) || primExcl a b || keyExcl a b || litExcl G a b ||
    boundExcl a b

/-- The clauses of a list that a source clause's exclusions leave. -/
@[nospecialize] def among (a : Clause (List ι)) (cs : List (Clause (List ι))) : List (Clause (List ι)) :=
  cs.filter fun b => !excludes G a b

/-- The candidates of a source clause in a target type. -/
@[nospecialize] def candidates (a : Clause (List ι)) (B : List ι) : List (Clause (List ι)) :=
  among G a (clausesOf G B)

omit [DecidableEq ι] in
theorem mem_candidates {a b : Clause (List ι)} {B : List ι} (h : b ∈ candidates G a B) :
    b ∈ clausesOf G B := (List.mem_filter.mp h).1

omit [DecidableEq ι] in
/-- A covering among the candidates is a covering among the target clauses. -/
theorem any_candidates {a : Clause (List ι)} {B : List ι} {p : Clause (List ι) → Bool}
    (h : (candidates G a B).any p = true) : (clausesOf G B).any p = true := by
  obtain ⟨b, hb, hp⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨b, mem_candidates G hb, hp⟩

/-! ### Every covering is by a candidate, under a sound table -/

/-- A relation each of whose pairs is an inclusion at the assignment `η`. -/
def SoundRel (η : MixedAssignment ι) (R : List ι → List ι → Prop) : Prop :=
  ∀ A B, R A B → FamLe (mixedValues G η A) (mixedValues G η B)

omit [DecidableEq ι] in
/-- An element's literal of a clause of a type is a member of the type. -/
theorem element_member {η : MixedAssignment ι} {A : List ι} {c e : Clause (List ι)} {v : Val}
    (hc : c ∈ clausesOf G A) (he : e ∈ c.elements) (hv : litVal e = some v) {n W} :
    mixedValues G η A n W v := by
  have hev : semWithArgs (excOf G) (mixedValues G η) (mixedArgs G η) e n W v := litVal_sem hv n W
  have hcv := (elements_sem _ _ _ c n W v).mp ⟨e, he, hev⟩
  have hplain : c.carriesInvariant = false := by
    cases c <;> simp [Clause.elements] at he <;> (try subst he) <;>
      first | rfl | exact litVal_plain hv
  exact mixed_expand_mpr ⟨c, hc, hcv, builtinInvariant_of_withoutInvariant hplain _ _ _⟩

omit [DecidableEq ι] in
theorem lit_excluded {η : MixedAssignment ι} {B : List ι} {c : Clause (List ι)} {v : Val}
    (hv : litVal c = some v) (hB : G.plainTy B = true)
    (hx : (clausesOf G B).all (fun d => !admitsVal d v) = true) {n W} :
    ¬ mixedValues G η B n W v := by
  intro hm
  obtain ⟨d, hd, hsem, -⟩ := (mixed_expand η hB n W v).mp hm
  rw [expand_of_plain hB] at hd
  exact not_admits hv (by simpa using List.all_eq_true.mp hx d hd) hsem

/-- **R3, proved.** Under a sound table, a target fixing a key at a plain type
that excludes, for every source entry at the key, a literal of that entry, is
no covering: the entry coverage selects supplies its own counterexample. -/
theorem covers_litExcl {sub : Option (Renaming G)} {R : List ι → List ι → Prop}
    {known : Known ι} {arrows self} {η : MixedAssignment ι} (hR : SoundRel G η R)
    {a b : Clause (List ι)} (h : CoversWith G sub R known arrows self a b) :
    litExcl G a b = false := by
  cases hx : litExcl G a b with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨⟨f, B⟩, hq, hx⟩ := List.any_eq_true.mp hx
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true] at hx
    obtain ⟨hB, -, hall⟩ := hx
    obtain ⟨p, hp, hpf, hpB⟩ := covers_fixed h hq
    obtain ⟨c, hc, hcv⟩ := List.any_eq_true.mp
      (hall p (List.mem_filter.mpr ⟨hp, by simp [hpf]⟩))
    obtain ⟨e, he, hev⟩ := List.any_eq_true.mp hcv
    cases hv : litVal e with
    | none => simp [hv] at hev
    | some v =>
      simp only [hv] at hev
      exact lit_excluded G hv hB hev
        (hR _ _ hpB 0 (ofList []) v (element_member G hc he hv))

/-- **R4, proved.** A target requiring a key the source holds no entry at is
no covering, under every table. -/
theorem covers_keyExcl {sub : Option (Renaming G)} {R : List ι → List ι → Prop}
    {known : Known ι} {arrows self} {a b : Clause (List ι)}
    (h : CoversWith G sub R known arrows self a b) : keyExcl a b = false := by
  cases hx : keyExcl a b with
  | false => rfl
  | true =>
    exfalso
    simp only [keyExcl, Bool.and_eq_true] at hx
    obtain ⟨q, hq, hn⟩ := List.any_eq_true.mp hx.2
    obtain ⟨p, hp, hpf, -⟩ := covers_fixed h hq
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hn
    exact hn p hp hpf

/-- **R5, proved.** A dictionary covers a record only through a bound
listing the record's own keys, the prototype key not among them. -/
theorem covers_boundExcl {sub : Option (Renaming G)} {R : List ι → List ι → Prop}
    {known : Known ι} {arrows self} {a b : Clause (List ι)}
    (h : CoversWith G sub R known arrows self a b) : boundExcl a b = false := by
  cases a <;> cases b <;> simp only [boundExcl]
  case refs.dict ks _ _ _ _ _ _ _ _ =>
    unfold CoversWith at h
    obtain ⟨⟨K, hK, ha, hp, -⟩, -⟩ := h
    simp only [Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨K, hK, ha, by simpa using hp⟩

/-- **R1–R5 together.** Under a sound table every covering target clause is a
candidate: the selection loses no covering. -/
theorem covers_candidate {sub : Option (Renaming G)} {R : List ι → List ι → Prop}
    {known : Known ι} {arrows self} {η : MixedAssignment ι} (hR : SoundRel G η R)
    {a b : Clause (List ι)} (h : CoversWith G sub R known arrows self a b) :
    excludes G a b = false := by
  have h1 : (!isUniverse b && shape a != shape b) = false := by
    rcases covers_shape h with rfl | rfl | hs <;> simp_all [isUniverse]
  simp only [excludes, h1, covers_prim h, covers_keyExcl G h, covers_litExcl G hR h,
    covers_boundExcl G h, Bool.or_self]

end Verification.ClauseSelection
