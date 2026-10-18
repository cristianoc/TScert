import Verification.Programs.PointClaims
import Verification.Semantics.HeapFacts

/-! Refinement of immutable environment slots under observed Boolean or tag outcomes.
Heap contents are not refined: the witness concerns the tested value,
not a retained observation about a mutable location. -/
namespace Verification.BranchRefinement
open ProgramTyping PositiveGraphs PositiveRules PositiveNormalization PointClaims ProgramCertificates
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

def booleanMember [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) (q : Bool) : Bool :=
  (expand G A).any fun c => match c with
    | .bool => true
    | .boolLit b => b == q
    | _ => false

def onlyBoolean (G : NormalGraph ι) (A : Ty ι) : Bool :=
  G.plainTy A && (expand G A).all fun c => match c with
    | .bool | .boolLit _ => true
    | _ => false

theorem booleanMember_sound [DecidableEq ι] {G : NormalGraph ι} {A q}
    (h : booleanMember G A q = true) (n W) :
    meaning G A n W (if q then .tru else .fls) := by
  obtain ⟨c,hc,h⟩ := List.any_eq_true.mp h
  have hrec : c.carriesInvariant = false := by cases c <;> simp_all [Clause.carriesInvariant]
  refine expand_sem_mpr ⟨c,expand_sub hc,?_,builtinInvariant_of_withoutInvariant hrec _ _ _⟩
  cases c <;> simp_all [semWithArgs, boolT]

theorem onlyBoolean_sound {G : NormalGraph ι} {A n W v}
    (h : onlyBoolean G A = true) (hv : meaning G A n W v) :
    v = .tru ∨ v = .fls := by
  simp only [onlyBoolean, Bool.and_eq_true] at h
  rw [expand_sem G A h.1] at hv
  obtain ⟨c,hc,hv,-⟩ := hv
  have h := List.all_eq_true.mp h.2 c hc
  cases c <;> simp_all [semWithArgs, boolT]

/-- Drop only labels whose every clause contradicts the observed tag. A mixed
label is retained intact: this does not assume that labels have uniform shapes.
A parameter or scheme row has no clauses to contradict it, and is retained. -/
def tagSlice (G : NormalGraph ι) (A : Ty ι) (tag : Tag) (q : Bool) : Ty ι :=
  A.filter fun a => !(G.plain a && (expand G [a]).all fun c => (tagClause tag c) == some (!q))

theorem tagSlice_sound {G : NormalGraph ι} {A tag q n W v}
    (hv : meaning G A n W v) (hq : tagHolds tag v = q ∨ protoFree tag v = false) :
    meaning G (tagSlice G A tag q) n W v := by
  obtain ⟨a, ha, hv⟩ := hv
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hv⟩
  cases h : (G.plain a && (expand G [a]).all fun c => (tagClause tag c) == some (!q)) with
  | false => rfl
  | true =>
    simp only [Bool.and_eq_true] at h
    have hop : Answers G [a] tag (!q) := by
      refine ⟨by simp [NormalGraph.plainTy, h.1], fun c hc => ?_⟩
      exact beq_iff_eq.mp (List.all_eq_true.mp h.2 c hc)
    have he := answers_weak hop (show meaning G [a] n W v from ⟨a, by simp, hv⟩) hq
    cases q <;> simp at he

/-! ### Refinement by an observed field

A tag observed on a value read from a field of an object excludes each label
whose record contract for that field answers the other way: the field's
location holds the read value, and its world contract, fixed at allocation,
admits only values of the field's type. The exclusion concerns the object's
label, which is timeless; what the field holds later is not claimed. -/

/-- Whether a record clause fixes the field `f` at a type answering `tag`
with `q`: an invariant field or a readonly view. -/
def fieldAnswers (G : NormalGraph ι) (c : Clause (Ty ι)) (f : PropKey) (tag : Tag) (q : Bool) : Bool :=
  match c with
  | .refs a _ vs _ _ _ => (a ++ vs.filter (·.1 != lengthKey)).any fun p =>
      decide (p.1 = f) && G.plainTy p.2 && (expand G p.2).all fun c => tagClause tag c == some q
  | _ => false

/-- The labels of `A` an object may still have once the value of its field
`f` answered `tag` with `q`. A label is dropped only where every clause of it
fixes `f` at a type answering the other way. -/
def fieldSlice (G : NormalGraph ι) (A : Ty ι) (f : PropKey) (tag : Tag) (q : Bool) : Ty ι :=
  A.filter fun a => !(G.plain a && (expand G [a]).all fun c => fieldAnswers G c f tag (!q))

/-- The value in a record's field location is of the field's type, one level
down: its contract says so, and a heap meeting the world holds it. -/
theorem field_value {G : NormalGraph ι} {c : Clause (Ty ι)} {f : PropKey} {K : Ty ι}
    {n W h v flds code l u}
    (hK : match c with
      | .refs a _ vs _ _ _ => (f, K) ∈ a ++ vs.filter (·.1 != lengthKey)
      | _ => False)
    (hv : semWithArgs (excOf G) (meaning G) (argMeaning G) c (n+1) W v) (hh : HeapOk (n+1) W h)
    (hl : v = .objAt flds code oid) (hf : flds.lookup f = some l) (hu : h[l]? = some u) :
    meaning G K n (trunc n (Nat.le_succ n) W) u := by
  cases c with
  | refs a bs vs os ms ks =>
    simp only at hK
    have take : ∀ (c' : Ctr (n+1)), lookup W l = some c' →
        (∀ (W' : WorldT n) (w : Val), c' n (Nat.lt_succ_self n) W' w → meaning G K n W' w) →
        meaning G K n (trunc n (Nat.le_succ n) W) u := by
      intro c' hc' himp
      obtain ⟨u', hu', hall⟩ := hh.2 l c' hc'
      rw [hu] at hu'
      cases hu'
      exact himp _ _ (hall n (Nat.lt_succ_self n))
    rcases List.mem_append.mp hK with hK | hK
    · obtain ⟨flds', oid', hv', hall⟩ := hv.1.1
      rw [hl] at hv'
      cases hv'
      obtain ⟨l', c', hl', hc', hag⟩ := hall f (meaning G K) (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩)
      rw [hf] at hl'
      cases hl'
      exact take c' hc' fun W' w hw => (hag n (Nat.lt_succ_self n) W' w).mp hw
    · obtain ⟨hK, hKl⟩ := List.mem_filter.mp hK
      obtain ⟨flds', l', c', oid', hv', hl', hc', himp⟩ :=
        viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩) (by simpa using hKl) hv.2.1
      rw [hl] at hv'
      cases hv'
      rw [hf] at hl'
      cases hl'
      exact take c' hc' fun W' w hw => himp n (Nat.lt_succ_self n) W' w hw
  | _ => exact hK.elim

theorem fieldSlice_sound {G : NormalGraph ι} {A : Ty ι} {f tag q n W h v flds code l u}
    (hv : meaning G A (n+1) W v) (hh : HeapOk (n+1) W h)
    (hl : v = .objAt flds code oid) (hf : flds.lookup f = some l) (hu : h[l]? = some u)
    (hq : tagHolds tag u = q ∨ protoFree tag u = false) : meaning G (fieldSlice G A f tag q) (n+1) W v := by
  obtain ⟨a, ha, hva⟩ := hv
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hva⟩
  cases hd : (G.plain a && (expand G [a]).all fun c => fieldAnswers G c f tag (!q)) with
  | false => rfl
  | true =>
    exfalso
    simp only [Bool.and_eq_true, List.all_eq_true] at hd
    have hm : meaning G [a] (n+1) W v := ⟨a, by simp, hva⟩
    rw [expand_sem G [a] (by simp [NormalGraph.plainTy, hd.1])] at hm
    obtain ⟨c, hc, hcv, -⟩ := hm
    have hans := hd.2 c hc
    cases c with
    | refs a' bs vs os ms ks =>
      simp only [fieldAnswers, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hans
      obtain ⟨⟨g, K⟩, hp, ⟨rfl, hplain⟩, hall⟩ := hans
      have hK : Answers G K tag (!q) :=
        ⟨hplain, fun c hc => beq_iff_eq.mp (List.all_eq_true.mp hall c hc)⟩
      have hu' := field_value (c := .refs a' bs vs os ms ks) (K := K) hp hcv hh hl hf hu
      have := answers_weak hK hu' hq
      cases q <;> simp at this
    | _ => simp [fieldAnswers] at hans

/-- An object lacking the key `f` is of no label every clause of which fixes
`f` (an invariant field or a view is a key the object has): the field slice
keeps its label, whatever the observation. This is what a read through a key
the object may lack (an optional link) needs where the key was absent. -/
theorem fieldSlice_absent {G : NormalGraph ι} {A : Ty ι} {f tag q n W v flds code}
    (hv : meaning G A (n+1) W v) (hl : v = .objAt flds code oid) (hf : flds.lookup f = none) :
    meaning G (fieldSlice G A f tag q) (n+1) W v := by
  obtain ⟨a, ha, hva⟩ := hv
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hva⟩
  cases hd : (G.plain a && (expand G [a]).all fun c => fieldAnswers G c f tag (!q)) with
  | false => rfl
  | true =>
    exfalso
    simp only [Bool.and_eq_true, List.all_eq_true] at hd
    have hm : meaning G [a] (n+1) W v := ⟨a, by simp, hva⟩
    rw [expand_sem G [a] (by simp [NormalGraph.plainTy, hd.1])] at hm
    obtain ⟨c, hc, hcv, -⟩ := hm
    have hans := hd.2 c hc
    cases c with
    | refs a' bs vs os ms ks =>
      simp only [fieldAnswers, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hans
      obtain ⟨⟨g, K⟩, hp, ⟨rfl, _⟩, _⟩ := hans
      rcases List.mem_append.mp hp with hK | hK
      · obtain ⟨flds', oid', hv', hall⟩ := hcv.1.1
        rw [hl] at hv'
        cases hv'
        obtain ⟨l', _, hl', _⟩ := hall g (meaning G K) (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩)
        rw [hf] at hl'
        cases hl'
      · obtain ⟨hK, hKl⟩ := List.mem_filter.mp hK
        obtain ⟨flds', l', _, oid', hv', hl', _⟩ :=
          viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩) (by simpa using hKl) hcv.2.1
        rw [hl] at hv'
        cases hv'
        rw [hf] at hl'
        cases hl'
    | _ => simp [fieldAnswers] at hans

/-! ### Exclusion by a field's observed contents

A cell fact states that an object's field holds a value meeting one of its
atoms. Each atom of a primitive family or a singleton is a tag's passing
answer; a label every clause of which fixes the field at a type answering
each such tag `false` is no label of the object. The exclusion concerns the
object's type label, which its contract fixes: it is no claim about what the
field holds later. Successive tests leave successive facts, all of which
hold, so one of them suffices. -/

/-- The test a value meeting an atom passes. -/
def atomTag : HeapFacts.Atom → Option Tag
  | .nul => some .isNul
  | .undef => some .isUndef
  | .tru => some (.boolEq true)
  | .fls => some (.boolEq false)
  | .str => some .isStr
  | .strLit s => some (.strEq s)
  | .num => some .isNum
  | _ => none

theorem atomTag_sound {a : HeapFacts.Atom} {t : Tag} {v : Tm} (ht : atomTag a = some t)
    (hv : a.holds v) : tagHolds t v = true := by
  cases a <;> simp only [atomTag, Option.some.injEq, reduceCtorEq] at ht <;> subst ht <;>
    simp only [HeapFacts.Atom.holds] at hv
  all_goals first
    | (subst hv; simp [tagHolds])
    | (obtain ⟨_, rfl⟩ := hv; simp [tagHolds])

/-- The labels of `A` an object may have whose field `f` holds a value
meeting one of the atoms `R`: a label is dropped where, for every atom, every
clause of it fixes `f` at a type answering that atom's test `false`. -/
def factSlice (G : NormalGraph ι) (A : Ty ι) (f : PropKey) (R : List HeapFacts.Atom) : Ty ι :=
  A.filter fun a => !(G.plain a && !R.isEmpty && R.all fun atom => match atomTag atom with
    | some t => (expand G [a]).all fun c => fieldAnswers G c f t false
    | none => false)

private theorem factSlice_keeps {G : NormalGraph ι} {A : Ty ι} {f : PropKey} {R : List HeapFacts.Atom}
    {atom : HeapFacts.Atom} {t : Tag} (hm : atom ∈ R) (ht : atomTag atom = some t) {a : ι}
    (ha : a ∈ fieldSlice G A f t true) : a ∈ factSlice G A f R := by
  obtain ⟨haA, hkeep⟩ := List.mem_filter.mp ha
  change (!(G.plain a && (expand G [a]).all fun c => fieldAnswers G c f t false)) = true at hkeep
  refine List.mem_filter.mpr ⟨haA, ?_⟩
  have key : (R.all fun atom => match atomTag atom with
      | some t => (expand G [a]).all fun c => fieldAnswers G c f t false
      | none => false) = true → ((expand G [a]).all fun c => fieldAnswers G c f t false) = true := by
    intro hall
    have := List.all_eq_true.mp hall atom hm
    simpa [ht] using this
  revert hkeep key
  generalize (R.all fun atom => match atomTag atom with
      | some t => (expand G [a]).all fun c => fieldAnswers G c f t false
      | none => false) = X
  generalize ((expand G [a]).all fun c => fieldAnswers G c f t false) = Y
  cases G.plain a <;> cases X <;> cases Y <;> cases R.isEmpty <;> simp

/-- The fact slice is sound one level up, as the field slice is: the field's
location holds a value of the field's type one level down, which meets one
of the atoms. -/
theorem factSlice_sound {G : NormalGraph ι} {A : Ty ι} {f R n W h v flds code u}
    (hv : meaning G A (n+1) W v) (hh : HeapOk (n+1) W h)
    (hl : v = .objAt flds code oid) (hr : HeapFacts.ReadGave flds f h u)
    (hR : ∃ atom ∈ R, atom.holds u) : meaning G (factSlice G A f R) (n+1) W v := by
  obtain ⟨atom, hm, hatom⟩ := hR
  cases ht : atomTag atom with
  | none =>
    obtain ⟨a, ha, hva⟩ := hv
    refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hva⟩
    cases hp : G.plain a
    · simp
    · cases hR : R.isEmpty
      · have : (R.all fun atom => match atomTag atom with
            | some t => (expand G [a]).all fun c => fieldAnswers G c f t false
            | none => false) = false := by
          apply List.all_eq_false.mpr
          exact ⟨atom, hm, by simp [ht]⟩
        simp [this]
      · simp [List.isEmpty_iff.mp hR] at hm
  | some t =>
    have hq : tagHolds t u = true ∨ protoFree t u = false := .inl (atomTag_sound ht hatom)
    unfold HeapFacts.ReadGave at hr
    cases hfl : flds.lookup f with
    | some l =>
      rw [hfl] at hr
      obtain ⟨a, ha, hva⟩ := fieldSlice_sound (tag := t) (q := true) hv hh hl hfl hr hq
      exact ⟨a, factSlice_keeps hm ht ha, hva⟩
    | none =>
      obtain ⟨a, ha, hva⟩ := fieldSlice_absent (tag := t) (q := true) hv hl hfl
      exact ⟨a, factSlice_keeps hm ht ha, hva⟩

/-! ### Presence of an optional key

An object owns its keys from its allocation on: a key found present stays
present. An optional field of a record clause is, on an object that has the
key, a field of the clause proper: invariant where the key is writable, a view
where it is readonly (`optT`, `SlotContract`). -/

/-- The index views of a dictionary whose class surely admits `k`, each as a
view of `k`: an object of the dictionary holds no prototype, so where it has
`k` it owns it, at a contract implying the index's type. -/
def presentViews (k : PropKey) (ds : List (IndexKeys × α)) : List (PropKey × α) :=
  (ds.filter fun d => d.1.surely k).map fun d => (k, d.2)

/-- The record clause `c` with its optional key `k` taken as present, and
the dictionary clause with `k` a view at each index type whose class surely
admits it. Other clauses, and a record without that optional key, are
unchanged. A writable optional key becomes an invariant field only of a
record whose objects are ordinary (an invariant field already, or a closed
own-key bound): a field a host object might hold is read as a view. -/
def promote (k : PropKey) : Clause α → Clause α
  | .refs a bs vs os ms ks =>
    match os.find? (fun o => decide (o.key = k)) with
    | some o =>
      if o.readonly || ((a :: bs).flatten.isEmpty && !ks.any KeyBound.closed) then
        .refs a bs (vs ++ [(k, o.type)]) os ms ks
      else .refs (a ++ [(k, o.type)]) bs vs os ms ks
    | none => .refs a bs vs os ms ks
  | .dict a bs vs ds os ms ks cs => .dict a bs (vs ++ presentViews k ds) ds os ms ks cs
  | c => c

/-- What a test or a read says of an object and a key: where it lacks the
key, it holds a prototype. An object of a record naming the key as optional
holds none where it lacks it (`optT`), so there it has the key. -/
def KeyFound (k : PropKey) (v : Tm) : Prop :=
  ∀ flds code oid, v = .objAt flds code oid → flds.lookup k = none →
    (flds.lookup CallArguments.protoField).isSome = true

theorem promote_sound {X : α → Fam} {P : α → ArgFam} {k : PropKey} {c : Clause α} {n W v}
    (hc : semWithArgs Ξ X P c n W v) (hk : KeyFound k v) :
    semWithArgs Ξ X P (promote k c) n W v := by
  cases c with
  | refs a bs vs os ms ks =>
    simp only [promote]
    split
    · rename_i o ho
      have hmem := List.mem_of_find?_eq_some ho
      have hkey : o.key = k := by simpa using List.find?_some ho
      obtain ⟨⟨⟨flds, oid, hv, hrec⟩, hbs⟩, hview, hopt, hmeth, hkeys⟩ := hc
      subst hv
      have hmem' : o.map X ∈ os.map (·.map X) := List.mem_map.mpr ⟨o, hmem, rfl⟩
      obtain ⟨l, hl⟩ : ∃ l, flds.lookup k = some l := by
        cases hlk : flds.lookup k with
        | some l => exact ⟨l, rfl⟩
        | none =>
          have hnp := optT_no_proto hmem' hopt (by simpa [OptionalField.map, hkey] using hlk)
          have hp := hk flds .absent oid rfl hlk
          rw [hnp] at hp
          cases hp
      have hl' : flds.lookup (o.map X).key = some l := by simpa [OptionalField.map, hkey] using hl
      obtain ⟨c', hw, hsc⟩ := optT_present hmem' hopt hl'
      by_cases hcond : (o.readonly || ((a :: bs).flatten.isEmpty && !ks.any KeyBound.closed)) = false
      · rw [if_neg (by rw [hcond]; exact Bool.false_ne_true)]
        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_false'] at hcond
        have hro : o.readonly = false := hcond.1
        refine ⟨⟨⟨flds, oid, rfl, ?_⟩, hbs.1, fun _ => ?_⟩, hview, hopt, hmeth, hkeys⟩
        · intro f T hm
          simp only [ReferenceConjunctions.famsOf, List.map_append, List.mem_append,
            List.map_cons, List.map_nil, List.mem_singleton] at hm
          rcases hm with hm | hm
          · exact hrec f T hm
          · cases hm
            refine ⟨l, c', hl, hw, fun j hj W' u => ⟨(hsc j hj W' u).1, ?_⟩⟩
            exact (hsc j hj W' u).2 (by simp [OptionalField.map, hro])
        · by_cases hne : (a :: bs).flatten = []
          · have hc : ks.any KeyBound.closed = true := by
              rcases hcond.2 with h | h
              · simp [hne] at h
              · exact h
            obtain ⟨K, hK, hKc⟩ := List.any_eq_true.mp hc
            intro flds' oid' he
            cases he
            exact KeyBound.closed_lookup hKc (hkeys K hK)
          · exact hbs.2 (ReferenceConjunctions.famsOf_flatten_ne hne)
      · have hc' : (o.readonly || ((a :: bs).flatten.isEmpty && !ks.any KeyBound.closed)) = true := by
          revert hcond
          cases (o.readonly || ((a :: bs).flatten.isEmpty && !ks.any KeyBound.closed)) <;> simp
        rw [if_pos hc']
        refine ⟨⟨⟨flds, oid, rfl, hrec⟩, hbs⟩, ?_, hopt, hmeth, hkeys⟩
        intro f T hm
        simp only [ReferenceConjunctions.famsOf, List.map_append, List.mem_append,
          List.map_cons, List.map_nil, List.mem_singleton] at hm
        rcases hm with hm | hm
        · exact hview f T hm
        · cases hm
          exact .inl (viewT_single ⟨flds, l, c', oid, rfl, hl, hw, fun j hj W' u hu => (hsc j hj W' u).1 hu⟩)
    · exact hc
  | dict a bs vs ds os ms ks cs =>
    obtain ⟨hr, hview, ⟨hd, hcs⟩, hopt, hmeth, hkeys⟩ := hc
    refine ⟨hr, fun f T hm => ?_, ⟨hd, hcs⟩, hopt, hmeth, hkeys⟩
    obtain ⟨i, hi, rfl⟩ := ReferenceConjunctions.mem_famsOf.mp hm
    rcases List.mem_append.mp hi with hi | hi
    · exact hview f _ (ReferenceConjunctions.mem_famsOf.mpr ⟨i, hi, rfl⟩)
    · obtain ⟨x, hx, he⟩ := List.mem_map.mp hi
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hxd, hs⟩ := List.mem_filter.mp hx
      obtain ⟨flds, oid, rfl, hnp, -⟩ := hd x hxd
      obtain ⟨l, hl⟩ : ∃ l, flds.lookup k = some l := by
        cases hlk : flds.lookup k with
        | some l => exact ⟨l, rfl⟩
        | none =>
          have hp := hk flds .absent oid rfl hlk
          rw [hnp.1] at hp
          cases hp
      obtain ⟨c, hw, hag⟩ := dictViewT_present (hd x hxd) (IndexKeys.surely_admits hs) hl
      exact .inl (viewT_single ⟨flds, l, c, oid, rfl, hl, hw, hag⟩)
  | _ => exact hc

/-- Whether every member of `xs` is one of `ys`. -/
def within [DecidableEq β] (xs ys : List β) : Bool := xs.all fun x => decide (x ∈ ys)

theorem within_mem [DecidableEq β] {xs ys : List β} (h : within xs ys = true) {x} (hx : x ∈ xs) :
    x ∈ ys := of_decide_eq_true (List.all_eq_true.mp h x hx)

/-- A record clause asking no more than another: each of its operands is one
of the other's. Every part of a record clause's meaning is a statement about
each of its operands, so asking fewer is weaker. -/
def weaker [DecidableEq α] : Clause α → Clause α → Bool
  | .refs a bs vs os ms ks, .refs a' bs' vs' os' ms' ks' =>
    within a a' && within bs bs' && within vs vs' && within os os' && within ms ms' && within ks ks'
  | .dict a bs vs ds os ms ks cs, .dict a' bs' vs' ds' os' ms' ks' cs' =>
    within a a' && within bs bs' && within vs vs' && within ds ds' && within os os' &&
      within ms ms' && within ks ks' && within cs cs'
  | _, _ => false

/-- Asking fewer operands names an invariant field only where asking more
does. -/
theorem fewer_named [DecidableEq α] {X : α → Fam} {a a' : List (PropKey × α)}
    {bs bs' : List (List (PropKey × α))} (ha : within a a' = true) (hb : within bs bs' = true)
    (hne : (ReferenceConjunctions.famsOf X a :: bs.map (ReferenceConjunctions.famsOf X)).flatten ≠ []) :
    (ReferenceConjunctions.famsOf X a' :: bs'.map (ReferenceConjunctions.famsOf X)).flatten ≠ [] := by
  intro he
  apply hne
  rw [List.eq_nil_iff_forall_not_mem]
  intro q hq
  obtain ⟨L, hL, hqL⟩ := List.mem_flatten.mp hq
  have hm : q ∈ (ReferenceConjunctions.famsOf X a' :: bs'.map (ReferenceConjunctions.famsOf X)).flatten := by
    rcases List.mem_cons.mp hL with rfl | hL
    · obtain ⟨⟨f, i⟩, hi, rfl⟩ := List.mem_map.mp hqL
      exact List.mem_flatten.mpr ⟨_, List.mem_cons_self,
        ReferenceConjunctions.mem_famsOf.mpr ⟨i, within_mem ha hi, rfl⟩⟩
    · obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hL
      exact List.mem_flatten.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_map_of_mem (within_mem hb hb')), hqL⟩
  rw [he] at hm
  cases hm

theorem weaker_sound [DecidableEq α] {X : α → Fam} {P : α → ArgFam} {d c : Clause α} {n W v}
    (hw : weaker d c = true) (hc : semWithArgs Ξ X P c n W v) : semWithArgs Ξ X P d n W v := by
  cases d with
  | refs a bs vs os ms ks =>
    cases c with
    | refs a' bs' vs' os' ms' ks' =>
      simp only [weaker, Bool.and_eq_true] at hw
      obtain ⟨⟨⟨⟨⟨ha, hb⟩, hv⟩, ho⟩, hm⟩, hk⟩ := hw
      obtain ⟨⟨⟨flds, oid, hvf, hrec⟩, hbs⟩, hview, hopt, hmeth, hkeys⟩ := hc
      refine ⟨⟨⟨flds, oid, hvf, fun f T hmem => ?_⟩, fun B hB => ?_,
        fun hne => hbs.2 (fewer_named ha hb hne)⟩, fun f T hmem => ?_, ?_,
        fun m hm' => ?_, fun K hK => hkeys K (within_mem hk hK)⟩
      · obtain ⟨i, hi, rfl⟩ := ReferenceConjunctions.mem_famsOf.mp hmem
        exact hrec f _ (ReferenceConjunctions.mem_famsOf.mpr ⟨i, within_mem ha hi, rfl⟩)
      · obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hB
        exact hbs.1 _ (List.mem_map.mpr ⟨B', within_mem hb hB', rfl⟩)
      · obtain ⟨i, hi, rfl⟩ := ReferenceConjunctions.mem_famsOf.mp hmem
        exact hview f _ (ReferenceConjunctions.mem_famsOf.mpr ⟨i, within_mem hv hi, rfl⟩)
      · obtain ⟨flds', oid', hv', hp, hf⟩ := hopt
        refine ⟨flds', oid', hv', fun o hmo => ?_, fun o hmo => ?_⟩
        · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hmo
          exact hp _ (List.mem_map.mpr ⟨o', within_mem ho ho', rfl⟩)
        · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hmo
          exact hf _ (List.mem_map.mpr ⟨o', within_mem ho ho', rfl⟩)
      · obtain ⟨m', hm'', rfl⟩ := List.mem_map.mp hm'
        exact hmeth _ (List.mem_map.mpr ⟨m', within_mem hm hm'', rfl⟩)
    | _ => simp [weaker] at hw
  | dict a bs vs ds os ms ks cs =>
    cases c with
    | dict a' bs' vs' ds' os' ms' ks' cs' =>
      simp only [weaker, Bool.and_eq_true] at hw
      obtain ⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hv⟩, hds⟩, ho⟩, hm⟩, hk⟩, hcs⟩ := hw
      obtain ⟨⟨⟨flds, oid, hvf, hrec⟩, hbs⟩, hview, ⟨hd, hc⟩, hopt, hmeth, hkeys⟩ := hc
      refine ⟨⟨⟨flds, oid, hvf, fun f T hmem => ?_⟩, fun B hB => ?_,
        fun hne => hbs.2 (fewer_named ha hb hne)⟩, fun f T hmem => ?_,
        ⟨fun x hx => hd x (within_mem hds hx), fun x hx => hc x (within_mem hcs hx)⟩, ?_,
        fun m hm' => ?_, fun K hK => hkeys K (within_mem hk hK)⟩
      · obtain ⟨i, hi, rfl⟩ := ReferenceConjunctions.mem_famsOf.mp hmem
        exact hrec f _ (ReferenceConjunctions.mem_famsOf.mpr ⟨i, within_mem ha hi, rfl⟩)
      · obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hB
        exact hbs.1 _ (List.mem_map.mpr ⟨B', within_mem hb hB', rfl⟩)
      · obtain ⟨i, hi, rfl⟩ := ReferenceConjunctions.mem_famsOf.mp hmem
        exact hview f _ (ReferenceConjunctions.mem_famsOf.mpr ⟨i, within_mem hv hi, rfl⟩)
      · obtain ⟨flds', oid', hv', hp, hf⟩ := hopt
        refine ⟨flds', oid', hv', fun o hmo => ?_, fun o hmo => ?_⟩
        · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hmo
          exact hp _ (List.mem_map.mpr ⟨o', within_mem ho ho', rfl⟩)
        · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hmo
          exact hf _ (List.mem_map.mpr ⟨o', within_mem ho ho', rfl⟩)
      · obtain ⟨m', hm'', rfl⟩ := List.mem_map.mp hm'
        exact hmeth _ (List.mem_map.mpr ⟨m', within_mem hm hm'', rfl⟩)
    | _ => simp [weaker] at hw
  | _ => simp [weaker] at hw

theorem weaker_record [DecidableEq α] {d c : Clause α} (h : weaker d c = true) :
    d.record = true ∧ c.record = true := by
  unfold weaker at h
  split at h <;> first | exact ⟨rfl, rfl⟩ | simp at h

theorem promote_record (k : PropKey) (c : Clause α) : (promote k c).record = c.record := by
  cases c <;> simp only [promote] <;> (try split) <;> (try split) <;> rfl

/-- Every value of `A` that has the key `k` is one of `B`: each clause of `A`,
with `k` taken as present, asks at least what one clause of `B` does. -/
def promotes [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) (k : PropKey) : Bool :=
  G.plainTy A && (expand G A).all fun c => (expand G B).any fun d => weaker d (promote k c)

theorem promotes_sound [DecidableEq ι] {G : NormalGraph ι} {A B : Ty ι} {k : PropKey} {n W v}
    (hp : promotes G A B k = true) (hv : meaning G A n W v)
    (hk : KeyFound k v) : meaning G B n W v := by
  simp only [promotes, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hp
  obtain ⟨c, hc, hcv, hinv⟩ := (expand_sem G A hp.1 n W v).mp hv
  obtain ⟨d, hd, hw⟩ := hp.2 c hc
  -- `weaker` holds of two record clauses only, and `promote` keeps a
  -- clause's kind.
  have hdr : d.record = true ∧ c.record = true := by
    obtain ⟨h1, h2⟩ := weaker_record hw
    exact ⟨h1, (promote_record k c).symm.trans h2⟩
  exact expand_sem_mpr ⟨d, expand_sub hd, weaker_sound hw (promote_sound hcv hk),
    (builtinInvariant_carriesInvariant (Clause.carriesInvariant_of_record hdr.2) (Clause.carriesInvariant_of_record hdr.1)).mp hinv⟩

/-- A small, explicit vocabulary of observations established by execution. -/
inductive Observation where
  | boolean (value : Bool)
  | tag (test : Tag) (answer : Bool)

def Observation.holds : Observation → Tm → Prop
  | .boolean q, v => v = (if q then .tru else .fls)
  -- `key in o` on an object reading a prototype may answer either way.
  | .tag t q, v => tagHolds t v = q ∨ protoFree t v = false

/-- The durable refinement obligation. B is supplied; no canonical filtered
representation, join, or inferred invariant is required by this contract. -/
def ObservedSub (G : NormalGraph ι) (A B : Ty ι) (o : Observation) : Prop :=
  ∀ n W v, meaning G A n W v → o.holds v → meaning G B n W v

/-- Whether one of the clauses `cs` holds every value a passed tag test
admits: `string` after `typeof x === "string"`, whatever `x` was before,
`unknown` included. A test naming one primitive family needs that family's
clause; `typeof x === "function"` needs both function clauses without
signatures, `arrs [] []` for the invocable values and `ctors [] []` for the
class values. -/
def familyMember (cs : List (Clause α)) : Tag → Bool → Bool
  | .isStr, true => cs.any fun c => match c with | .str => true | _ => false
  | .isNum, true => cs.any fun c => match c with | .num => true | _ => false
  | .isBigint, true => cs.any fun c => match c with | .bigint => true | _ => false
  | .isSymbol, true => cs.any fun c => match c with | .symbol => true | _ => false
  | .isUndef, true => cs.any fun c => match c with | .undef => true | _ => false
  | .isNul, true => cs.any fun c => match c with | .nul => true | _ => false
  | .isBool, true => cs.any fun c => match c with | .bool => true | _ => false
  | .isFun, true => (cs.any fun c => match c with | .arrs [] [] => true | _ => false) &&
      cs.any fun c => match c with | .ctors [] [] => true | _ => false
  -- Equality with one number other than a zero, or one string, holds of that
  -- value alone.
  | .numEq b, true => b &&& 0x7fffffffffffffff != 0 &&
      cs.any fun c => match c with | .numLit b' => b' == b | _ => false
  | .strEq s, true => cs.any fun c => match c with | .strLit s' => s' == s | _ => false
  | _, _ => false

/-- A closed value a family test admits is in one of the family's clauses,
none of them a record's. -/
theorem familyMember_sound {X : α → Fam} {P : α → ArgFam} {cs : List (Clause α)} {t : Tag} {q : Bool}
    (hm : familyMember cs t q = true) {n W v} (hv : isVal v = true) (hs : Scoped 0 v)
    (ht : tagHolds t v = q) : ∃ c ∈ cs, semWithArgs Ξ X P c n W v ∧ c.carriesInvariant = false := by
  cases t <;> cases q <;> simp only [familyMember, Bool.false_eq_true] at hm
  case numEq.true b =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hm
    obtain ⟨c, hc, hk⟩ := List.any_eq_true.mp hm.2
    cases c <;> simp at hk
    subst hk
    cases v <;> simp [tagHolds, isVal] at ht hv
    rename_i bits
    simp only [numberEqual, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht.2 with h | h
    · subst h
      exact ⟨_, hc, by simp [semWithArgs], rfl⟩
    · exact absurd h.2 hm.1
  case strEq.true s =>
    obtain ⟨c, hc, hk⟩ := List.any_eq_true.mp hm
    cases c <;> simp at hk
    subst hk
    cases v <;> simp [tagHolds, isVal] at ht hv
    subst ht
    exact ⟨_, hc, by simp [semWithArgs], rfl⟩
  case isFun.true =>
    simp only [Bool.and_eq_true, List.any_eq_true] at hm
    obtain ⟨⟨a, ha, hka⟩, ⟨k, hk, hkk⟩⟩ := hm
    cases v <;> simp [tagHolds] at ht
    rename_i fs code oid
    cases code with
    | absent => simp at ht
    | bound target r pre =>
      have hi : Invocable (.objAt fs (.bound target r pre) oid) := ⟨_, _, _, rfl, rfl, hs⟩
      refine ⟨a, ha, ?_, ?_⟩ <;> (split at hka <;> simp at hka)
      · exact ⟨⟨hi, by simp⟩, ⟨hi, by simp⟩⟩
      · rfl
    | graph arity E K start caps kind rest =>
      cases kind with
      | call =>
        have hi : Invocable (.objAt fs (.graph arity E K start caps .call rest) oid) :=
          ⟨_, _, _, rfl, rfl, hs⟩
        refine ⟨a, ha, ?_, ?_⟩ <;> (split at hka <;> simp at hka)
        · exact ⟨⟨hi, by simp⟩, ⟨hi, by simp⟩⟩
        · rfl
      | sloppy =>
        have hi : Invocable (.objAt fs (.graph arity E K start caps .sloppy rest) oid) :=
          ⟨_, _, _, rfl, rfl, hs⟩
        refine ⟨a, ha, ?_, ?_⟩ <;> (split at hka <;> simp at hka)
        · exact ⟨⟨hi, by simp⟩, ⟨hi, by simp⟩⟩
        · rfl
      | construct =>
        have hc : Constructible (.objAt fs (.graph arity E K start caps .construct rest) oid) :=
          ⟨_, _, _, _, _, _, _, _, rfl, hs⟩
        refine ⟨k, hk, ?_, ?_⟩ <;> (split at hkk <;> simp at hkk)
        · exact ⟨⟨⟨hc, by simp⟩, ⟨hc, by simp⟩⟩, CallableConjunctions.props_nil, CallableConjunctions.views_nil⟩
        · rfl
  all_goals
    obtain ⟨c, hc, hk⟩ := List.any_eq_true.mp hm
    cases c <;> simp at hk
    cases v <;> simp [tagHolds, isVal] at ht hv <;>
      exact ⟨_, hc, by simp [semWithArgs, nulT, undefT, boolT, numT, strT, bigintT, symbolT], rfl⟩

/-- Whether one clause of `B` holds every value a passed tag test admits
(`familyMember`). -/
def tagMember (G : NormalGraph ι) (B : Ty ι) (t : Tag) (q : Bool) : Bool :=
  familyMember (expand G B) t q

theorem tagMember_sound {G : NormalGraph ι} {B : Ty ι} {t : Tag} {q : Bool}
    (hm : tagMember G B t q = true) {n W v} (hv : isVal v = true) (hs : Scoped 0 v)
    (ht : tagHolds t v = q) : meaning G B n W v := by
  obtain ⟨c, hc, hcv, hrec⟩ := familyMember_sound hm hv hs ht
  exact expand_sem_mpr ⟨c, expand_sub hc, hcv, builtinInvariant_of_withoutInvariant hrec _ _ _⟩

/-! ### A type parameter's value under a test

A meet row `p ⊓ cs` holds the values the assignment gives its parts that are
also in its clauses `cs`. Where a test answers `q`, such a value is in a
clause the test does not contradict, so it is in a meet row of the same parts
(or of fewer) holding that clause, or, for a family test, holding the family's
clauses: `T ⊓ (null | undefined | number)` is `T ⊓ number` where `x ?? d`
takes `x`, and `T ⊓ unknown` is `T ⊓ Function` where `typeof x === "function"`
holds. The parts are not read, so this holds at every assignment of them. -/

/-- The meet rows of `B` whose parts are among the meet row `a`'s. -/
def meetTargets [DecidableEq ι] (G : NormalGraph ι) (a : ι) (B : Ty ι) : List ι :=
  B.filter fun b => G.meetRow b && (meetParts G b).all fun p => (meetParts G a).contains p

/-- Every label the tag slice keeps is in `B`, or is a meet row each of
whose clauses the test contradicts, a meet target of `B` holds, or whose
family the meet targets' clauses hold. -/
def meetSlice [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) (t : Tag) (q : Bool) : Bool :=
  (tagSlice G A t q).all fun a => B.contains a ||
    (G.meetRow a && (meetClauses G a).all fun c => tagClause t c == some (!q) ||
      (meetTargets G a B).any (fun b => (meetClauses G b).contains c) ||
      familyMember ((meetTargets G a B).flatMap (meetClauses G)) t q)

theorem meetSlice_sound [DecidableEq ι] {G : NormalGraph ι} {A B : Ty ι} {t : Tag} {q : Bool}
    (h : meetSlice G A B t q = true) {n W v} (hv : meaning G A n W v)
    (ho : tagHolds t v = q ∨ protoFree t v = false) : meaning G B n W v := by
  obtain ⟨a, ha, hva⟩ := tagSlice_sound hv ho
  have ha' := List.all_eq_true.mp h a ha
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at ha'
  rcases ha' with hB | ⟨hmr, hcs⟩
  · exact ⟨a, hB, hva⟩
  obtain ⟨hparts, c, hc, hcv⟩ := (meet_row_iff (η := G.env) hmr).mp hva
  have target : ∀ b ∈ meetTargets G a B, (∃ d ∈ meetClauses G b, mixedSem G G.env d n W v) →
      meaning G B n W v := by
    intro b hb hd
    simp only [meetTargets, List.mem_filter, Bool.and_eq_true, List.all_eq_true,
      List.contains_iff_mem] at hb
    exact ⟨b, hb.1, (meet_row_iff hb.2.1).mpr ⟨fun p hp => hparts p (hb.2.2 p hp), hd⟩⟩
  have hcc := List.all_eq_true.mp hcs c hc
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.contains_iff_mem] at hcc
  rcases hcc with (hno | ⟨b, hb, hcb⟩) | hfam
  · have hpf := tagClause_protoFree hno hcv.1
    have hans := tagClause_sound hno hcv.1
    rcases ho with ho | ho
    · rw [ho] at hans; cases q <;> simp at hans
    · rw [hpf] at ho; cases ho
  · exact target b hb ⟨c, hcb, hcv⟩
  · have hq : tagHolds t v = q := ho.resolve_right (by
      cases t <;> cases q <;> simp [familyMember] at hfam <;> simp [protoFree])
    obtain ⟨d, hd, hdv, hrec⟩ := familyMember_sound (X := mixedValues G G.env) (P := mixedArgs G G.env)
      hfam (meaning_value hv).1 (meaning_value hv).2 hq
    obtain ⟨b, hb, hdb⟩ := List.mem_flatMap.mp hd
    exact target b hb ⟨d, hdb, hdv, builtinInvariant_of_withoutInvariant hrec n W v⟩

/-- A passed `hasKey` test finds its key present: `check` of the key. -/
def presentKey (t : Tag) (q : Bool) (check : PropKey → Bool) : Bool :=
  match t, q with
  | .hasKey k, true => check k
  | _, _ => false

/-- A passed `in` test found the key on the object's chain: the object's own,
or, where it lacks it, one its prototype chain holds. -/
theorem presentKey_sound {t : Tag} {q : Bool} {check : PropKey → Bool}
    (h : presentKey t q check = true) {v} (hv : tagHolds t v = q ∨ protoFree t v = false) :
    ∃ k, check k = true ∧ KeyFound k v := by
  cases t <;> cases q <;> simp only [presentKey, Bool.false_eq_true] at h
  rename_i k
  refine ⟨k, h, ?_⟩
  intro flds code oid he hl
  subst he
  rcases hv with hv | hv
  · simp [tagHolds, hl] at hv
  · simp only [protoFree, hl, Option.isSome_none, Bool.false_or] at hv
    simpa [Option.isSome_iff_ne_none] using hv

/-! ### A built-in array

`Array.isArray` finds that an object owns the store key. A record or
dictionary type is of objects meeting the built-in array invariant
(`PositiveGraphs.builtinInvariant`): one owning the store key holds a possibly sparse store
and the built-in prototype and owns no key it provides. So where the test holds,
a member of such a type is a member of the built-in `sparse ReadonlyArray<unknown>`, the
array shape over a store of values (`builtinArrayLabel`). -/

/-- A type every JavaScript value meets. -/
def valuesTy [DecidableEq ι] (G : NormalGraph ι) (T : Ty ι) : Bool :=
  T.any fun t => G.plain t && ((G t).contains .top || (G t).contains .source)

theorem valuesTy_sound [DecidableEq ι] {G : NormalGraph ι} {T : Ty ι} (h : valuesTy G T = true)
    {n W v} (hv : excOf G n W v) : meaning G T n W v := by
  obtain ⟨t, ht, hp⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hp
  refine ⟨t, ht, (unfold_plain hp.1 n W v).mpr ?_⟩
  rcases hp.2 with h | h
  · exact ⟨.top, h, ⟨sourceVal_isVal hv.1.1, hv.1.2⟩, builtinInvariant_of_withoutInvariant rfl n W v⟩
  · exact ⟨.source, h, hv⟩

/-- A type holding every possibly sparse store of values: a readonly array store at a
type every value meets. -/
def storeOfValues [DecidableEq ι] (G : NormalGraph ι) (S : Ty ι) : Bool :=
  S.any fun s => G.plain s && (G s).any fun c => match c with
    | .list ⟨[], [], some T, true, .sparse⟩ [] => valuesTy G T
    | _ => false

theorem storeOfValues_sound [DecidableEq ι] {G : NormalGraph ι} {S U : Ty ι}
    (h : storeOfValues G S = true) (hu : exactUnknown G U = true) {n W v}
    (hv : builtinStoreT (builtinValues G U) n W v) : meaning G S n W v := by
  obtain ⟨s, hs, hp⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, List.any_eq_true] at hp
  obtain ⟨hplain, c, hc, hcv⟩ := hp
  refine ⟨s, hs, (unfold_plain hplain n W v).mpr ⟨c, hc, ?_, ?_⟩⟩
  · split at hcv
    · rename_i T
      obtain ⟨ls, rfl, hd, hlen, hbound, hreq, hopt, hrest⟩ := hv
      refine ⟨⟨ls, rfl, hd, by simp [tupleFams], by simp [tupleFams],
        fun i A hA => by simp [tupleFams] at hA, fun i A l hA => by simp [tupleFams] at hA, ?_⟩, by simp⟩
      intro i l hi hl
      obtain ⟨E, c', hE, hw, hag⟩ := hrest i l hi hl
      cases hE
      exact ⟨_, c', rfl, hw, fun j hj W' u => ⟨fun hu' =>
        valuesTy_sound hcv (exactUnknown_sound hu ((hag j hj W' u).1 hu')), fun h => nomatch h⟩⟩
    · cases hcv
  · split at hcv
    · exact builtinInvariant_of_withoutInvariant rfl n W v
    · cases hcv

/-- The built-in `readonly unknown[]`: a clause row holding the array shape
over a store of values, `ArrayProto` read at a type without parameters, and
the keys that prototype provides. -/
def builtinArrayLabel [DecidableEq ι] (G : NormalGraph ι) (L : ι) : Bool :=
  match G.builtins with
  | none => false
  | some r => builtinsFree G r.proto && exactUnknown G r.unknown && G.plain L && match G L with
    | [.refs [] [] [(k, S), (p, P)] [] [] [K]] =>
      k == CallArguments.arrayStoreField && p == CallArguments.protoField && P == r.proto &&
        K == ⟨false, r.keys⟩ && storeOfValues G S
    | _ => false

/-- **A built-in array.** A member of a record or dictionary clause that
owns the store key is a member of the built-in `sparse ReadonlyArray<unknown>`. -/
theorem builtinArray_of_record [DecidableEq ι] {G : NormalGraph ι} {L : ι}
    (hL : builtinArrayLabel G L = true) {c : Clause (Ty ι)} (hc : c.carriesInvariant = true) {n W v}
    (hinv : builtinInvariant G (builtinValues G) c n W v) (ha : tagHolds .isArray v = true) :
    meaning G [L] n W v := by
  unfold builtinArrayLabel at hL
  cases hr : G.builtins with
  | none => rw [hr] at hL; cases hL
  | some r =>
    rw [hr] at hL
    simp only [Bool.and_eq_true] at hL
    obtain ⟨⟨⟨hfree, hunk⟩, hplain⟩, hrow⟩ := hL
    split at hrow
    · rename_i k S p P K hGL
      simp only [Bool.and_eq_true, beq_iff_eq] at hrow
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hS⟩ := hrow
      -- The tested value is a plain object owning the store key.
      obtain ⟨flds, oid, rfl, hst⟩ : ∃ flds oid, v = .objAt flds .absent oid ∧
          (flds.lookup CallArguments.arrayStoreField).isSome = true := by
        cases v with
        | objAt fs code oid =>
          cases code <;> simp [tagHolds] at ha
          exact ⟨fs, oid, rfl, by simpa [CallArguments.arrayStoreField] using ha⟩
        | _ => simp [tagHolds] at ha
      have hinv' := hinv
      unfold builtinInvariant at hinv'
      rw [hr] at hinv'
      simp only [hc, ite_true] at hinv'
      obtain ⟨hview, hkeys, -⟩ := hinv' flds oid rfl hst
      refine ⟨L, List.mem_singleton_self L, (unfold_plain hplain n W _).mpr
        ⟨.refs [] [] [(CallArguments.arrayStoreField, S), (CallArguments.protoField, r.proto)] [] []
          [⟨false, r.keys⟩], by rw [hGL]; simp, ?_, ?_⟩⟩
      · refine ⟨⟨⟨flds, oid, rfl, fun f T hm => by simp [ReferenceConjunctions.famsOf] at hm⟩, by simp,
          by simp [ReferenceConjunctions.famsOf]⟩,
          fun f T hm => ?_, by simpa [OptionalField.map] using optT_nil,
          MethodMembers.methodT_nil _ _ _, fun K hK => ?_⟩
        · simp only [ReferenceConjunctions.famsOf, List.map_cons, List.map_nil, List.mem_cons,
            Prod.mk.injEq, List.not_mem_nil, or_false] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · obtain ⟨flds', l, c', oid', he, hl, hw, hag⟩ := hview CallArguments.arrayStoreField
              (builtinStoreT (builtinValues G r.unknown)) (by simp)
            exact .inl (viewT_single ⟨flds', l, c', oid', he, hl, hw, fun j hj W' u hu =>
              storeOfValues_sound hS hunk (hag j hj W' u hu)⟩)
          · obtain ⟨flds', l, c', oid', he, hl, hw, hag⟩ := hview CallArguments.protoField (builtinValues G r.proto) (by simp)
            exact .inl (viewT_single ⟨flds', l, c', oid', he, hl, hw, fun j hj W' u hu =>
              (builtinsFree_meaning hfree j W' u).mpr (hag j hj W' u hu)⟩)
        · simp only [List.mem_singleton] at hK
          subst hK
          exact hkeys
      · exact (builtinInvariant_carriesInvariant hc rfl).mp hinv
    · cases hrow

/-- Where `Array.isArray` holds, every label of the tested type is kept in
`B`, or is a clause row each clause of which is of no array or a record's,
whose members that are arrays `B`'s builtins array label holds. -/
def arraySlice [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) : Bool :=
  B.any (builtinArrayLabel G) &&
    (tagSlice G A .isArray true).all fun a =>
      B.contains a || (G.plain a && (G a).all fun c => tagClause .isArray c == some false || c.carriesInvariant)

theorem arraySlice_sound [DecidableEq ι] {G : NormalGraph ι} {A B : Ty ι}
    (h : arraySlice G A B = true) {n W v} (hv : meaning G A n W v)
    (ha : tagHolds .isArray v = true) : meaning G B n W v := by
  simp only [arraySlice, Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨L, hLB, hL⟩, hall⟩ := h
  obtain ⟨a, haS, hva⟩ := tagSlice_sound (tag := .isArray) (q := true) hv (Or.inl ha)
  rcases Bool.or_eq_true_iff.mp (hall a haS) with hB | hrow
  · exact ⟨a, List.contains_iff_mem.mp hB, hva⟩
  · simp only [Bool.and_eq_true, List.all_eq_true] at hrow
    obtain ⟨c, hc, hcv, hinv⟩ := (unfold_plain hrow.1 n W v).mp hva
    rcases Bool.or_eq_true_iff.mp (hrow.2 c hc) with hno | hrec
    · have := tagClause_sound (beq_iff_eq.mp hno) hcv
      rw [ha] at this; cases this
    · obtain ⟨l, hl, hvl⟩ := builtinArray_of_record hL hrec hinv ha
      cases List.mem_singleton.mp hl
      exact ⟨L, hLB, hvl⟩

/-- Sufficient implementations of ObservedSub. Whole-label filtering is only
an algorithm for the tag case, not the meaning of refinement. -/
@[nospecialize] def checkObservedSubResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (A B : Ty ι) (o : Observation) (p : PositiveCertificates.SubtypeChoices ι) : CheckResult ι Unit :=
  match o with
  | .boolean q => CheckResult.ofBool (booleanMember G B q)
  | .tag t q =>
      (ProgramCertificates.checkSubtypeUsing G images (tagSlice G A t q) B p).orElse fun _ =>
      CheckResult.ofBool (tagMember G B t q || presentKey t q (promotes G (tagSlice G A t q) B) ||
        (t == .isArray && q && arraySlice G A B) || meetSlice G A B t q)

@[nospecialize] def checkObservedSubUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (A B : Ty ι) (o : Observation) (p : PositiveCertificates.SubtypeChoices ι) : Bool :=
  (checkObservedSubResult G images A B o p).accepted

theorem checkObservedSubResult_accepted [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (A B : Ty ι) (o : Observation) (p : PositiveCertificates.SubtypeChoices ι) :
    (checkObservedSubResult G images A B o p).accepted = checkObservedSubUsing G images A B o p := rfl

theorem checkObservedSubUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (A B : Ty ι) (o : Observation) (p : PositiveCertificates.SubtypeChoices ι) :
    checkObservedSubUsing G images A B o p =
  match o with
  | .boolean q => booleanMember G B q
  | .tag t q => PositiveCertificates.checkUsing G images (tagSlice G A t q) B p || tagMember G B t q ||
      presentKey t q (promotes G (tagSlice G A t q) B) ||
      (t == .isArray && q && arraySlice G A B) || meetSlice G A B t q := by
  cases o <;> simp only [checkObservedSubUsing, checkObservedSubResult, CheckResult.accepted_ofBool,
    CheckResult.accepted_orElse, ProgramCertificates.checkSubtypeUsing_accepted, Bool.or_assoc]

theorem checkObservedSub_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {A B o p} (hc : checkObservedSubUsing G images A B o p = true) : ObservedSub G A B o := by
  intro n W v hv ho
  cases o with
  | boolean q =>
    simp only [checkObservedSubUsing_eq] at hc
    have hb := hc
    change v = (if q then .tru else .fls) at ho
    rw [ho]
    exact booleanMember_sound hb n W
  | tag t q =>
    simp only [checkObservedSubUsing_eq, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with (((hc | hm) | hk) | ⟨⟨ht, hq⟩, hs⟩) | hmeet
    · exact PositiveCertificates.acceptedUsing hc n W v (tagSlice_sound hv ho)
    · exact tagMember_sound hm (meaning_value hv).1 (meaning_value hv).2 (ho.resolve_right (by
        cases t <;> cases q <;> simp [tagMember, familyMember] at hm <;> simp [protoFree]))
    · obtain ⟨k, hp, hkey⟩ := presentKey_sound hk ho
      exact promotes_sound hp (tagSlice_sound hv ho) hkey
    · have ht := beq_iff_eq.mp ht
      subst ht; subst hq
      exact arraySlice_sound hs hv (ho.resolve_right (by simp [protoFree]))
    · exact meetSlice_sound hmeet hv ho

/-- The field refinements a tag observation admits for other slots: each
object a current read link says the tested value was read from, and the
field it was read through. -/
@[nospecialize] def fieldRefinementsResult [DecidableEq ι] (o : Observation) (fields : List (Nat × PropKey))
    (A B : Ty ι) (j : Nat) (G : NormalGraph ι) (images : InstanceImageCheck G)
    (p : PositiveCertificates.SubtypeChoices ι) : CheckResult ι Unit :=
  match o with
  | .tag t q => CheckResult.any fields fun (k, f) =>
      (CheckResult.ofBool (k == j)).bind fun _ =>
        ProgramCertificates.checkSubtypeUsing G images (fieldSlice G A f t q) B p
  | .boolean _ => failure

@[nospecialize] def fieldRefinements [DecidableEq ι] (o : Observation) (fields : List (Nat × PropKey)) (A B : Ty ι)
    (j : Nat) (G : NormalGraph ι) (images : InstanceImageCheck G) (p : PositiveCertificates.SubtypeChoices ι) : Bool :=
  (fieldRefinementsResult o fields A B j G images p).accepted

theorem fieldRefinements_eq [DecidableEq ι] (o : Observation) (fields : List (Nat × PropKey)) (A B : Ty ι)
    (j : Nat) (G : NormalGraph ι) (images : InstanceImageCheck G) (p : PositiveCertificates.SubtypeChoices ι) :
    fieldRefinements o fields A B j G images p =
  match o with
  | .tag t q => fields.any fun (k, f) => k == j &&
      PositiveCertificates.checkUsing G images (fieldSlice G A f t q) B p
  | .boolean _ => false := by
  cases o <;> simp only [fieldRefinements, fieldRefinementsResult, CheckResult.accepted_any,
    CheckResult.accepted_bind, CheckResult.accepted_ofBool, ProgramCertificates.checkSubtypeUsing_accepted]
  rfl

/-- An object a cell fact is about keeps the labels its field's observed
contents admit (`factSlice`). -/
@[nospecialize] def cellRefinementsResult [DecidableEq ι] (cells : HeapFacts.Facts) (A B : Ty ι) (j : Nat)
    (G : NormalGraph ι) (images : InstanceImageCheck G) (p : PositiveCertificates.SubtypeChoices ι) :
    CheckResult ι Unit :=
  CheckResult.any cells fun fct =>
    (CheckResult.ofBool (fct.slot == j)).bind fun _ =>
      ProgramCertificates.checkSubtypeUsing G images (factSlice G A fct.field fct.contents) B p

@[nospecialize] def cellRefinements [DecidableEq ι] (cells : HeapFacts.Facts) (A B : Ty ι) (j : Nat)
    (G : NormalGraph ι) (images : InstanceImageCheck G) (p : PositiveCertificates.SubtypeChoices ι) : Bool :=
  (cellRefinementsResult cells A B j G images p).accepted

theorem cellRefinements_eq [DecidableEq ι] (cells : HeapFacts.Facts) (A B : Ty ι) (j : Nat)
    (G : NormalGraph ι) (images : InstanceImageCheck G) (p : PositiveCertificates.SubtypeChoices ι) :
    cellRefinements cells A B j G images p =
      cells.any fun fct => fct.slot == j &&
        PositiveCertificates.checkUsing G images (factSlice G A fct.field fct.contents) B p := by
  simp only [cellRefinements, cellRefinementsResult, CheckResult.accepted_any,
    CheckResult.accepted_bind, CheckResult.accepted_ofBool, ProgramCertificates.checkSubtypeUsing_accepted]

/-- Whether an observation rules out `undefined`: a Boolean is not it, and a
tag answers it one way. -/
def excludesUndef : Observation → Bool
  | .boolean _ => true
  | .tag t q => tagHolds t .undef != q

theorem excludesUndef_sound {o : Observation} {v : Tm} (h : excludesUndef o = true)
    (ho : o.holds v) : v ≠ .undef := by
  rintro rfl
  cases o with
  | boolean q => cases q <;> simp [Observation.holds] at ho
  | tag t q =>
    simp only [excludesUndef, bne_iff_ne, ne_eq] at h
    rcases ho with ho | ho
    · exact h ho
    · simp [protoFree] at ho

/-- The promotions an observation admits for other slots: an object the
tested value was read from through an optional key (`optionals`), where the
observation rules out `undefined`, which is what a read of the key gives where
the object lacks it. The object then has the key, from then on. -/
def optionalRefinements [DecidableEq ι] (o : Observation) (optionals : List (Nat × PropKey)) (A B : Ty ι)
    (j : Nat) (G : NormalGraph ι) : Bool :=
  excludesUndef o && optionals.any fun (k, f) => k == j && promotes G A B f

/-- An observation no value of the tested type makes: a tag answer every
label contradicts, or a Boolean the type does not hold. The edge is then
never taken, and constrains nothing. -/
def impossible [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) : Observation → Bool
  | .tag t q => (tagSlice G A t q).isEmpty
  | .boolean q => G.plainTy A && (expand G A).all fun c =>
      c == .boolLit (!q) || tagClause .isBool c == some false

theorem impossible_sound [DecidableEq ι] {G : NormalGraph ι} {A o n W v}
    (h : impossible G A o = true) (hv : meaning G A n W v) (ho : o.holds v) : False := by
  cases o with
  | tag t q =>
    simp only [impossible, List.isEmpty_iff] at h
    obtain ⟨a, ha, _⟩ := tagSlice_sound hv ho
    rw [h] at ha
    cases ha
  | boolean q =>
    simp only [impossible, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨c, hc, hcv, -⟩ := (expand_sem G A h.1 n W v).mp hv
    change v = (if q then .tru else .fls) at ho
    subst ho
    rcases h.2 c hc with rfl | hb
    · cases q <;> simp [semWithArgs] at hcv
    · have := tagClause_sound hb hcv
      cases q <;> simp [tagHolds] at this

/-- One observed edge slot, with alternatives justified by its source facts. -/
@[nospecialize] def checkObservedSlotResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (source target : Option (Ty ι)) (evidence : Option (PositiveCertificates.SubtypeChoices ι))
    (sourceSlot tested : Nat) (o : Observation) (fields optionals : List (Nat × PropKey))
    (cells : HeapFacts.Facts := []) : CheckResult ι Unit :=
  match source, target, evidence with
  | some A, some B, some p =>
      if sourceSlot == tested then checkObservedSubResult G images A B o p
      else (((ProgramCertificates.checkSubtypeUsing G images A B p).orElse fun _ =>
        fieldRefinementsResult o (fields ++ optionals) A B sourceSlot G images p).orElse fun _ =>
        CheckResult.ofBool (optionalRefinements o optionals A B sourceSlot G)).orElse fun _ =>
        cellRefinementsResult cells A B sourceSlot G images p
  | _, _, _ => failure

theorem checkObservedSlotResult_accepted [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (source target : Option (Ty ι)) (evidence : Option (PositiveCertificates.SubtypeChoices ι))
    (sourceSlot tested : Nat) (o : Observation) (fields optionals : List (Nat × PropKey))
    (cells : HeapFacts.Facts) :
    (checkObservedSlotResult G images source target evidence sourceSlot tested o fields optionals cells).accepted =
      match source, target, evidence with
      | some A, some B, some p =>
          if sourceSlot == tested then checkObservedSubUsing G images A B o p
          else PositiveCertificates.checkUsing G images A B p ||
            fieldRefinements o (fields ++ optionals) A B sourceSlot G images p ||
            optionalRefinements o optionals A B sourceSlot G ||
            cellRefinements cells A B sourceSlot G images p
      | _, _, _ => false := by
  cases source <;> cases target <;> cases evidence <;>
    simp only [checkObservedSlotResult]
  all_goals first
    | rfl
    | (split <;> (try simp only [CheckResult.accepted_orElse, CheckResult.accepted_ofBool,
        ProgramCertificates.checkSubtypeUsing_accepted]) <;> rfl)

/-- One mapped-edge checker for all supported observations. Other slots use
ordinary subtype evidence, or, for an object the tested value was read from
(`fields`), subtype evidence from its field slice. The tested slot must
exist, even if forgotten. -/
@[nospecialize] def checkObservedResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (tested : Nat) (o : Observation) (mapping : Mapping) (ps : EdgeEvidence ι)
    (fields : List (Nat × PropKey) := []) (optionals : List (Nat × PropKey) := [])
    (cells : HeapFacts.Facts := []) : CheckResult ι Unit :=
  (CheckResult.ofBool Γ[tested]?.isSome).bind fun _ =>
  (CheckResult.ofBool ((Γ[tested]?).any (impossible G · o))).orElse fun _ =>
  (CheckResult.ofBool ((match mapping with | none => true | some slots => slots.length == Δ.length) &&
    ps.length == Δ.length)).bind fun _ =>
  CheckResult.all (List.range Δ.length) fun j =>
    checkObservedSlotResult G images Γ[slot mapping j]? Δ[j]? ps[j]? (slot mapping j) tested o fields optionals cells

@[nospecialize] def checkObservedUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (tested : Nat) (o : Observation) (mapping : Mapping) (ps : EdgeEvidence ι)
    (fields : List (Nat × PropKey) := []) (optionals : List (Nat × PropKey) := [])
    (cells : HeapFacts.Facts := []) : Bool :=
  (checkObservedResult G images Γ Δ tested o mapping ps fields optionals cells).accepted

theorem checkObservedUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (tested : Nat) (o : Observation) (mapping : Mapping) (ps : EdgeEvidence ι)
    (fields optionals : List (Nat × PropKey)) (cells : HeapFacts.Facts) :
    checkObservedUsing G images Γ Δ tested o mapping ps fields optionals cells =
  (Γ[tested]?.isSome &&
  ((Γ[tested]?).any (impossible G · o) ||
  (match mapping with | none => true | some slots => slots.length == Δ.length) &&
  ps.length == Δ.length && (List.range Δ.length).all (fun j =>
    match Γ[slot mapping j]?, Δ[j]?, ps[j]? with
    | some A, some B, some p =>
      if slot mapping j == tested then checkObservedSubUsing G images A B o p
      else PositiveCertificates.checkUsing G images A B p ||
        fieldRefinements o (fields ++ optionals) A B (slot mapping j) G images p ||
        optionalRefinements o optionals A B (slot mapping j) G ||
        cellRefinements cells A B (slot mapping j) G images p
    | _, _, _ => false))) := by
  simp only [checkObservedUsing, checkObservedResult, CheckResult.accepted_bind,
    CheckResult.accepted_orElse, CheckResult.accepted_ofBool, CheckResult.accepted_all,
    checkObservedSlotResult_accepted, Bool.and_assoc]

def ObservedCovers [DecidableEq ι] (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (tested : Nat) (o : Observation) (mapping : Mapping) (fields : List (Nat × PropKey) := [])
    (optionals : List (Nat × PropKey) := []) (cells : HeapFacts.Facts := []) : Prop :=
  (∃ A, Γ[tested]? = some A ∧ ∀ n W v, meaning G A n W v → o.holds v → False) ∨
  ∀ j B, Δ[j]? = some B → ∃ A, Γ[slot mapping j]? = some A ∧
    (if slot mapping j = tested then ObservedSub G A B o
     else FamLe (meaning G A) (meaning G B) ∨
       (∃ t q f, o = .tag t q ∧ (slot mapping j, f) ∈ fields ++ optionals ∧
         FamLe (meaning G (fieldSlice G A f t q)) (meaning G B)) ∨
       (∃ f, (slot mapping j, f) ∈ optionals ∧ excludesUndef o = true ∧ promotes G A B f = true) ∨
       ∃ fct ∈ cells, fct.slot = slot mapping j ∧
         FamLe (meaning G (factSlice G A fct.field fct.contents)) (meaning G B))

theorem checkObserved_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {Γ Δ i o mapping ps fields optionals cells}
    (h : checkObservedUsing G images Γ Δ i o mapping ps fields optionals cells = true) :
    ObservedCovers G Γ Δ i o mapping fields optionals cells := by
  simp only [checkObservedUsing_eq, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at h
  rcases h.2 with hdead | h
  · left
    cases ht : Γ[i]? with
    | none => simp [ht] at hdead
    | some A =>
      rw [ht] at hdead
      exact ⟨A, rfl, fun n W v hv ho => impossible_sound (by simpa using hdead) hv ho⟩
  right
  intro j B hj
  have hc := h.2 j (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hj).1)
  rw [hj] at hc
  cases ha : Γ[slot mapping j]? with
  | none => simp [ha] at hc
  | some A =>
    cases hp : ps[j]? with
    | none => simp [ha,hp] at hc
    | some p =>
      refine ⟨A,rfl,?_⟩
      simp only [ha,hp] at hc
      by_cases he : slot mapping j = i
      · simp only [beq_iff_eq,he,↓reduceIte] at hc
        simp only [he,↓reduceIte]
        exact checkObservedSub_sound hc
      · simp only [beq_iff_eq,he,↓reduceIte,Bool.or_eq_true] at hc
        simp only [he,↓reduceIte]
        rcases hc with ((hc | hc) | hc) | hc
        · exact .inl (PositiveCertificates.acceptedUsing hc)
        · right; left
          cases o with
          | boolean _ => simp [fieldRefinements_eq] at hc
          | tag t q =>
            simp only [fieldRefinements_eq, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨⟨k, f⟩, hk, rfl, hck⟩ := hc
            exact ⟨t, q, f, rfl, hk, PositiveCertificates.acceptedUsing hck⟩
        · right; right; left
          simp only [optionalRefinements, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨hx, ⟨k, f⟩, hk, rfl, hp⟩ := hc
          exact ⟨f, hk, hx, hp⟩
        · right; right; right
          simp only [cellRefinements_eq, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨fct, hm, hslot, hck⟩ := hc
          exact ⟨fct, hm, hslot, PositiveCertificates.acceptedUsing hck⟩

/-- A branch edge's environment, one level above the one it is used at: a
field slice needs the heap's contents at the field, which the world types one
level down. -/
theorem ObservedCovers.env [DecidableEq ι] {G : NormalGraph ι} {Γ Δ i o mapping fields optionals cells ρ n W h}
    (hc : ObservedCovers G Γ Δ i o mapping fields optionals cells) (he : EnvOk G Γ ρ (n+1) W)
    (ho : o.holds (ρ i)) (hh : HeapOk (n+1) W h)
    (hl : ∀ k f, (k, f) ∈ fields → ∃ flds c oid l, ρ k = .objAt flds c oid ∧ flds.lookup f = some l ∧
      h[l]? = some (ρ i))
    (hopt : ∀ k f, (k, f) ∈ optionals → ∃ flds c oid, ρ k = .objAt flds c oid ∧
      (flds.lookup f = none → ρ i = .undef) ∧ (∀ l, flds.lookup f = some l → h[l]? = some (ρ i)))
    (hcells : HeapFacts.Holds cells ρ h) :
    EnvOk G Δ (mapEnv mapping ρ) (n+1) W := by
  rcases hc with ⟨A, ha, himp⟩ | hc
  · exact (himp _ _ _ (he.2 _ A ha) ho).elim
  refine ⟨fun j => he.1 (slot mapping j), ?_⟩
  intro j B hj
  obtain ⟨A,ha,h⟩ := hc j B hj
  by_cases hij : slot mapping j = i
  · simp only [hij,↓reduceIte] at h
    change meaning G B (n+1) W (ρ (slot mapping j))
    rw [hij]
    exact h (n+1) W _ (by simpa [hij] using he.2 _ A ha) ho
  · simp only [hij,↓reduceIte] at h
    rcases h with h | ⟨t, q, f, rfl, hf, hs⟩ | ⟨f, hf, hx, hp⟩ | ⟨fct, hm, hslot, hs⟩
    · exact h (n+1) W _ (he.2 _ A ha)
    · rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨flds, c, oid, l, hv, hfl, hu⟩ := hl _ f hf
        exact hs (n+1) W _ (fieldSlice_sound (he.2 _ A ha) hh hv hfl hu ho)
      -- Read through a key the object may lack: where it has it, the read
      -- gave the field's value; where it lacks it, no label the slice drops
      -- is the object's.
      · obtain ⟨flds, c, oid, hv, _, hpresent⟩ := hopt _ f hf
        cases hfl : flds.lookup f with
        | none => exact hs (n+1) W _ (fieldSlice_absent (he.2 _ A ha) hv hfl)
        | some l => exact hs (n+1) W _ (fieldSlice_sound (he.2 _ A ha) hh hv hfl (hpresent l hfl) ho)
    · obtain ⟨flds, c, oid, hv, hab, _⟩ := hopt _ f hf
      cases hfl : flds.lookup f with
      | none => exact absurd (hab hfl) (excludesUndef_sound hx ho)
      | some l =>
        refine promotes_sound hp (he.2 _ A ha) fun flds' c' oid' he' hn => ?_
        have he'' : ρ (slot mapping j) = .objAt flds' c' oid' := he'
        rw [hv] at he''
        cases he''
        rw [hfl] at hn
        cases hn
    · obtain ⟨flds, c, oid, u, hv, hr, hatom⟩ := hcells fct hm
      rw [hslot] at hv
      exact hs (n+1) W _ (factSlice_sound (he.2 _ A ha) hh hv hr hatom)

end Verification.BranchRefinement
