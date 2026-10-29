import Verification.Programs.PointClaims
import Verification.Semantics.HeapFacts
-- Std.Data.HashMap.Lemmas reads a map built by insertion; without it the keyed restriction index has no proof.
import Std.Data.HashMap.Lemmas

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

/-- A tag set label the test answers element by element: the labels of the
elements it does not contradict, where the graph holds a label for each
(HOST-FAMILIES.md, "Tag sets"). -/
def setSplit (G : NormalGraph ι) (a : ι) (tag : Tag) (q : Bool) : Option (List ι) :=
  match G a with
  | [c] => if c.elements.length == 1 then none else
      (c.elements.filter fun e => tagClause tag e != some (!q)).mapM (elementLabel G)
  | _ => none

/-- Drop only labels whose every clause contradicts the observed tag, and
split a tag set into the labels of the elements the test leaves. A mixed
label is retained intact: this does not assume that labels have uniform shapes.
A parameter or scheme row has no clauses to contradict it, and is retained. -/
def tagSlice (G : NormalGraph ι) (A : Ty ι) (tag : Tag) (q : Bool) : Ty ι :=
  A.flatMap fun a =>
    if G.plain a && (expand G [a]).all (fun c => (tagClause tag c) == some (!q)) then []
    else (setSplit G a tag q).getD [a]

/-- A value of a label the split names is in one of the split's labels. -/
theorem setSplit_sound {G : NormalGraph ι} {a : ι} {tag q ls n W v}
    (hs : setSplit G a tag q = some ls) (hv : meaning G [a] n W v)
    (hq : tagHolds tag v = q ∨ protoFree tag v = false) : meaning G ls n W v := by
  unfold setSplit at hs
  split at hs
  · rename_i c hrow
    split at hs
    · cases hs
    · have hplain : G.plain a = true := NormalGraph.plain_of_clauses (c := c) (by simp [hrow])
      have hpt : G.plainTy [a] = true := by simp [NormalGraph.plainTy, hplain]
      obtain ⟨c', hc', hcv⟩ := (expand_sem G [a] hpt n W v).mp hv
      have hcc : c' = c := by
        simpa [expand, hpt, clausesOf, hrow] using hc'
      subst hcc
      obtain ⟨e, he, hev⟩ := rowSem_elements G _ _ _ hcv
      have hkeep : e ∈ c'.elements.filter fun e => tagClause tag e != some (!q) := by
        refine List.mem_filter.mpr ⟨he, ?_⟩
        cases ht : tagClause tag e with
        | none => rfl
        | some r =>
          by_cases hr : r = !q
          · subst hr
            have hans := tagClause_sound ht hev.1
            have hpf := tagClause_protoFree ht hev.1
            rcases hq with hq | hq
            · rw [hq] at hans; cases q <;> simp at hans
            · rw [hpf] at hq; cases hq
          · simp [hr]
      obtain ⟨l, hl, hel⟩ := mapM_mem hs e hkeep
      have hlr := elementLabel_sound hel
      have hlp : G.plain l = true :=
        NormalGraph.plain_of_clauses (c := e) (show e ∈ G l by rw [hlr]; exact List.mem_singleton_self e)
      have hlt : G.plainTy [l] = true := by simp [NormalGraph.plainTy, hlp]
      obtain ⟨u, hu, hmu⟩ := (expand_sem G [l] hlt n W v).mpr ⟨e, by simp [expand, hlt, clausesOf, hlr], hev⟩
      exact ⟨u, by simp at hu; subst hu; exact hl, hmu⟩
  · cases hs

theorem tagSlice_sound {G : NormalGraph ι} {A tag q n W v}
    (hv : meaning G A n W v) (hq : tagHolds tag v = q ∨ protoFree tag v = false) :
    meaning G (tagSlice G A tag q) n W v := by
  obtain ⟨a, ha, hv⟩ := hv
  cases h : (G.plain a && (expand G [a]).all fun c => (tagClause tag c) == some (!q)) with
  | true =>
    simp only [Bool.and_eq_true] at h
    have hop : Answers G [a] tag (!q) := by
      refine ⟨by simp [NormalGraph.plainTy, h.1], fun c hc => ?_⟩
      exact beq_iff_eq.mp (List.all_eq_true.mp h.2 c hc)
    have he := answers_weak hop (show meaning G [a] n W v from ⟨a, by simp, hv⟩) hq
    cases q <;> simp at he
  | false =>
    cases hs : setSplit G a tag q with
    | none => exact ⟨a, List.mem_flatMap.mpr ⟨a, ha, by simp [h, hs]⟩, hv⟩
    | some ls =>
      obtain ⟨l, hl, hlv⟩ := setSplit_sound hs ⟨a, by simp, hv⟩ hq
      exact ⟨l, List.mem_flatMap.mpr ⟨a, ha, by simp [h, hs, hl]⟩, hlv⟩

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
  | .refs a _ vs _ _ _ _ => (a ++ vs.filter (·.1 != lengthKey)).any fun p =>
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
      | .refs a _ vs _ _ _ _ => (f, K) ∈ a ++ vs.filter (·.1 != lengthKey)
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
      have hu' := field_value (c := .refs a' bs vs os ms ks _) (K := K) hp hcv hh hl hf hu
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

/-! ### Disjoint labels, and a fact filtered by a slot's type

A value of two types is in a label of each. Two clauses no value meets are
disjoint: their meet is empty (`meetLists`: two shapes, two literals, an owned
key a bound excludes), or both fix one field, as an invariant field or a
readonly view, at types whose clauses meet in none, since the field's one
location holds one value, of both types (`field_value`). A fact about a slot
keeps the fact's labels the slot's type does not exclude
(PROGRAM-TYPING.md, "Refinement by a fact"). -/

/-- The fields a record clause fixes: its invariant fields and its views,
the length view aside. -/
@[nospecialize] def fixedFields (c : Clause (Ty ι)) : List (PropKey × Ty ι) :=
  match c with
  | .refs a _ vs _ _ _ _ => a ++ vs.filter (·.1 != lengthKey)
  | _ => []

/-- No clause of `A` meets a clause of `B` consistently: `meetLists A B` is
empty, decided pair by pair and ending at the first consistent meet. -/
@[nospecialize] def meetsNone (A B : List (Clause α)) : Bool :=
  A.all fun a => B.all fun b => !(meet a b).any Clause.consistent

theorem meetsNone_iff {A B : List (Clause α)} : meetsNone A B = true ↔ meetLists A B = [] := by
  simp [meetsNone, meetLists, List.flatMap_eq_nil_iff, List.filter_eq_nil_iff]

/-- Two types of clause rows whose clauses meet in none, decided label by
label, ending at the first pair of labels with a consistent meet. -/
@[nospecialize] def typesDisjoint (G : NormalGraph ι) (K L : Ty ι) : Bool :=
  G.plainTy K && G.plainTy L && K.all fun k => L.all fun l => meetsNone (clausesOf G [k]) (clausesOf G [l])

theorem meetsNone_labels {G : NormalGraph ι} {K L : Ty ι} :
    (K.all fun k => L.all fun l => meetsNone (clausesOf G [k]) (clausesOf G [l])) =
      meetsNone (clausesOf G K) (clausesOf G L) := by
  apply Bool.eq_iff_iff.mpr
  simp only [meetsNone, clausesOf, List.all_eq_true, List.mem_flatMap, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  constructor
  · rintro h a ⟨k, hk, ha⟩ b ⟨l, hl, hb⟩
    exact h k hk l hl a ha b hb
  · intro h k hk l hl a ha b hb
    exact h a ⟨k, hk, ha⟩ b ⟨l, hl, hb⟩

/-- Two clauses no value meets. -/
@[nospecialize] def clausesDisjoint (G : NormalGraph ι) (c d : Clause (Ty ι)) : Bool :=
  meetsNone [c] [d] ||
    (fixedFields c).any fun p => (fixedFields d).any fun q => decide (p.1 = q.1) && typesDisjoint G p.2 q.2

/-- A label no value of `A` is in: each of its clauses is disjoint from each
clause of `A`. -/
@[nospecialize] def labelExcluded (G : NormalGraph ι) (A : Ty ι) (b : ι) : Bool :=
  G.plainTy A && G.plain b &&
    let ds := expand G [b]
    (expand G A).all fun c => ds.all fun d => clausesDisjoint G c d

/-- Two clauses of a label that `clausesDisjoint` does not find disjoint:
the label is excluded by no type it is a label of. -/
@[nospecialize] def selfOverlaps (G : NormalGraph ι) (b : ι) : Bool :=
  G.plain b &&
    let ds := expand G [b]
    ds.any fun c => ds.any fun d => !clausesDisjoint G c d

/-- A fact's type `B` filtered by a slot's type `A`: the labels of `B`
that `A` does not exclude, none where `A` excludes them all. A label of `A`
the graph's hint `overlapping` names is kept without comparing clauses: the
hint is each label's `selfOverlaps`, computed once, and then the filter is
the same (`factFilter_hint`). -/
@[nospecialize] def factFilter [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) : Ty ι :=
  B.filter fun b => (A.contains b && G.overlapping b) || !labelExcluded G A b

/-- A record clause's member, with a heap meeting the world, owns each field
the clause fixes at a location the heap holds. -/
theorem field_located {G : NormalGraph ι} {c : Clause (Ty ι)} {f : PropKey} {K : Ty ι} {n W h v}
    (hK : (f, K) ∈ fixedFields c)
    (hv : semWithArgs (excOf G) (meaning G) (argMeaning G) c (n+1) W v) (hh : HeapOk (n+1) W h) :
    ∃ flds code oid l u, v = .objAt flds code oid ∧ flds.lookup f = some l ∧ h[l]? = some u := by
  cases c with
  | refs a bs vs os ms ks =>
    simp only [fixedFields] at hK
    rcases List.mem_append.mp hK with hK | hK
    · obtain ⟨flds', oid', hv', hall⟩ := hv.1.1
      obtain ⟨l', c', hl', hc', -⟩ := hall f (meaning G K) (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩)
      obtain ⟨u, hu, -⟩ := hh.2 l' c' hc'
      exact ⟨flds', _, oid', l', u, hv', hl', hu⟩
    · obtain ⟨hK, hKl⟩ := List.mem_filter.mp hK
      obtain ⟨flds', l', c', oid', hv', hl', hc', -⟩ :=
        viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩) (by simpa using hKl) hv.2.1
      obtain ⟨u, hu, -⟩ := hh.2 l' c' hc'
      exact ⟨flds', _, oid', l', u, hv', hl', hu⟩
  | _ => simp [fixedFields] at hK

theorem typesDisjoint_sound {G : NormalGraph ι} {K L : Ty ι} {n W u}
    (hd : typesDisjoint G K L = true) (hK : meaning G K n W u) (hL : meaning G L n W u) : False := by
  simp only [typesDisjoint, Bool.and_eq_true] at hd
  have hn : meetLists (expand G K) (expand G L) = [] := by
    rw [← meetsNone_iff, expand_of_plain hd.1.1, expand_of_plain hd.1.2, ← meetsNone_labels]
    exact hd.2
  have hm := (meetLists_row G _ _ _ (expand G K) (expand G L) n W u).mpr
    ⟨(expand_sem G K hd.1.1 n W u).mp hK, (expand_sem G L hd.1.2 n W u).mp hL⟩
  rw [hn] at hm
  obtain ⟨_, hm, _⟩ := hm
  cases hm

theorem clausesDisjoint_sound {G : NormalGraph ι} {c d : Clause (Ty ι)} {n W h v}
    (hd : clausesDisjoint G c d = true) (hc : clauseSem G c (n+1) W v) (hd' : clauseSem G d (n+1) W v)
    (hh : HeapOk (n+1) W h) : False := by
  simp only [clausesDisjoint, Bool.or_eq_true, meetsNone_iff, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hd
  rcases hd with hm | ⟨p, hp, q, hq, hpq, hdis⟩
  · have hs := (meetLists_row G _ _ _ [c] [d] (n+1) W v).mpr
      ⟨⟨c, List.mem_singleton_self c, hc⟩, ⟨d, List.mem_singleton_self d, hd'⟩⟩
    rw [hm] at hs
    obtain ⟨_, hs, _⟩ := hs
    cases hs
  · obtain ⟨f, K⟩ := p
    obtain ⟨g, L⟩ := q
    simp only at hpq hdis
    subst hpq
    obtain ⟨flds, code, oid, l, u, hl, hf, hu⟩ := field_located hp hc.1 hh
    have hK := field_value (c := c) (f := f) (K := K) (by cases c <;> first | exact hp | simp [fixedFields] at hp) hc.1 hh hl hf hu
    have hL := field_value (c := d) (f := f) (K := L) (by cases d <;> first | exact hq | simp [fixedFields] at hq) hd'.1 hh hl hf hu
    exact typesDisjoint_sound hdis hK hL

theorem labelExcluded_sound {G : NormalGraph ι} {A : Ty ι} {b : ι} {n W h v}
    (hx : labelExcluded G A b = true) (hA : meaning G A (n+1) W v) (hb : meaning G [b] (n+1) W v)
    (hh : HeapOk (n+1) W h) : False := by
  simp only [labelExcluded, Bool.and_eq_true, List.all_eq_true] at hx
  obtain ⟨c, hc, hcv⟩ := (expand_sem G A hx.1.1 _ W v).mp hA
  obtain ⟨d, hd, hdv⟩ := (expand_sem G [b] (by simp [NormalGraph.plainTy, hx.1.2]) _ W v).mp hb
  exact clausesDisjoint_sound (hx.2 c hc d hd) hcv hdv hh

/-- A value of both types is of the fact's type filtered by the slot's. -/
theorem factFilter_sound [DecidableEq ι] {G : NormalGraph ι} {A B : Ty ι} {n W h v}
    (hA : meaning G A (n+1) W v) (hB : meaning G B (n+1) W v) (hh : HeapOk (n+1) W h) :
    meaning G (factFilter G A B) (n+1) W v := by
  obtain ⟨b, hb, hv⟩ := hB
  refine ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, hv⟩
  cases hx : labelExcluded G A b
  · simp
  · exact (labelExcluded_sound hx hA ⟨b, by simp, hv⟩ hh).elim

/-- A label of `A` whose clauses overlap is excluded by no type it is a
label of. -/
theorem labelExcluded_of_selfOverlaps [DecidableEq ι] {G : NormalGraph ι} {A : Ty ι} {b : ι}
    (ho : selfOverlaps G b = true) (hb : A.contains b = true) : labelExcluded G A b = false := by
  simp only [selfOverlaps, Bool.and_eq_true, List.any_eq_true, Bool.not_eq_true'] at ho
  obtain ⟨hp, c, hc, d, hd, hcd⟩ := ho
  cases hx : labelExcluded G A b
  · rfl
  · simp only [labelExcluded, Bool.and_eq_true, List.all_eq_true] at hx
    have hcA : c ∈ expand G A := by
      have hbA : b ∈ A := by simpa using hb
      rw [expand_of_plain hx.1.1, clausesOf, List.mem_flatMap]
      rw [expand_of_plain (by simp [NormalGraph.plainTy, hp]), clausesOf, List.mem_flatMap] at hc
      obtain ⟨b', hb', hc'⟩ := hc
      simp only [List.mem_singleton] at hb'
      exact ⟨b, hbA, hb' ▸ hc'⟩
    rw [hx.2 c hcA d hd] at hcd
    cases hcd

/-- Where the graph's hint names only labels whose clauses overlap, the
filter keeps exactly the labels `A` does not exclude. -/
theorem factFilter_hint [DecidableEq ι] {G : NormalGraph ι} (hint : ∀ b, G.overlapping b = true → selfOverlaps G b = true)
    (A B : Ty ι) : factFilter G A B = B.filter fun b => !labelExcluded G A b := by
  unfold factFilter
  congr 1
  funext b
  cases ho : G.overlapping b
  · simp
  · cases hb : A.contains b
    · simp
    · simp [labelExcluded_of_selfOverlaps (hint b ho) hb]

/-! ### What a membership test's `false` answer removes

Where a membership test of the tags `ts` answered `false`, each tag's test
answered `false` of the tested value, so the value is of no clause each of
whose elements one of the tags answers `true` of (PROGRAM-TYPING.md, "A
membership test", member-split). -/

/-- Each element of a clause, a tag set's literals or the clause itself,
answers `true` to one of the tags. -/
def coveredBy (ts : List Tag) (c : Clause α) : Bool :=
  c.elements.all fun e => ts.any fun t => tagClause t e == some true

/-- No value of a covered clause is one every tag answers `false` of. -/
theorem coveredBy_sound {Ξ : Fam} {S : α → Fam} {P : α → ArgFam} {ts : List Tag} {c : Clause α} {n W v}
    (hc : coveredBy ts c = true) (hv : semWithArgs Ξ S P c n W v)
    (hno : ∀ t ∈ ts, tagHolds t v = false ∨ protoFree t v = false) : False := by
  obtain ⟨e, he, hev⟩ := (elements_sem Ξ S P c n W v).mpr hv
  obtain ⟨t, ht, hte⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc e he)
  have hq : tagClause t e = some true := beq_iff_eq.mp hte
  rcases hno t ht with h | h
  · rw [tagClause_sound hq hev] at h; cases h
  · rw [tagClause_protoFree hq hev] at h; cases h

/-- The labels of `A` a value may still have once every tag of `ts` answered
`false` of it: a label all of whose clauses are covered is dropped. -/
def uncovered (G : NormalGraph ι) (A : Ty ι) (ts : List Tag) : Ty ι :=
  A.filter fun a => !(G.plain a && (expand G [a]).all (coveredBy ts))

theorem uncovered_sound {G : NormalGraph ι} {A : Ty ι} {ts n W v} (hv : meaning G A n W v)
    (hno : ∀ t ∈ ts, tagHolds t v = false ∨ protoFree t v = false) :
    meaning G (uncovered G A ts) n W v := by
  obtain ⟨a, ha, hva⟩ := hv
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hva⟩
  cases hd : (G.plain a && (expand G [a]).all (coveredBy ts)) with
  | false => rfl
  | true =>
    exfalso
    simp only [Bool.and_eq_true, List.all_eq_true] at hd
    have hm : meaning G [a] n W v := ⟨a, by simp, hva⟩
    rw [expand_sem G [a] (by simp [NormalGraph.plainTy, hd.1])] at hm
    obtain ⟨c, hc, hcv, -⟩ := hm
    exact coveredBy_sound (hd.2 c hc) hcv hno

/-- Whether a record clause fixes the field `f` at a type each clause of
which `ts` covers: an invariant field or a readonly view. -/
def fieldCovered (G : NormalGraph ι) (c : Clause (Ty ι)) (f : PropKey) (ts : List Tag) : Bool :=
  match c with
  | .refs a _ vs _ _ _ _ => (a ++ vs.filter (·.1 != lengthKey)).any fun p =>
      decide (p.1 = f) && G.plainTy p.2 && (expand G p.2).all (coveredBy ts)
  | _ => false

/-- A clause whose value is one value at every level and world: a literal. -/
def literalClause : Clause α → Bool
  | .numLit _ | .strLit _ => true
  | _ => false

theorem literal_sem {Ξ : Fam} {X : α → Fam} {P : α → ArgFam} {e : Clause α} (he : literalClause e = true)
    {n W v m U} (hv : semWithArgs Ξ X P e n W v) : semWithArgs Ξ X P e m U v := by
  cases e <;> simp_all [literalClause, semWithArgs]

/-- `c'` is the record clause `c` with its views of the stable key `f` at
another type, each element of each clause of `c`'s type at `f` covered by
`ts` or a literal clause of the other (member-split). -/
def restricts [DecidableEq ι] (G : NormalGraph ι) (c c' : Clause (Ty ι)) (f : PropKey) (ts : List Tag) : Bool :=
  match c, c' with
  | .refs a bs vs os ms ks st, .refs a' bs' vs' os' ms' ks' st' =>
    decide (a = a' ∧ bs = bs' ∧ os = os' ∧ ms = ms' ∧ ks = ks' ∧ st = st') && st.contains f &&
      f != lengthKey && vs.length == vs'.length &&
      (vs.zip vs').all fun (p, p') => p.1 == p'.1 && (p.2 == p'.2 || (p.1 == f && G.plainTy p.2 &&
        G.plainTy p'.2 && (expand G p.2).all fun d => d.elements.all fun e =>
          ts.any (fun t => tagClause t e == some true) || (literalClause e && (expand G p'.2).contains e)))
  | _, _ => false

theorem exists_zip_left {xs : List α} {ys : List β} (hl : xs.length = ys.length) {y : β} (hy : y ∈ ys) :
    ∃ x, (x, y) ∈ xs.zip ys := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hy
  have hk' : k < xs.length := hl ▸ hk
  exact ⟨xs[k], List.mem_iff_getElem.mpr ⟨k, by simp [hl, hk], by simp⟩⟩

/-- A value of a record clause whose stable key `f` holds a value no tag of
`ts` answers `true` of is a value of the clause `restricts` reads it at: the
key's location holds that one value at every level and world, so the view
at the other type holds of every value its contract admits. -/
theorem restricts_sound [DecidableEq ι] {G : NormalGraph ι} {c c' : Clause (Ty ι)} {f : PropKey} {ts : List Tag}
    {n W h v flds code oid l u}
    (hr : restricts G c c' f ts = true) (hv : clauseSem G c (n+1) W v) (hh : HeapOk (n+1) W h)
    (hl : v = .objAt flds code oid) (hf : flds.lookup f = some l) (hu : h[l]? = some u)
    (hno : ∀ t ∈ ts, tagHolds t u = false ∨ protoFree t u = false) : clauseSem G c' (n+1) W v := by
  cases c with
  | refs a bs vs os ms ks st =>
    cases c' with
    | refs a' bs' vs' os' ms' ks' st' =>
      simp only [restricts, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem,
        bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true] at hr
      obtain ⟨⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, hst⟩, hlen⟩, hlen'⟩, hall⟩ := hr
      obtain ⟨⟨hrefs, hviews, hopt, hmeth, hkeys, hstable⟩, hinv⟩ := hv
      refine ⟨⟨hrefs, ?_, hopt, hmeth, hkeys, hstable⟩, by simpa [builtinInvariant, Clause.carriesInvariant] using hinv⟩
      -- The stable location at `f`: the tested value is its one value.
      obtain ⟨sflds, soid, hsv, hsa⟩ := stableKeysT_at hstable hst
      have heq : flds = sflds ∧ code = .absent := by rw [hl] at hsv; cases hsv; exact ⟨rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨sc, value, hsc, hstab⟩ := hsa.present hf
      have hvalue : u = value := by
        have := HeapOk.stable_value hh (Nat.succ_pos n) hsc hstab
        rw [hu] at this; exact Option.some.inj this
      subst hvalue
      intro g T hm
      obtain ⟨i', hi', rfl⟩ := ReferenceConjunctions.mem_famsOf.mp hm
      obtain ⟨⟨g0, i⟩, hz⟩ := exists_zip_left (by simpa using hlen') hi'
      have hpair := hall _ hz
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hpair
      obtain ⟨rfl, hsame | ⟨⟨⟨⟨rfl, hK⟩, hK'⟩, helems⟩⟩⟩ := hpair
      · subst hsame
        exact hviews g0 _ (ReferenceConjunctions.mem_famsOf.mpr ⟨i, (List.of_mem_zip hz).1, rfl⟩)
      · -- The original view of `f`, at the stable location.
        obtain ⟨vflds, vl, vc, void, hvv, hvl, hvc, himp⟩ :=
          viewsT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨i, (List.of_mem_zip hz).1, rfl⟩) hlen hviews
        rw [hl] at hvv
        cases hvv
        rw [hf] at hvl
        cases hvl
        rw [hsc] at hvc
        cases hvc
        refine .inl (viewT_single ⟨flds, l, sc, oid, hl ▸ rfl, hf, hsc, ?_⟩)
        intro j hj U w hw
        have hw' := hstab j hj U w hw
        subst hw'
        -- The value is of the original type at level zero, in one element.
        obtain ⟨u0, hu0, hm0⟩ := hh.2 l sc hsc
        rw [hu] at hu0
        cases hu0
        have hk := himp 0 (Nat.succ_pos n) _ _ (hm0 0 (Nat.succ_pos n))
        rw [expand_sem G i hK] at hk
        obtain ⟨d, hd, hdv, -⟩ := hk
        obtain ⟨e, he, hev⟩ := (elements_sem _ _ _ d _ _ _).mpr hdv
        have hcase := List.all_eq_true.mp (List.all_eq_true.mp helems d hd) e he
        simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, beq_iff_eq,
          List.contains_iff_mem] at hcase
        rcases hcase with ⟨t, ht, hte⟩ | ⟨hlit, hmem⟩
        · rcases hno t ht with h' | h'
          · rw [tagClause_sound hte hev] at h'; cases h'
          · rw [tagClause_protoFree hte hev] at h'; cases h'
        · rw [expand_sem G i' hK']
          refine ⟨e, hmem, literal_sem hlit hev, ?_⟩
          exact builtinInvariant_of_withoutInvariant (by cases e <;> simp_all [literalClause, Clause.carriesInvariant]) _ _ _
    | _ => simp [restricts] at hr
  | _ => cases c' <;> simp [restricts] at hr

/-- A label of `candidates` the one record clause of `a` restricts to the
rest of its stable key `f`'s type (`restricts`). -/
def restriction [DecidableEq ι] (G : NormalGraph ι) (a : ι) (f : PropKey) (ts : List Tag) (candidates : Ty ι) : Option ι :=
  match expand G [a] with
  | [c] => candidates.find? fun b => b != a && match expand G [b] with
    | [c'] => restricts G c c' f ts
    | _ => false
  | _ => none

theorem restriction_sound [DecidableEq ι] {G : NormalGraph ι} {a b : ι} {f : PropKey} {ts : List Tag} {candidates : Ty ι}
    {n W h v flds code oid l u}
    (hb : restriction G a f ts candidates = some b) (hv : meaning G [a] (n+1) W v) (hh : HeapOk (n+1) W h)
    (hl : v = .objAt flds code oid) (hf : flds.lookup f = some l) (hu : h[l]? = some u)
    (hno : ∀ t ∈ ts, tagHolds t u = false ∨ protoFree t u = false) : meaning G [b] (n+1) W v := by
  unfold restriction at hb
  split at hb
  · rename_i c hx
    have hp := List.find?_some hb
    simp only [Bool.and_eq_true] at hp
    obtain ⟨-, hfound⟩ := hp
    split at hfound
    · rename_i c' hb'
      have hp := plain_of_mem_expand (G := G) (S := [a]) (c := c) (by simp [hx])
      rw [expand_sem G [a] hp, hx] at hv
      obtain ⟨c0, hc0, hcv⟩ := hv
      simp only [List.mem_singleton] at hc0
      subst hc0
      have hpb := plain_of_mem_expand (G := G) (S := [b]) (c := c') (by simp [hb'])
      rw [expand_sem G [b] hpb, hb']
      exact ⟨c', by simp, restricts_sound hfound hcv hh hl hf hu hno⟩
    · cases hfound
  · cases hb

/-- The candidates of one clause each, with that clause, unfolded once. -/
@[nospecialize] def candidateRows (G : NormalGraph ι) (candidates : Ty ι) : List (ι × Clause (Ty ι)) :=
  candidates.filterMap fun b => match expand G [b] with
    | [c'] => some (b, c')
    | _ => none

/-- `restriction` over candidates unfolded once (`candidateRows`). -/
@[nospecialize] def restrictionIn [DecidableEq ι] (G : NormalGraph ι) (a : ι) (f : PropKey) (ts : List Tag)
    (rows : List (ι × Clause (Ty ι))) : Option ι :=
  match expand G [a] with
  | [c] => (rows.find? fun r => r.1 != a && restricts G c r.2 f ts).map (·.1)
  | _ => none

theorem find?_filterMap_fst {g : β → Option (β × γ)} (hg : ∀ b x, g b = some x → x.1 = b)
    (P : β × γ → Bool) : ∀ cs : List β,
    ((cs.filterMap g).find? P).map Prod.fst = cs.find? (fun b => (g b).any P)
  | [] => rfl
  | b :: bs => by
    rw [List.filterMap_cons, List.find?_cons]
    cases h : g b with
    | none => simpa only [h, Option.any_none] using find?_filterMap_fst hg P bs
    | some x =>
      simp only [List.find?_cons, Option.any_some]
      cases hp : P x with
      | true => simp [hg b x h]
      | false => simpa only using find?_filterMap_fst hg P bs

theorem restrictionIn_eq [DecidableEq ι] (G : NormalGraph ι) (a : ι) (f : PropKey) (ts : List Tag)
    (candidates : Ty ι) :
    restrictionIn G a f ts (candidateRows G candidates) = restriction G a f ts candidates := by
  unfold restrictionIn restriction candidateRows
  split
  · rename_i c _
    rw [find?_filterMap_fst]
    · congr 1
      funext b
      split <;> simp
    · intro b x hx
      split at hx
      · cases hx; rfl
      · cases hx
  · rfl

/-- A type's hash by the graph's label hash. -/
@[nospecialize] def tyHash (G : NormalGraph ι) (T : Ty ι) : UInt64 := T.foldl (fun x l => mixHash x (G.labelHash l)) 7

/-- One view's step of `viewsHash`: its key, and its type unless the key is
`f`, which `restricts` changes. -/
@[nospecialize] def viewStep (G : NormalGraph ι) (f : PropKey) (acc : UInt64) (v : PropKey × Ty ι) : UInt64 :=
  mixHash acc (mixHash (hash v.1) (if v.1 == f then 0 else tyHash G v.2))

/-- The views' hash with the views of `f` at no type. -/
@[nospecialize] def viewsHash (G : NormalGraph ι) (f : PropKey) (vs : List (PropKey × Ty ι)) : UInt64 :=
  vs.foldl (viewStep G f) 13

/-- The key `restricts` keeps: a record clause's first invariant operand and
its views but at `f`, hashed by the graph's label hash. A candidate
`restricts` accepts has its source's key (`restricts_key`). -/
@[nospecialize] def restrictKey (G : NormalGraph ι) (f : PropKey) : Clause (Ty ι) → UInt64
  | .refs a _ vs _ _ _ _ => mixHash (a.foldl (fun acc p => mixHash acc (mixHash (hash p.1) (tyHash G p.2))) 11)
      (viewsHash G f vs)
  | _ => 0

theorem viewsHash_foldl [DecidableEq ι] {G : NormalGraph ι} {f : PropKey} :
    ∀ {vs vs' : List (PropKey × Ty ι)} (acc : UInt64), vs.length = vs'.length →
      (∀ x ∈ vs.zip vs', x.1.1 = x.2.1 ∧ (x.1.2 = x.2.2 ∨ x.1.1 = f)) →
      vs.foldl (viewStep G f) acc = vs'.foldl (viewStep G f) acc
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | (k, T) :: vs, (k', T') :: vs', acc, hl, h => by
    obtain ⟨hk, ht⟩ := h ((k, T), (k', T')) (by simp)
    simp only at hk ht
    subst hk
    have hstep : viewStep G f acc (k, T) = viewStep G f acc (k, T') := by
      rcases ht with rfl | rfl
      · rfl
      · simp [viewStep]
    simp only [List.foldl_cons, hstep]
    exact viewsHash_foldl _ (by simpa using hl) fun x hx => h x (by simp [hx])

theorem viewsHash_eq [DecidableEq ι] {G : NormalGraph ι} {f : PropKey} {vs vs' : List (PropKey × Ty ι)}
    (hl : vs.length = vs'.length) (h : ∀ x ∈ vs.zip vs', x.1.1 = x.2.1 ∧ (x.1.2 = x.2.2 ∨ x.1.1 = f)) :
    viewsHash G f vs = viewsHash G f vs' :=
  viewsHash_foldl 13 hl h

theorem restricts_key [DecidableEq ι] {G : NormalGraph ι} {c c' : Clause (Ty ι)} {f : PropKey} {ts : List Tag}
    (h : restricts G c c' f ts = true) : restrictKey G f c' = restrictKey G f c := by
  cases c <;> cases c' <;> simp only [restricts, Bool.false_eq_true] at h
  case refs.refs a _ vs _ _ _ _ a' _ vs' _ _ _ _ =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, hl⟩, hall⟩ := h
    subst ha
    have hv : ∀ x ∈ vs.zip vs', x.1.1 = x.2.1 ∧ (x.1.2 = x.2.2 ∨ x.1.1 = f) := by
      intro x hx
      have := List.all_eq_true.mp hall x hx
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at this
      obtain ⟨hk, hv | hf⟩ := this
      · exact ⟨hk, .inl hv⟩
      · exact ⟨hk, .inr hf.1.1.1⟩
    simp only [restrictKey]
    rw [viewsHash_eq hl hv]

/-- Unfolded candidates by key, each key's in list order. -/
@[nospecialize] def rowIndex (G : NormalGraph ι) (f : PropKey) (rows : List (ι × Clause (Ty ι))) :
    Std.HashMap UInt64 (List (ι × Clause (Ty ι))) :=
  rows.foldr (fun r m => m.insert (restrictKey G f r.2) (r :: m.getD (restrictKey G f r.2) [])) {}

theorem rowIndex_getD (G : NormalGraph ι) (f : PropKey) (rows : List (ι × Clause (Ty ι))) (k : UInt64) :
    (rowIndex G f rows).getD k [] = rows.filter (fun r => restrictKey G f r.2 == k) := by
  induction rows with
  | nil => simp [rowIndex, Std.HashMap.getD_empty]
  | cons r rs ih =>
    simp only [rowIndex, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getD_insert]
    by_cases hk : restrictKey G f r.2 = k
    · subst hk; simp [ih]
    · simp [hk, ih]

/-- `restrictionIn` reading only the candidates of the source's key. -/
@[nospecialize] def restrictionAt [DecidableEq ι] (G : NormalGraph ι) (a : ι) (f : PropKey) (ts : List Tag)
    (idx : Std.HashMap UInt64 (List (ι × Clause (Ty ι)))) : Option ι :=
  match expand G [a] with
  | [c] => ((idx.getD (restrictKey G f c) []).find? fun r => r.1 != a && restricts G c r.2 f ts).map (·.1)
  | _ => none

theorem restrictionAt_eq [DecidableEq ι] (G : NormalGraph ι) (a : ι) (f : PropKey) (ts : List Tag)
    (rows : List (ι × Clause (Ty ι))) :
    restrictionAt G a f ts (rowIndex G f rows) = restrictionIn G a f ts rows := by
  unfold restrictionAt restrictionIn
  split
  · rename_i c _
    rw [rowIndex_getD, List.find?_filter]
    congr 2
    funext r
    cases hr : (r.1 != a && restricts G c r.2 f ts)
    · simp
    · simp only [Bool.and_eq_true] at hr
      simp [restricts_key hr.2]
  · rfl

/-- The labels of `A` an object may still have once every tag of `ts`
answered `false` of the value of its field `f`: a label each of whose clauses
fixes `f` at a covered type is dropped, and a label of one record clause a
label of `candidates` restricts (`restriction`) is read as that label. The
candidates are unfolded once for all of `A`'s labels and read by key
(`restrictionAt_eq`). -/
def uncoveredField [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) (f : PropKey) (ts : List Tag) (candidates : Ty ι) : Ty ι :=
  let idx := rowIndex G f (candidateRows G candidates)
  A.flatMap fun a =>
    if G.plain a && (expand G [a]).all (fieldCovered G · f ts) then []
    else [(restrictionAt G a f ts idx).getD a]

theorem uncoveredField_sound [DecidableEq ι] {G : NormalGraph ι} {A : Ty ι} {f : PropKey} {ts : List Tag} {candidates : Ty ι}
    {n W h v flds code oid l u}
    (hv : meaning G A (n+1) W v) (hh : HeapOk (n+1) W h)
    (hl : v = .objAt flds code oid) (hf : flds.lookup f = some l) (hu : h[l]? = some u)
    (hno : ∀ t ∈ ts, tagHolds t u = false ∨ protoFree t u = false) :
    meaning G (uncoveredField G A f ts candidates) (n+1) W v := by
  obtain ⟨a, ha, hva⟩ := hv
  have hm : meaning G [a] (n+1) W v := ⟨a, by simp, hva⟩
  cases hd : (G.plain a && (expand G [a]).all (fieldCovered G · f ts)) with
  | true =>
    exfalso
    simp only [Bool.and_eq_true, List.all_eq_true] at hd
    rw [expand_sem G [a] (by simp [NormalGraph.plainTy, hd.1])] at hm
    obtain ⟨c, hc, hcv, -⟩ := hm
    have hans := hd.2 c hc
    cases c with
    | refs a' bs vs os ms ks =>
      simp only [fieldCovered, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hans
      obtain ⟨⟨g, K⟩, hp, ⟨⟨rfl, hplain⟩, hall⟩⟩ := hans
      have hK := field_value (c := .refs a' bs vs os ms ks _) (K := K) hp hcv hh hl hf hu
      rw [expand_sem G K hplain] at hK
      obtain ⟨d, hd', hdv, -⟩ := hK
      exact coveredBy_sound (List.all_eq_true.mp hall d hd') hdv hno
    | _ => simp [fieldCovered] at hans
  | false =>
    have hmem : (restriction G a f ts candidates).getD a ∈ uncoveredField G A f ts candidates :=
      List.mem_flatMap.mpr ⟨a, ha, by simp [hd, restrictionAt_eq, restrictionIn_eq]⟩
    cases hr : restriction G a f ts candidates with
    | none =>
      simp only [hr, Option.getD_none] at hmem
      exact ⟨a, hmem, hva⟩
    | some b =>
      simp only [hr, Option.getD_some] at hmem
      obtain ⟨b', hb', hbv⟩ := restriction_sound hr hm hh hl hf hu hno
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact ⟨b', hmem, hbv⟩

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
  | .refs a bs vs os ms ks st =>
    match os.find? (fun o => decide (o.key = k)) with
    | some o =>
      if o.readonly || ((a :: bs).flatten.isEmpty && !ks.any KeyBound.closed) then
        .refs a bs (vs ++ [(k, o.type)]) os ms ks st
      else .refs (a ++ [(k, o.type)]) bs vs os ms ks st
    | none => .refs a bs vs os ms ks st
  | .dict a bs vs ds os ms ks cs st => .dict a bs (vs ++ presentViews k ds) ds os ms ks cs st
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
      obtain ⟨⟨⟨flds, oid, hv, hrec⟩, hbs⟩, hview, hopt, hmeth, hkeys, hst⟩ := hc
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
        refine ⟨⟨⟨flds, oid, rfl, ?_⟩, hbs.1, fun _ => ?_⟩, hview, hopt, hmeth, hkeys, hst⟩
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
        refine ⟨⟨⟨flds, oid, rfl, hrec⟩, hbs⟩, ?_, hopt, hmeth, hkeys, hst⟩
        intro f T hm
        simp only [ReferenceConjunctions.famsOf, List.map_append, List.mem_append,
          List.map_cons, List.map_nil, List.mem_singleton] at hm
        rcases hm with hm | hm
        · exact hview f T hm
        · cases hm
          exact .inl (viewT_single ⟨flds, l, c', oid, rfl, hl, hw, fun j hj W' u hu => (hsc j hj W' u).1 hu⟩)
    · exact hc
  | dict a bs vs ds os ms ks cs =>
    obtain ⟨hr, hview, ⟨hd, hcs⟩, hopt, hmeth, hkeys, hst⟩ := hc
    refine ⟨hr, fun f T hm => ?_, ⟨hd, hcs⟩, hopt, hmeth, hkeys, hst⟩
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
  | .refs a bs vs os ms ks st, .refs a' bs' vs' os' ms' ks' st' =>
    within a a' && within bs bs' && within vs vs' && within os os' && within ms ms' && within ks ks' &&
      within st st'
  | .dict a bs vs ds os ms ks cs st, .dict a' bs' vs' ds' os' ms' ks' cs' st' =>
    within a a' && within bs bs' && within vs vs' && within ds ds' && within os os' &&
      within ms ms' && within ks ks' && within cs cs' && within st st'
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
      obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hv⟩, ho⟩, hm⟩, hk⟩, hs⟩ := hw
      obtain ⟨⟨⟨flds, oid, hvf, hrec⟩, hbs⟩, hview, hopt, hmeth, hkeys, hst⟩ := hc
      refine ⟨⟨⟨flds, oid, hvf, fun f T hmem => ?_⟩, fun B hB => ?_,
        fun hne => hbs.2 (fewer_named ha hb hne)⟩, fun f T hmem => ?_, ?_,
        fun m hm' => ?_, fun K hK => hkeys K (within_mem hk hK),
        stableKeysT_weaken (fun x hx => within_mem hs hx) n W v hst⟩
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
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hv⟩, hds⟩, ho⟩, hm⟩, hk⟩, hcs⟩, hs⟩ := hw
      obtain ⟨⟨⟨flds, oid, hvf, hrec⟩, hbs⟩, hview, ⟨hd, hc⟩, hopt, hmeth, hkeys, hst⟩ := hc
      refine ⟨⟨⟨flds, oid, hvf, fun f T hmem => ?_⟩, fun B hB => ?_,
        fun hne => hbs.2 (fewer_named ha hb hne)⟩, fun f T hmem => ?_,
        ⟨fun x hx => hd x (within_mem hds hx), fun x hx => hc x (within_mem hcs hx)⟩, ?_,
        fun m hm' => ?_, fun K hK => hkeys K (within_mem hk hK),
        stableKeysT_weaken (fun x hx => within_mem hs hx) n W v hst⟩
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

/-- The labels of `A` an object owning the key `f` may still have once the
value at `f` answered `tag` with `q`: the field slice of each clause with
`f` taken as present (`promote`), so that an optional key's type answers as
a field's does. A label is dropped only where every clause of it, so
promoted, fixes `f` at a type answering the other way; an empty type
answers every way. -/
def presentSlice (G : NormalGraph ι) (A : Ty ι) (f : PropKey) (tag : Tag) (q : Bool) : Ty ι :=
  A.filter fun a => !(G.plain a && (expand G [a]).all fun c => fieldAnswers G (promote f c) f tag (!q))

theorem presentSlice_sound {G : NormalGraph ι} {A : Ty ι} {f tag q n W h v flds code l u}
    (hv : meaning G A (n+1) W v) (hh : HeapOk (n+1) W h)
    (hl : v = .objAt flds code oid) (hf : flds.lookup f = some l) (hu : h[l]? = some u)
    (hq : tagHolds tag u = q ∨ protoFree tag u = false) : meaning G (presentSlice G A f tag q) (n+1) W v := by
  obtain ⟨a, ha, hva⟩ := hv
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hva⟩
  cases hd : (G.plain a && (expand G [a]).all fun c => fieldAnswers G (promote f c) f tag (!q)) with
  | false => rfl
  | true =>
    exfalso
    simp only [Bool.and_eq_true, List.all_eq_true] at hd
    have hm : meaning G [a] (n+1) W v := ⟨a, by simp, hva⟩
    rw [expand_sem G [a] (by simp [NormalGraph.plainTy, hd.1])] at hm
    obtain ⟨c, hc, hcv, -⟩ := hm
    have hk : KeyFound f v := fun flds' code' oid' he hn => by
      rw [hl] at he
      cases he
      rw [hf] at hn
      cases hn
    have hcv' := promote_sound hcv hk
    have hans := hd.2 c hc
    generalize promote f c = c' at hcv' hans
    cases c' with
    | refs a' bs vs os ms ks =>
      simp only [fieldAnswers, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hans
      obtain ⟨⟨g, K⟩, hp, ⟨rfl, hplain⟩, hall⟩ := hans
      have hK : Answers G K tag (!q) :=
        ⟨hplain, fun c hc => beq_iff_eq.mp (List.all_eq_true.mp hall c hc)⟩
      have hu' := field_value (c := .refs a' bs vs os ms ks _) (K := K) hp hcv' hh hl hf hu
      have := answers_weak hK hu' hq
      cases q <;> simp at this
    | _ => simp [fieldAnswers] at hans

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
      cs.any fun c => match c with | .numLit b' => b' == b | .numIn S => S.contains b | _ => false
  | .strEq s, true => cs.any fun c => match c with
      | .strLit s' => s' == s | .strIn S => S.contains s | _ => false
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
    cases v <;> simp [tagHolds, isVal] at ht hv
    rename_i bits
    simp only [numberEqual, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht.2 with h | h
    · subst h
      cases c <;> simp at hk
      · subst hk; exact ⟨_, hc, by simp [semWithArgs], rfl⟩
      · exact ⟨_, hc, ⟨_, hk, rfl⟩, rfl⟩
    · exact absurd h.2 hm.1
  case strEq.true s =>
    obtain ⟨c, hc, hk⟩ := List.any_eq_true.mp hm
    cases v <;> simp [tagHolds, isVal] at ht hv
    subst ht
    cases c <;> simp at hk
    · subst hk; exact ⟨_, hc, by simp [semWithArgs], rfl⟩
    · exact ⟨_, hc, ⟨_, hk, rfl⟩, rfl⟩
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
          MethodMembers.methodT_nil _ _ _, fun K hK => ?_, stableKeysT_nil _ _ _⟩
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

/-- A dictionary clause with an index: each of its members owns no
`[[proto]]` (`dictViewT`, `dictCellT`). -/
def indexedDict : Clause α → Bool
  | .dict _ _ _ ds _ _ _ cs _ => !ds.isEmpty || !cs.isEmpty
  | _ => false

/-- **No array is a dictionary.** Where the graph states the built-ins, a
member of a clause owning the store key owns the prototype key
(`arrayInvariant`), which a member of an indexed dictionary clause does not. -/
theorem not_array_of_indexed {G : NormalGraph ι} {c : Clause (Ty ι)} (hb : G.builtins.isSome = true)
    (hi : indexedDict c = true) {Ξ : Fam} {X : Ty ι → Fam} {P : Ty ι → ArgFam} {n W v}
    (hcv : semWithArgs Ξ X P c n W v) (hinv : builtinInvariant G (builtinValues G) c n W v)
    (ha : tagHolds .isArray v = true) : False := by
  cases c with
  | dict a bs vs ds os ms ks cs =>
    obtain ⟨-, -, ⟨hds, hcs⟩, -⟩ := hcv
    obtain ⟨flds, oid, hv, hst⟩ : ∃ flds oid, v = .objAt flds .absent oid ∧
        (flds.lookup CallArguments.arrayStoreField).isSome = true := by
      cases v with
      | objAt fs code oid =>
        cases code <;> simp [tagHolds] at ha
        exact ⟨fs, oid, rfl, by simpa [CallArguments.arrayStoreField] using ha⟩
      | _ => simp [tagHolds] at ha
    have hnone : flds.lookup CallArguments.protoField = none := by
      simp only [indexedDict, Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hi
      rcases hi with hd | hd
      · obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hd
        obtain ⟨flds', oid', hv', hp, -⟩ := hds d hd
        rw [hv] at hv'; cases hv'; exact hp.1
      · obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hd
        obtain ⟨flds', oid', hv', hp, -⟩ := hcs d hd
        rw [hv] at hv'; cases hv'; exact hp.1
    unfold builtinInvariant at hinv
    cases hr : G.builtins with
    | none => rw [hr] at hb; cases hb
    | some r =>
      rw [hr] at hinv
      simp only [Clause.carriesInvariant] at hinv
      obtain ⟨hview, -, -⟩ := hinv flds oid hv hst
      obtain ⟨flds', l, -, oid', hv', hl, -⟩ := hview CallArguments.protoField (builtinValues G r.proto) (by simp)
      rw [hv] at hv'; cases hv'
      rw [hnone] at hl; cases hl
  | _ => simp [indexedDict] at hi

/-- Where `Array.isArray` holds, every label of the tested type is kept in
`B`, or is a clause row each clause of which is of no array, an indexed
dictionary's (no array, where the graph states the built-ins), or a record's,
whose members that are arrays `B`'s builtins array label holds. -/
def arraySlice [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) : Bool :=
  (tagSlice G A .isArray true).all fun a =>
    B.contains a || (G.plain a && (G a).all fun c => tagClause .isArray c == some false ||
      (G.builtins.isSome && indexedDict c) || (c.carriesInvariant && B.any (builtinArrayLabel G)))

theorem arraySlice_sound [DecidableEq ι] {G : NormalGraph ι} {A B : Ty ι}
    (h : arraySlice G A B = true) {n W v} (hv : meaning G A n W v)
    (ha : tagHolds .isArray v = true) : meaning G B n W v := by
  simp only [arraySlice, List.all_eq_true] at h
  obtain ⟨a, haS, hva⟩ := tagSlice_sound (tag := .isArray) (q := true) hv (Or.inl ha)
  rcases Bool.or_eq_true_iff.mp (h a haS) with hB | hrow
  · exact ⟨a, List.contains_iff_mem.mp hB, hva⟩
  · simp only [Bool.and_eq_true, List.all_eq_true] at hrow
    obtain ⟨c, hc, hcv, hinv⟩ := (unfold_plain hrow.1 n W v).mp hva
    rcases Bool.or_eq_true_iff.mp (hrow.2 c hc) with hno | hrec
    · rcases Bool.or_eq_true_iff.mp hno with hno | hdict
      · have := tagClause_sound (beq_iff_eq.mp hno) hcv
        rw [ha] at this; cases this
      · simp only [Bool.and_eq_true] at hdict
        exact (not_array_of_indexed hdict.1 hdict.2 hcv hinv ha).elim
    · simp only [Bool.and_eq_true, List.any_eq_true] at hrec
      obtain ⟨hrec, L, hLB, hL⟩ := hrec
      obtain ⟨l, hl, hvl⟩ := builtinArray_of_record hL hrec hinv ha
      cases List.mem_singleton.mp hl
      exact ⟨L, hLB, hvl⟩

/-! ### A tag set under a test

A test answers on a tag set element by element (HOST-FAMILIES.md, "Tag
sets"): what the slice keeps of a set is the elements the test does not
contradict, each of which a clause of the target must hold. -/

/-- Whether the literal `e` is a member of the primitive clause `d`: its
family, itself, or a tag set holding it. -/
def litIn (e d : Clause α) : Bool :=
  match e, d with
  | .numLit _, .num | .strLit _, .str => true
  | .numLit a, .numLit b => a == b
  | .strLit a, .strLit b => a == b
  | .numLit a, .numIn S => S.contains a
  | .strLit a, .strIn S => S.contains a
  | _, _ => false

theorem litIn_sound {X : α → Fam} {P : α → ArgFam} {e d : Clause α} (h : litIn e d = true) {n W v}
    (hv : semWithArgs Ξ X P e n W v) : semWithArgs Ξ X P d n W v ∧ d.carriesInvariant = false := by
  cases e <;> cases d <;> simp [litIn] at h <;> simp only [semWithArgs] at hv ⊢ <;> subst hv
  all_goals first
    | exact ⟨⟨_, rfl⟩, rfl⟩
    | (subst h; exact ⟨rfl, rfl⟩)
    | exact ⟨⟨_, h, rfl⟩, rfl⟩

/-- Every label the tag slice keeps is in `B`, or each of its clauses the test
contradicts, `B` holds, or is a tag set whose every element the test
contradicts or a clause of `B` holds. -/
def setSlice [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) (t : Tag) (q : Bool) : Bool :=
  (tagSlice G A t q).all fun a => B.contains a ||
    (G.plain a && (expand G [a]).all fun c => tagClause t c == some (!q) ||
      (expand G B).contains c ||
      (c.elements != [c] && c.elements.all fun e => tagClause t e == some (!q) ||
        (expand G B).any (litIn e)))

theorem setSlice_sound [DecidableEq ι] {G : NormalGraph ι} {A B : Ty ι} {t : Tag} {q : Bool}
    (h : setSlice G A B t q = true) {n W v} (hv : meaning G A n W v)
    (ho : tagHolds t v = q ∨ protoFree t v = false) : meaning G B n W v := by
  obtain ⟨a, ha, hva⟩ := tagSlice_sound hv ho
  have ha' := List.all_eq_true.mp h a ha
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at ha'
  rcases ha' with hB | ⟨hplain, hcs⟩
  · exact ⟨a, hB, hva⟩
  have hpt : G.plainTy [a] = true := by simp [NormalGraph.plainTy, hplain]
  obtain ⟨c, hc, hcv⟩ := (expand_sem G [a] hpt n W v).mp ⟨a, by simp, hva⟩
  -- A clause the test contradicts holds no tested value.
  have contra : ∀ d, tagClause t d = some (!q) → semWithArgs (builtinExc G (builtinValues G))
      (meaning G) (argMeaning G) d n W v → False := by
    intro d hd hdv
    have hpf := tagClause_protoFree hd hdv
    have hans := tagClause_sound hd hdv
    rcases ho with ho | ho
    · rw [ho] at hans; cases q <;> simp at hans
    · rw [hpf] at ho; cases ho
  have hcc := List.all_eq_true.mp hcs c hc
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne,
    ne_eq, List.all_eq_true, List.any_eq_true] at hcc
  rcases hcc with (hno | hin) | ⟨-, helems⟩
  · exact (contra c hno hcv.1).elim
  · exact expand_sem_mpr ⟨c, expand_sub hin, hcv⟩
  · obtain ⟨e, he, hev⟩ := rowSem_elements G _ _ _ hcv
    rcases helems e he with hno | ⟨d, hd, hlit⟩
    · exact (contra e hno hev.1).elim
    · obtain ⟨hdv, hdr⟩ := litIn_sound hlit hev.1
      exact expand_sem_mpr ⟨d, expand_sub hd, hdv, builtinInvariant_of_withoutInvariant hdr _ _ _⟩

/-! ### `unknown` under a test

A JavaScript value (`isSourceVal`) is of exactly one kind: `null`,
`undefined`, a Boolean, a number, a string, a bigint, a symbol, an object
without call code, or one with call code, invocable or constructible. Each
kind is a clause, so a test on a value at the `source` clause keeps the
kinds it does not contradict (SOURCE-MODEL.md, "Slices of the value
universe by tag tests"). -/

/-- The kinds of a JavaScript value, each as its clause: an object without
call code is the record of no field (`refs` with no operand), an object
with call code `arrs [] []` where it is invocable and `ctors []` where it
is constructible. -/
def sourceKinds : List (Clause α) :=
  [.nul, .undef, .bool, .num, .str, .bigint, .symbol, .refs [] [] [], .arrs [] [], .ctors []]

/-- **The kinds cover `unknown`**: a member of the `source` clause is in one
of the kinds' clauses, meeting the built-ins' invariant there. -/
theorem sourceKinds_cover {G : NormalGraph ι} {n W v} (hv : clauseSem G .source n W v) :
    ∃ k ∈ (sourceKinds : List (Clause (List ι))), clauseSem G k n W v := by
  obtain ⟨⟨hsv, hsc⟩, hinv⟩ := hv
  have hval := sourceVal_isVal hsv
  -- A kind no record's: its family's test admits the value.
  have family : ∀ t, familyMember (sourceKinds : List (Clause (List ι))) t true = true →
      tagHolds t v = true → ∃ k ∈ (sourceKinds : List (Clause (List ι))), clauseSem G k n W v := by
    intro t hm ht
    obtain ⟨k, hk, hkv, hr⟩ := familyMember_sound (Ξ := builtinExc G (builtinValues G))
      (X := meaning G) (P := argMeaning G) hm hval hsc ht
    exact ⟨k, hk, hkv, builtinInvariant_of_withoutInvariant hr _ _ _⟩
  cases v with
  | nul => exact family .isNul (by simp [familyMember, sourceKinds]) rfl
  | undef => exact family .isUndef (by simp [familyMember, sourceKinds]) rfl
  | tru => exact family .isBool (by simp [familyMember, sourceKinds]) rfl
  | fls => exact family .isBool (by simp [familyMember, sourceKinds]) rfl
  | num b => exact family .isNum (by simp [familyMember, sourceKinds]) rfl
  | str s => exact family .isStr (by simp [familyMember, sourceKinds]) rfl
  | bigint i => exact family .isBigint (by simp [familyMember, sourceKinds]) rfl
  | sym i => exact family .isSymbol (by simp [familyMember, sourceKinds]) rfl
  | objAt fs code oid =>
    cases code with
    | absent =>
      refine ⟨.refs [] [] [], by simp [sourceKinds], ⟨⟨⟨⟨fs, oid, rfl, fun f T hm => by
          simp [ReferenceConjunctions.famsOf] at hm⟩, by simp, by simp [ReferenceConjunctions.famsOf]⟩,
        fun f T hm => by simp [ReferenceConjunctions.famsOf] at hm, optT_nil,
        MethodMembers.methodT_nil _ _ _, fun K hK => by simp at hK, stableKeysT_nil _ _ _⟩, ?_⟩⟩
      exact (builtinInvariant_carriesInvariant rfl rfl).mp hinv
    | bound t r pre => exact family .isFun (by simp [familyMember, sourceKinds]) rfl
    | graph arity E K start caps kind rest =>
      cases kind <;> exact family .isFun (by simp [familyMember, sourceKinds]) rfl
  | _ => simp [isSourceVal] at hsv

/-- Whether the clauses `cs` hold a kind: as one of them, or, the Boolean
kind, as its two singletons. -/
def kindIn [DecidableEq α] (cs : List (Clause α)) (k : Clause α) : Bool :=
  cs.contains k || (k == .bool && cs.contains (.boolLit true) && cs.contains (.boolLit false))

theorem kindIn_sound [DecidableEq ι] {G : NormalGraph ι} {cs : List (Clause (List ι))} {k}
    (h : kindIn cs k = true) {n W v} (hv : clauseSem G k n W v) :
    ∃ c ∈ cs, clauseSem G c n W v := by
  simp only [kindIn, Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at h
  rcases h with hk | ⟨⟨rfl, ht⟩, hf⟩
  · exact ⟨k, hk, hv⟩
  · obtain ⟨hb, -⟩ := hv
    rcases hb with rfl | rfl
    · exact ⟨_, ht, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩
    · exact ⟨_, hf, rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩

/-- Every label the tag slice keeps is in `B`, or each of its clauses the
test contradicts, `B` holds, or is `source`, each of whose kinds the test
contradicts or `B` holds. -/
def sourceSlice [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) (t : Tag) (q : Bool) : Bool :=
  (tagSlice G A t q).all fun a => B.contains a ||
    (G.plain a && (expand G [a]).all fun c => tagClause t c == some (!q) ||
      (expand G B).contains c ||
      (c == .source && (sourceKinds : List (Clause (List ι))).all fun k =>
        tagClause t k == some (!q) || kindIn (expand G B) k))

theorem sourceSlice_sound [DecidableEq ι] {G : NormalGraph ι} {A B : Ty ι} {t : Tag} {q : Bool}
    (h : sourceSlice G A B t q = true) {n W v} (hv : meaning G A n W v)
    (ho : tagHolds t v = q ∨ protoFree t v = false) : meaning G B n W v := by
  obtain ⟨a, ha, hva⟩ := tagSlice_sound hv ho
  have ha' := List.all_eq_true.mp h a ha
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at ha'
  rcases ha' with hB | ⟨hplain, hcs⟩
  · exact ⟨a, hB, hva⟩
  have hpt : G.plainTy [a] = true := by simp [NormalGraph.plainTy, hplain]
  obtain ⟨c, hc, hcv⟩ := (expand_sem G [a] hpt n W v).mp ⟨a, by simp, hva⟩
  -- A clause the test contradicts holds no tested value.
  have contra : ∀ d, tagClause t d = some (!q) → semWithArgs (builtinExc G (builtinValues G))
      (meaning G) (argMeaning G) d n W v → False := by
    intro d hd hdv
    have hpf := tagClause_protoFree hd hdv
    have hans := tagClause_sound hd hdv
    rcases ho with ho | ho
    · rw [ho] at hans; cases q <;> simp at hans
    · rw [hpf] at ho; cases ho
  have hcc := List.all_eq_true.mp hcs c hc
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.contains_iff_mem,
    List.all_eq_true] at hcc
  rcases hcc with (hno | hin) | ⟨rfl, hkinds⟩
  · exact (contra c hno hcv.1).elim
  · exact expand_sem_mpr ⟨c, expand_sub hin, hcv⟩
  · obtain ⟨k, hk, hkv⟩ := sourceKinds_cover hcv
    rcases hkinds k hk with hno | hin
    · exact (contra k hno hkv.1).elim
    · obtain ⟨d, hd, hdv⟩ := kindIn_sound hin hkv
      exact expand_sem_mpr ⟨d, expand_sub hd, hdv⟩

/-- What a test answering `q` keeps of `A`, a `source` row given as the
kinds it does not contradict, read at `kinds`, the kinds' labels in the
order of `sourceKinds`: the type `sourceSlice` checks. Untrusted: the edge's
check decides. -/
def sourceRefine [DecidableEq ι] (G : NormalGraph ι) (kinds : List ι) (A : Ty ι) (t : Tag) (q : Bool) : Ty ι :=
  let sliced := tagSlice G A t q
  if kinds.isEmpty then sliced else
  sliced.flatMap fun a =>
    if G.plain a && G a == [.source] then
      kinds.filter fun k => !(G.plain k && (G k).all fun c => tagClause t c == some (!q))
    else [a]

/-- Sufficient implementations of ObservedSub. Whole-label filtering is only
an algorithm for the tag case, not the meaning of refinement. -/
@[nospecialize] def checkObservedSubResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (A B : Ty ι) (o : Observation) (p : PositiveCertificates.SubtypeChoices ι) : CheckResult ι Unit :=
  match o with
  | .boolean q => CheckResult.ofBool (booleanMember G B q)
  | .tag t q =>
      (ProgramCertificates.checkSubtypeUsing G images (tagSlice G A t q) B p).orElse fun _ =>
      CheckResult.ofBool (tagMember G B t q || presentKey t q (promotes G (tagSlice G A t q) B) ||
        (t == .isArray && q && arraySlice G A B) || meetSlice G A B t q || setSlice G A B t q ||
        sourceSlice G A B t q)

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
      (t == .isArray && q && arraySlice G A B) || meetSlice G A B t q || setSlice G A B t q ||
      sourceSlice G A B t q := by
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
    rcases hc with (((((hc | hm) | hk) | ⟨⟨ht, hq⟩, hs⟩) | hmeet) | hset) | hsource
    · exact PositiveCertificates.acceptedUsing hc n W v (tagSlice_sound hv ho)
    · exact tagMember_sound hm (meaning_value hv).1 (meaning_value hv).2 (ho.resolve_right (by
        cases t <;> cases q <;> simp [tagMember, familyMember] at hm <;> simp [protoFree]))
    · obtain ⟨k, hp, hkey⟩ := presentKey_sound hk ho
      exact promotes_sound hp (tagSlice_sound hv ho) hkey
    · have ht := beq_iff_eq.mp ht
      subst ht; subst hq
      exact arraySlice_sound hs hv (ho.resolve_right (by simp [protoFree]))
    · exact meetSlice_sound hmeet hv ho
    · exact setSlice_sound hset hv ho
    · exact sourceSlice_sound hsource hv ho

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
      ProgramCertificates.checkSubtypeUsing G images (factSlice G A fct.field fct.contents.atomsView) B p

@[nospecialize] def cellRefinements [DecidableEq ι] (cells : HeapFacts.Facts) (A B : Ty ι) (j : Nat)
    (G : NormalGraph ι) (images : InstanceImageCheck G) (p : PositiveCertificates.SubtypeChoices ι) : Bool :=
  (cellRefinementsResult cells A B j G images p).accepted

theorem cellRefinements_eq [DecidableEq ι] (cells : HeapFacts.Facts) (A B : Ty ι) (j : Nat)
    (G : NormalGraph ι) (images : InstanceImageCheck G) (p : PositiveCertificates.SubtypeChoices ι) :
    cellRefinements cells A B j G images p =
      cells.any fun fct => fct.slot == j &&
        PositiveCertificates.checkUsing G images (factSlice G A fct.field fct.contents.atomsView) B p := by
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

/-- The present-key refinements an observation admits for other slots: an
object the tested value was read from through an optional key
(`optionals`), where the observation rules out the `undefined` a read of
the key gives where the object lacks it, so that the object has the key and
the value read is the one at it: the object keeps the labels of its present
slice (`presentSlice`). -/
@[nospecialize] def presentRefinementsResult [DecidableEq ι] (o : Observation) (optionals : List (Nat × PropKey))
    (A B : Ty ι) (j : Nat) (G : NormalGraph ι) (images : InstanceImageCheck G)
    (p : PositiveCertificates.SubtypeChoices ι) : CheckResult ι Unit :=
  match o with
  | .tag t q => (CheckResult.ofBool (excludesUndef (.tag t q))).bind fun _ =>
      CheckResult.any optionals fun (k, f) =>
        (CheckResult.ofBool (k == j)).bind fun _ =>
          ProgramCertificates.checkSubtypeUsing G images (presentSlice G A f t q) B p
  | .boolean _ => failure

@[nospecialize] def presentRefinements [DecidableEq ι] (o : Observation) (optionals : List (Nat × PropKey))
    (A B : Ty ι) (j : Nat) (G : NormalGraph ι) (images : InstanceImageCheck G)
    (p : PositiveCertificates.SubtypeChoices ι) : Bool :=
  (presentRefinementsResult o optionals A B j G images p).accepted

theorem presentRefinements_eq [DecidableEq ι] (o : Observation) (optionals : List (Nat × PropKey)) (A B : Ty ι)
    (j : Nat) (G : NormalGraph ι) (images : InstanceImageCheck G) (p : PositiveCertificates.SubtypeChoices ι) :
    presentRefinements o optionals A B j G images p =
  match o with
  | .tag t q => excludesUndef (.tag t q) && optionals.any fun (k, f) => k == j &&
      PositiveCertificates.checkUsing G images (presentSlice G A f t q) B p
  | .boolean _ => false := by
  cases o <;> simp only [presentRefinements, presentRefinementsResult, CheckResult.accepted_any,
    CheckResult.accepted_bind, CheckResult.accepted_ofBool, ProgramCertificates.checkSubtypeUsing_accepted]
  rfl

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
      else ((((ProgramCertificates.checkSubtypeUsing G images A B p).orElse fun _ =>
        fieldRefinementsResult o (fields ++ optionals) A B sourceSlot G images p).orElse fun _ =>
        CheckResult.ofBool (optionalRefinements o optionals A B sourceSlot G)).orElse fun _ =>
        presentRefinementsResult o optionals A B sourceSlot G images p).orElse fun _ =>
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
            presentRefinements o optionals A B sourceSlot G images p ||
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
        presentRefinements o optionals A B (slot mapping j) G images p ||
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
       (∃ t q f, o = .tag t q ∧ (slot mapping j, f) ∈ optionals ∧ excludesUndef o = true ∧
         FamLe (meaning G (presentSlice G A f t q)) (meaning G B)) ∨
       ∃ fct ∈ cells, fct.slot = slot mapping j ∧
         FamLe (meaning G (factSlice G A fct.field fct.contents.atomsView)) (meaning G B))

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
        rcases hc with (((hc | hc) | hc) | hc) | hc
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
        · right; right; right; left
          cases o with
          | boolean _ => simp [presentRefinements_eq] at hc
          | tag t q =>
            simp only [presentRefinements_eq, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨hx, ⟨k, f⟩, hk, rfl, hck⟩ := hc
            exact ⟨t, q, f, rfl, hk, hx, PositiveCertificates.acceptedUsing hck⟩
        · right; right; right; right
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
    rcases h with h | ⟨t, q, f, rfl, hf, hs⟩ | ⟨f, hf, hx, hp⟩ | ⟨t, q, f, rfl, hf, hx, hs⟩ | ⟨fct, hm, hslot, hs⟩
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
    -- Read through a key the object may lack, where the observation rules
    -- out the `undefined` an absent key gives: the object has the key, and
    -- the read gave its value.
    · obtain ⟨flds, c, oid, hv, hab, hpresent⟩ := hopt _ f hf
      cases hfl : flds.lookup f with
      | none => exact absurd (hab hfl) (excludesUndef_sound hx ho)
      | some l => exact hs (n+1) W _ (presentSlice_sound (he.2 _ A ha) hh hv hfl (hpresent l hfl) ho)
    · obtain ⟨flds, c, oid, u, hv, hr, hatom⟩ := hcells fct hm
      rw [hslot] at hv
      exact hs (n+1) W _ (factSlice_sound (he.2 _ A ha) hh hv hr (ValueSets.ValueSet.atomsView_holds hatom))

end Verification.BranchRefinement
