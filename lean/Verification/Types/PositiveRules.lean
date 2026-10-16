import Verification.Types.PositiveGraphs

/-! Declarative subtyping for positive recursive graphs. Rules have only finite
syntactic premises; semantic soundness is a separate theorem. -/
namespace Verification.PositiveRules
open PositiveNormalization PositiveGraphs ReferenceConjunctions Tower CallEffects

abbrev Table (ι : Type) := List (List ι × List ι)
/-- A table's relation: its rows, and label inclusion, which needs no row: a
type is within any type listing its labels. -/
abbrev Rel (table : Table ι) (a b : List ι) : Prop := (a, b) ∈ table ∨ ∀ i ∈ a, i ∈ b

/-- Fixed signatures, including their required per-call effect. -/
abbrev Ops (ι : Type) := List (Arrow (List ι))

/-- Rows known, by a proof outside a table, to be below an arrow clause: a
scheme row, and the fixed and variadic signatures of one of its instances. -/
abbrev Known (ι : Type) := List (List ι × Ops ι × List (RestArrow (List ι)))

/-- Scheme transport preserves the kind of signatures, call or construct, and
associated positions, and independently checks protection of
observation/result bounds on both rows. -/
@[nospecialize] def sameShape [DecidableEq ι] (s t : SchemeRow ι) : Bool :=
  decide (s.resolution = t.resolution) && s.resolutionValid && t.resolutionValid &&
    s.construct == t.construct

theorem sameShape_construct [DecidableEq ι] {s t : SchemeRow ι} (h : sameShape s t = true) :
    s.construct = t.construct := by
  simp only [sameShape, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

theorem resolutionValid_protected [DecidableEq ι] {s : SchemeRow ι}
    (h : s.resolutionValid = true) : s.protectedSlots := by
  simp only [SchemeRow.resolutionValid, Bool.or_eq_true] at h
  rcases h with h | h
  · have he : s.resolution = [] := List.isEmpty_iff.mp h
    simp [SchemeRow.protectedSlots, he]
  · simp only [Bool.and_eq_true, List.all_eq_true] at h
    intro g hg p hp b hb B hB
    have hs := h.2 g hg
    have hn := hs.2 (b, B) hB p hp
    simp only [bne_iff_ne] at hn
    exact hn hb

theorem sameShape_allowed [DecidableEq ι] {s t : SchemeRow ι}
    (domain : SchemeDomain ι k) (h : sameShape s t = true)
    (As : List (ParameterFamily k)) : domain.allowed s As ↔ domain.allowed t As := by
  simp only [sameShape, Bool.and_eq_true, decide_eq_true_eq] at h
  exact domain.congr s t h.1.1.1
    ⟨fun _ => resolutionValid_protected h.1.2, fun _ => resolutionValid_protected h.1.1.2⟩ As

/-- The clauses of a type's clause rows. -/
@[nospecialize] def clausesOf (G : NormalGraph ι) (S : List ι) : List (Clause (List ι)) := S.flatMap G

/-- A type's clauses, when every label is a clause row, and none otherwise. A
rule reading a type's clauses reads them here, so a type with a parameter or
scheme row has none to read: its members are not described by clauses. -/
@[nospecialize] def expand (G : NormalGraph ι) (S : List ι) : List (Clause (List ι)) :=
  if G.plainTy S then clausesOf G S else []

theorem expand_of_plain {G : NormalGraph ι} {S : List ι} (h : G.plainTy S = true) :
    expand G S = clausesOf G S := by simp [expand, h]

/-- A type with a clause to read is of clause rows. -/
theorem plain_of_mem_expand {G : NormalGraph ι} {S : List ι} {c}
    (h : c ∈ expand G S) : G.plainTy S = true := by
  unfold expand at h; split at h
  · assumption
  · simp at h

theorem expand_sub {G : NormalGraph ι} {S : List ι} {c} (h : c ∈ expand G S) :
    c ∈ clausesOf G S := by
  rwa [expand_of_plain (plain_of_mem_expand h)] at h

/-- Decompose one clause into an exactly equivalent finite union. `bool` is the
only clause of this language whose inhabitants are a finite set, so it is the
only one that decomposes: every Boolean value is `true` or `false`. Everything
else is already its own decomposition. -/
def splitClause : Clause α → List (Clause α)
  | .bool => [.boolLit true, .boolLit false]
  | c => [c]

/-- The clauses a covering obligation must discharge on its left. Splitting the
source, rather than searching the target for a matching pair, keeps `Covers`
clause-to-clause while letting one source clause be covered by several target
clauses. -/
@[nospecialize] def sourceClauses (G : NormalGraph ι) (S : List ι) : List (Clause (List ι)) :=
  (clausesOf G S).flatMap splitClause


/-- Top has no shape; it can share a member with any clause. -/
def isTop : Clause α → Bool
  | .top => true
  | _ => false

/-- Two clauses can share a member: same shape, or top, which has none. -/
def overlaps (a b : Clause α) : Bool :=
  isTop a || isTop b || (match a with | .source => true | _ => false) ||
    (match b with | .source => true | _ => false) || shape a == shape b

/-- A conservative compatibility check: two union labels can share a value
only if some pair of their clauses has the same outer shape. A parameter or
scheme row has no clauses to compare, so it may share a value with anything. -/
@[nospecialize] def compatible (G : NormalGraph ι) (i k : ι) : Bool :=
  !G.plain i || !G.plain k || (G i).any fun a => (G k).any fun b => overlaps a b

/-- The value members of a type, its parameter rows read at `η`. -/
noncomputable def mixedValues (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι) : Fam :=
  setSem (fun i => qDenoteWithArgs G (mixedParameters G) (η, i)) S

/-- The argument lists of a type, its parameter rows read at `η`. -/
noncomputable abbrev mixedArgs (G : NormalGraph ι) (η : MixedAssignment ι) : List ι → ArgFam :=
  graphArguments G η (mixedValues G η)

/-- The built-in prototype type as rows read it: at the fixed assignment
`builtinsAt`. -/
noncomputable abbrev builtinValues (G : NormalGraph ι) : List ι → Fam :=
  mixedValues G (ParameterAssignment.empty .mixed)

/-- The graph's exception family: its builtins's `unknown`, its prototype type
read at `builtinsAt` (`builtinExc`). -/
noncomputable abbrev excOf (G : NormalGraph ι) : Fam := builtinExc G (builtinValues G)

/-- A clause's value members, its operands read at `η`. -/
noncomputable abbrev mixedSem (G : NormalGraph ι) (η : MixedAssignment ι) : Clause (List ι) → Fam :=
  rowSem G (builtinValues G) (mixedValues G η) (mixedArgs G η)

/-- An instance's contract is its scheme's body read at the instance's
assignment. -/
theorem instance_body (G : NormalGraph ι) (η : MixedAssignment ι) (s : SchemeRow ι) (As : List MixedFamily) :
    instanceTWithArgs (builtinExc G (setSem fun l => qDenoteWithArgs G (mixedParameters G) ((mixedParameters G).builtinsAt, l)))
      (fun η' S => setSem (fun l => qDenoteWithArgs G (mixedParameters G) (η', l)) S) η s As
      (mixedParameters G).arguments =
    semWithArgs (excOf G) (mixedValues G (assign η s.binders As)) (mixedArgs G (assign η s.binders As)) s.body := by
  unfold instanceTWithArgs sigsT SchemeRow.body instanceSigs instanceRestsWithArgs
  cases s.construct
  · rfl
  · simp only [if_true, semWithArgs, List.map_map]
    -- A scheme body states no static field: its empty bag holds of every class value.
    refine Eq.trans ?_ (bag_nil_absorb ?_).symm
    · rfl
    · intro n W v h
      obtain ⟨fs, _, _, _, _, _, _, oid, rfl, -⟩ := h.1.1
      exact ⟨_, _, _, rfl⟩

/-- A type's value members at the graph's own assignment. -/
noncomputable def meaning (G : NormalGraph ι) (S : List ι) : Fam := setSem (normalDenote G) S

/-- A clause's value members at the graph's own assignment. -/
noncomputable abbrev clauseSem (G : NormalGraph ι) : Clause (List ι) → Fam :=
  rowSem G (builtinValues G) (meaning G) (argMeaning G)

/-- A clause row means its clauses, at every assignment. -/
theorem mixed_unfold_plain {G : NormalGraph ι} (η : MixedAssignment ι) {i : ι}
    (hi : G.plain i = true) (n W v) :
    qDenoteWithArgs G (mixedParameters G) (η, i) n W v ↔ setSem (mixedSem G η) (G i) n W v := by
  simp only [NormalGraph.plain, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hi
  rw [qDenoteWithArgs_unfold]
  simp only [qLayerWithArgs, hi.1, hi.2, Bool.false_eq_true, ite_false]
  rfl

/-- Every clause of a type's labels is within the type's meaning. -/
theorem mixed_expand_mpr {G : NormalGraph ι} {η : MixedAssignment ι} {S : List ι} {n W v}
    (h : setSem (mixedSem G η) (clausesOf G S) n W v) : mixedValues G η S n W v := by
  obtain ⟨c, hc, hv⟩ := h
  obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
  exact ⟨i, hi, (mixed_unfold_plain η (NormalGraph.plain_of_clauses hc) n W v).mpr ⟨c, hc, hv⟩⟩

theorem expand_sem_mpr {G : NormalGraph ι} {S : List ι} {n W v}
    (h : setSem (clauseSem G) (clausesOf G S) n W v) : meaning G S n W v :=
  mixed_expand_mpr (η := G.env) h

/-- A member of a type is in one of its clauses, or in one of its parameter or
scheme rows. -/
theorem mixed_cases {G : NormalGraph ι} {η : MixedAssignment ι} {S : List ι} {n W v}
    (h : mixedValues G η S n W v) :
    setSem (mixedSem G η) (clausesOf G S) n W v ∨
      ∃ i ∈ S, G.plain i = false ∧ qDenoteWithArgs G (mixedParameters G) (η, i) n W v := by
  obtain ⟨i, hi, hv⟩ := h
  cases hp : G.plain i
  · exact .inr ⟨i, hi, hp, hv⟩
  · obtain ⟨c, hc, hv⟩ := (mixed_unfold_plain η hp n W v).mp hv
    exact .inl ⟨c, List.mem_flatMap.mpr ⟨i, hi, hc⟩, hv⟩

/-- A type of clause rows means the union of its labels' clauses. -/
theorem mixed_expand {G : NormalGraph ι} (η : MixedAssignment ι) {S : List ι}
    (hS : G.plainTy S = true) (n W v) :
    mixedValues G η S n W v ↔ setSem (mixedSem G η) (expand G S) n W v := by
  rw [expand_of_plain hS]
  have hp : ∀ i ∈ S, G.plain i = true := List.all_eq_true.mp hS
  constructor
  · rintro ⟨i, hi, hv⟩
    obtain ⟨c, hc, hv⟩ := (mixed_unfold_plain η (hp i hi) n W v).mp hv
    exact ⟨c, List.mem_flatMap.mpr ⟨i, hi, hc⟩, hv⟩
  · rintro ⟨c, hc, hv⟩
    obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
    exact ⟨i, hi, (mixed_unfold_plain η (hp i hi) n W v).mpr ⟨c, hc, hv⟩⟩

/-- A member of a type's one clause is a member of the type. -/
theorem mixed_of_expand {G : NormalGraph ι} {η : MixedAssignment ι} {S : List ι}
    {c : Clause (List ι)} (hS : expand G S = [c]) {n W v} (hv : mixedSem G η c n W v) :
    mixedValues G η S n W v := by
  have hp := plain_of_mem_expand (G := G) (S := S) (c := c) (by simp [hS])
  exact (mixed_expand η hp n W v).mpr ⟨c, by simp [hS], hv⟩

theorem expand_sem (G : NormalGraph ι) (S : List ι) (hS : G.plainTy S = true) (n W v) :
    meaning G S n W v ↔ setSem (clauseSem G) (expand G S) n W v :=
  mixed_expand G.env hS n W v

/-- The split is meaning preserving in a row too: only `bool` splits, and
neither it nor its parts is a record's. -/
theorem splitClause_row (G : NormalGraph ι) (A X : List ι → Fam) (P : List ι → ArgFam)
    (c : Clause (List ι)) (n W v) :
    setSem (rowSem G A X P) (splitClause c) n W v ↔ rowSem G A X P c n W v := by
  cases c
  case bool =>
    simp only [splitClause, setSem, rowSem, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left]
    simp only [builtinInvariant_of_withoutInvariant (G := G) (X := A) (show (Clause.bool : Clause (List ι)).carriesInvariant = false from rfl),
      builtinInvariant_of_withoutInvariant (G := G) (X := A) (show (Clause.boolLit true : Clause (List ι)).carriesInvariant = false from rfl),
      builtinInvariant_of_withoutInvariant (G := G) (X := A) (show (Clause.boolLit false : Clause (List ι)).carriesInvariant = false from rfl),
      and_true, semWithArgs, boolT]
    constructor
    · rintro (h | h) <;> simp [h]
    · rintro (h | h) <;> simp [h]
  all_goals simp [splitClause, setSem]

/-- Rows sharing a value through one clause each are compatible, whatever the
clauses' operands mean. -/
theorem compatible_of_clauses {G : NormalGraph ι} {i k : ι} {a b : Clause (List ι)}
    {X Y : List ι → Fam} {P Q : List ι → ArgFam} {n m W U v}
    (ha : a ∈ G i) (hb : b ∈ G k) (hva : semWithArgs Ξ X P a n W v)
    (hvb : semWithArgs Ξ Y Q b m U v) : compatible G i k = true := by
  simp only [compatible, NormalGraph.plain_of_clauses ha, NormalGraph.plain_of_clauses hb,
    Bool.not_true, Bool.false_or, List.any_eq_true]
  refine ⟨a, ha, b, hb, ?_⟩
  by_cases hta : a = .top
  · subst hta; rfl
  by_cases htb : b = .top
  · subst htb; simp [overlaps, isTop]
  by_cases hja : a = .source
  · subst a; simp [overlaps]
  by_cases hjb : b = .source
  · subst b; simp [overlaps]
  have hs := (semWithArgs_shape hta hja hva).symm.trans (semWithArgs_shape htb hjb hvb)
  simp [overlaps, hs]

/-- Rows sharing a value are compatible. -/
theorem mixed_compatible {G : NormalGraph ι} {η : MixedAssignment ι} {i k : ι} {n W U v}
    (hi : qDenoteWithArgs G (mixedParameters G) (η, i) n W v)
    (hk : qDenoteWithArgs G (mixedParameters G) (η, k) n U v) :
    compatible G i k = true := by
  cases hpi : G.plain i
  · simp [compatible, hpi]
  cases hpk : G.plain k
  · simp [compatible, hpk]
  obtain ⟨a, ha, hva, -⟩ := (mixed_unfold_plain η hpi n W v).mp hi
  obtain ⟨b, hb, hvb, -⟩ := (mixed_unfold_plain η hpk n U v).mp hk
  exact compatible_of_clauses ha hb hva hvb

/-- The element of an element rest: a type whose one clause is the pack of any
number of actuals at `E`, which is what a rest `...xs: E[]` says. -/
@[nospecialize] def restElem (G : NormalGraph ι) (P : List ι) : Option (List ι) :=
  match expand G P with
  | [.pack ⟨[], [], some E, false, .dense⟩ []] => some E
  | _ => none


/-- The argument lists of a type of clause rows are those of its clauses. -/
theorem graphArguments_plain {G : NormalGraph ι} {η : MixedAssignment ι} {X : List ι → Fam}
    {S : List ι} (hS : G.plainTy S = true) {n W vs} :
    graphArguments G η X S n W vs ↔ ∃ c ∈ clausesOf G S, clauseArguments X c n W vs := by
  have hk : ∀ i ∈ S, G.listParam i = false := fun i hi =>
    NormalGraph.listParam_of_plain (List.all_eq_true.mp hS i hi)
  constructor
  · rintro ⟨i, hi, h⟩
    simp only [hk i hi, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨c, hc, h⟩ := h
    exact ⟨c, List.mem_flatMap.mpr ⟨i, hi, hc⟩, h⟩
  · rintro ⟨c, hc, h⟩
    obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
    exact ⟨i, hi, by simp only [hk i hi, Bool.false_eq_true, ↓reduceIte]; exact ⟨c, hc, h⟩⟩

/-- A type whose one clause is a pack admits the lists its tuple fits, at the
current level. -/
theorem mixed_pack_args {G : NormalGraph ι} {η : MixedAssignment ι} {X : List ι → Fam}
    {Q : List ι} {τ : Tuple (List ι)} (hP : expand G Q = [.pack τ []]) {n W vs} :
    graphArguments G η X Q n W vs ↔ ArgumentContracts.Fits (tupleFams X τ) n W vs := by
  have hplain : G.plainTy Q = true := plain_of_mem_expand (c := .pack τ []) (by simp [hP])
  rw [graphArguments_plain hplain, ← expand_of_plain hplain, hP]
  simp [clauseArguments]

/-- An element rest admits the lists of its element's values. -/
theorem mixed_restElem {G : NormalGraph ι} {η : MixedAssignment ι} {X : List ι → Fam}
    {E El : List ι} (hel : restElem G E = some El) {n W vs} :
    graphArguments G η X E n W vs ↔ ∀ v ∈ vs, X El n W v := by
  have hx : expand G E = [.pack ⟨[], [], some El, false, .dense⟩ []] := by
    unfold restElem at hel
    split at hel <;> simp_all
  rw [mixed_pack_args hx]
  simp only [tupleFams, List.map_nil, Option.map]
  exact ArgumentContracts.fits_elem

/-- An element rest admits a list of its element's values before a list it
admits. -/
theorem mixed_restElem_append {G : NormalGraph ι} {η : MixedAssignment ι} {X : List ι → Fam}
    {E El : List ι} (hel : restElem G E = some El) {n W xs ys}
    (hxs : ∀ u ∈ xs, X El n W u) (hys : graphArguments G η X E n W ys) :
    graphArguments G η X E n W (xs ++ ys) := by
  refine (mixed_restElem hel).mpr fun u hu => ?_
  rcases List.mem_append.mp hu with hu | hu
  · exact hxs u hu
  · exact (mixed_restElem hel).mp hys u hu

/-- An exact tuple holds each actual at its position, at the current level. -/
theorem mixed_pack_exact {G : NormalGraph ι} {η : MixedAssignment ι} {X : List ι → Fam}
    {Q : List ι} {τ : Tuple (List ι)} (hP : expand G Q = [.pack τ []]) (hopt : τ.optional = [])
    (hrest : τ.rest = none) {n W vs} (hargs : graphArguments G η X Q n W vs) :
    ArgsT (τ.required.map X) n W vs := by
  have hf := (mixed_pack_args hP).mp hargs
  obtain ⟨req, opt, rest, r, d⟩ := τ
  simp only at hopt hrest
  subst hopt hrest
  exact (ArgumentContracts.fits_exact _ _ _ _).mp hf

@[nospecialize] def FamLeAt (G : NormalGraph ι) (η : MixedAssignment ι) (a b : List ι) (n : Nat) : Prop :=
  ∀ (W : WorldT n) (v : Val), mixedValues G η a n W v → mixedValues G η b n W v

/-- Argument lists within, below a level, along a relation. -/
@[nospecialize] def ArgsLeBelow (G : NormalGraph ι) (η : MixedAssignment ι) (R : List ι → List ι → Prop)
    (n : Nat) : Prop :=
  ∀ j, j < n → ∀ S T, R S T → ∀ (W : WorldT j) vs, mixedArgs G η S j W vs → mixedArgs G η T j W vs


/-- Pointwise domain inclusion requires the same number of actual arguments. -/
@[nospecialize] def Domains (R : List ι → List ι → Prop) : List (List ι) → List (List ι) → Prop
  | [], [] => True
  | a :: As, b :: Bs => R a b ∧ Domains R As Bs
  | _, _ => False

instance Domains.decidable {R : List ι → List ι → Prop} [∀ a b, Decidable (R a b)] :
    ∀ As Bs, Decidable (Domains R As Bs)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse id
  | _ :: _, [] => isFalse id
  | a :: As, b :: Bs =>
    if h : R a b then
      match Domains.decidable As Bs with
      | isTrue h' => isTrue ⟨h, h'⟩
      | isFalse h' => isFalse fun hd => h' hd.2
    else isFalse fun hd => h hd.1

theorem Domains.length_eq {R : List ι → List ι → Prop} :
    ∀ {As Bs : List (List ι)}, Domains R As Bs → As.length = Bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => congrArg Nat.succ (Domains.length_eq h.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Domains.sound {G : NormalGraph ι} {η : MixedAssignment ι} {R As Bs n}
    (hd : Domains R As Bs) (hr : ∀ a b, R a b → FamLeAt G η a b n)
    {W args} (ha : ArgsT (As.map (mixedValues G η)) n W args) :
    ArgsT (Bs.map (mixedValues G η)) n W args := by
  induction As generalizing Bs args with
  | nil => cases Bs <;> simp_all [Domains]
  | cons A As ih =>
    cases Bs with
    | nil => exact False.elim hd
    | cons B Bs =>
      cases args with
      | nil => exact False.elim ha
      | cons a args => exact ⟨hr A B hd.1 W a ha.1, ih hd.2 ha.2⟩

/-- Domains pointwise below others at one budget admit, there, every list
the others admit. -/
theorem Domains.short {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop} {j : Nat}
    (hr : ∀ a b, R a b → FamLeAt G η a b j) {W : WorldT j} :
    ∀ {As Bs : List (List ι)} {args : List Tm}, Domains R As Bs →
      ArgsShort (As.map (mixedValues G η)) j W args → ArgsShort (Bs.map (mixedValues G η)) j W args
  | [], [], _, _, h => h
  | [], _ :: _, _, hd, _ | _ :: _, [], _, hd, _ => hd.elim
  | A :: As, B :: Bs, [], hd, h => by
    simp only [List.map_cons, ArgsShort_nil_args, List.mem_cons, forall_eq_or_imp] at h ⊢
    have := Domains.short hr (args := []) hd.2 (ArgsShort_nil_args.mpr h.2)
    exact ⟨hr A B hd.1 W _ h.1, ArgsShort_nil_args.mp this⟩
  | A :: As, B :: Bs, a :: args, hd, h => by
    simp only [List.map_cons, ArgsShort_cons] at h ⊢
    exact ⟨hr A B hd.1 W a h.1, Domains.short hr hd.2 h.2⟩

/-- An empty position admits no list: no value is written there, and
`undefined` is not in it either. -/
theorem short_empty {G : NormalGraph ι} {η : MixedAssignment ι} {j : Nat} {W : WorldT j} :
    ∀ {As : List (List ι)} {args : List Tm}, [] ∈ As →
      ¬ ArgsShort (As.map (mixedValues G η)) j W args
  | [], _, he => by simp at he
  | A :: As, args, he => by
    intro h
    have hnone : ∀ u, ¬ mixedValues G η [] j W u := by
      intro u ⟨i, hi, _⟩; simp at hi
    cases args with
    | nil =>
      simp only [List.map_cons, ArgsShort_nil_args, List.mem_cons, forall_eq_or_imp] at h
      rcases List.mem_cons.mp he with rfl | he
      · exact hnone _ h.1
      · exact short_empty he (ArgsShort_nil_args.mpr h.2)
    | cons a args =>
      simp only [List.map_cons, ArgsShort_cons] at h
      rcases List.mem_cons.mp he with rfl | he
      · exact hnone _ h.1
      · exact short_empty he h.2

/-- A union at any position splits the admitted lists without reordering. -/
theorem short_union {G : NormalGraph ι} {η : MixedAssignment ι} (a b : List ι) (suffix : List (List ι)) {j : Nat}
    {W : WorldT j} : ∀ (pre : List (List ι)) {args : List Tm},
      ArgsShort ((pre ++ (a ++ b) :: suffix).map (mixedValues G η)) j W args →
      ArgsShort ((pre ++ a :: suffix).map (mixedValues G η)) j W args ∨
        ArgsShort ((pre ++ b :: suffix).map (mixedValues G η)) j W args
  | [], [], h => by
    simp only [List.nil_append, List.map_cons, ArgsShort_nil_args, List.mem_cons,
      forall_eq_or_imp] at h ⊢
    obtain ⟨⟨i, hi, hv⟩, hs⟩ := h
    rcases List.mem_append.mp hi with hi | hi
    · exact Or.inl ⟨⟨i, hi, hv⟩, hs⟩
    · exact Or.inr ⟨⟨i, hi, hv⟩, hs⟩
  | [], x :: args, h => by
    simp only [List.nil_append, List.map_cons, ArgsShort_cons] at h ⊢
    obtain ⟨⟨i, hi, hv⟩, hs⟩ := h
    rcases List.mem_append.mp hi with hi | hi
    · exact Or.inl ⟨⟨i, hi, hv⟩, hs⟩
    · exact Or.inr ⟨⟨i, hi, hv⟩, hs⟩
  | P :: pre, [], h => by
    simp only [List.cons_append, List.map_cons, ArgsShort_nil_args, List.mem_cons,
      forall_eq_or_imp] at h ⊢
    rcases short_union a b suffix pre (args := []) (ArgsShort_nil_args.mpr h.2) with h' | h'
    · exact Or.inl ⟨h.1, ArgsShort_nil_args.mp h'⟩
    · exact Or.inr ⟨h.1, ArgsShort_nil_args.mp h'⟩
  | P :: pre, x :: args, h => by
    simp only [List.cons_append, List.map_cons, ArgsShort_cons] at h ⊢
    rcases short_union a b suffix pre h.2 with h' | h'
    · exact Or.inl ⟨h.1, h'⟩
    · exact Or.inr ⟨h.1, h'⟩

/-- Fixed positions within an element rest's element: the rest is an element
rest, and each position is within its element. -/
@[nospecialize] def ElemRest (elem : List ι → Option (List ι)) (R : List ι → List ι → Prop)
    (As : List (List ι)) (E : List ι) : Prop :=
  match elem E with
  | some El => ∀ A ∈ As, R A El
  | none => False

/-- Fixed positions a variadic signature takes into its rest: none, or
positions within its element rest's element. -/
@[nospecialize] def IntoRest (elem : List ι → Option (List ι)) (R : List ι → List ι → Prop)
    (As : List (List ι)) (E : List ι) : Prop :=
  As = [] ∨ ElemRest elem R As E

/-- Actuals admitted by fixed positions, each within one family, are in it. -/
theorem short_all_le {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop} {j : Nat}
    (hr : ∀ a b, R a b → FamLeAt G η a b j) {W : WorldT j} {As : List (List ι)} {El : List ι}
    (h : ∀ A ∈ As, R A El) {xs : List Tm} (hs : ArgsT ((As.map (mixedValues G η)).take xs.length) j W xs) :
    ∀ u ∈ xs, mixedValues G η El j W u := by
  refine ArgsT_all_le (fun A hA u hu => ?_) hs
  rw [← List.map_take] at hA
  obtain ⟨A0, hA0, rfl⟩ := List.mem_map.mp hA
  exact hr A0 El (h A0 (List.mem_of_mem_take hA0)) W u hu

/-- A variadic signature with an element rest admits, at one budget, every
list a fixed one admits when its fixed parameters come first, pointwise wider,
and the fixed one's further positions are within the rest's element. -/
theorem rest_short {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop} {j : Nat}
    (hr : ∀ a b, R a b → FamLeAt G η a b j) {W : WorldT j} {E El : List ι}
    (hel : restElem G E = some El) :
    ∀ {Ps As : List (List ι)} {args : List Tm}, Domains R (As.take Ps.length) Ps →
      (∀ A ∈ As.drop Ps.length, R A El) →
      ArgsShort (As.map (mixedValues G η)) j W args →
      ArgsRest (Ps.map (mixedValues G η)) (mixedArgs G η E) j W args
  | [], As, args, _, hd, h => by
    rw [List.map_nil, ArgsRest_nil_params]
    exact (mixed_restElem hel).mpr (short_all_le hr (by simpa using hd) h.2.1)
  | _ :: _, [], _, hd, _, _ => hd.elim
  | P :: Ps, A :: As, [], hd, hd', h => by
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons] at hd hd'
    simp only [List.map_cons, ArgsShort_nil_args, ArgsRest_nil_args, List.mem_cons,
      forall_eq_or_imp] at h ⊢
    have := rest_short hr hel (args := []) hd.2 hd' (ArgsShort_nil_args.mpr h.2)
    rw [ArgsRest_nil_args] at this
    exact ⟨⟨hr A P hd.1 W _ h.1, this.1⟩, this.2⟩
  | P :: Ps, A :: As, a :: args, hd, hd', h => by
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons] at hd hd'
    simp only [List.map_cons, ArgsShort_cons, ArgsRest_cons] at h ⊢
    exact ⟨hr A P hd.1 W a h.1, rest_short hr hel hd.2 hd' h.2⟩

/-- A variadic signature admits, at one budget, every list a narrower variadic
signature admits: fixed positions pointwise wider, the narrower one's further
fixed positions taken into its rest, and its rest within the rest. -/
theorem rest_rest {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop} {j : Nat}
    (hr : ∀ a b, R a b → FamLeAt G η a b j) {W : WorldT j} {E F : List ι}
    (hfe : ∀ (W : WorldT j) vs, mixedArgs G η F j W vs → mixedArgs G η E j W vs) :
    ∀ {Ps Qs : List (List ι)} {args : List Tm}, Domains R (Qs.take Ps.length) Ps →
      IntoRest (restElem G) R (Qs.drop Ps.length) E →
      ArgsRest (Qs.map (mixedValues G η)) (mixedArgs G η F) j W args →
      ArgsRest (Ps.map (mixedValues G η)) (mixedArgs G η E) j W args
  | [], Qs, args, _, hin, h => by
    rw [List.map_nil, ArgsRest_nil_params]
    simp only [ArgsRest, List.length_map] at h
    obtain ⟨hs, hf⟩ := h
    have hE := hfe W _ hf
    simp only [List.length_nil, List.drop_zero] at hin
    rcases hin with rfl | hin
    · simpa using hE
    · unfold ElemRest at hin
      split at hin
      · rename_i El hel
        rw [← List.take_append_drop Qs.length args]
        exact mixed_restElem_append hel (short_all_le hr hin hs.2.1) hE
      · exact hin.elim
  | _ :: _, [], _, hd, _, _ => hd.elim
  | P :: Ps, Q :: Qs, [], hd, hin, h => by
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons] at hd hin
    simp only [List.map_cons, ArgsRest_nil_args, List.mem_cons, forall_eq_or_imp] at h ⊢
    have := rest_rest hr hfe (args := []) hd.2 hin (ArgsRest_nil_args.mpr ⟨h.1.2, h.2⟩)
    rw [ArgsRest_nil_args] at this
    exact ⟨⟨hr Q P hd.1 W _ h.1.1, this.1⟩, this.2⟩
  | P :: Ps, Q :: Qs, a :: args, hd, hin, h => by
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons] at hd hin
    simp only [List.map_cons, ArgsRest_cons] at h ⊢
    exact ⟨hr Q P hd.1 W a h.1, rest_rest hr hfe hd.2 hin h.2⟩

/-- A variadic signature `(receiver, fixed, rest, result)` covers a fixed
target `(Rt, As, d)` when the target's receiver is within its receiver, the
target's first positions are within its fixed parameters, its rest is an
element rest with its further positions within the element, and its result
within the target's. -/
@[nospecialize] def RestFixed (elem : List ι → Option (List ι)) (R : List ι → List ι → Prop)
    (s : RestArrow (List ι)) (q : Arrow (List ι)) : Prop :=
  R q.receiver s.receiver ∧ Domains R (q.arguments.take s.arguments.1.length) s.arguments.1 ∧
    ElemRest elem R (q.arguments.drop s.arguments.1.length) s.arguments.2 ∧
    (s.result = [] ∨ R s.result q.result) ∧ s.effect.covers q.effect = true

/-- One variadic signature covers another: input contracts are contravariant,
results covariant, and the source must supply the target's effect. -/
@[nospecialize] def RestCovers (elem : List ι → Option (List ι)) (R : List ι → List ι → Prop)
    (p q : RestArrow (List ι)) : Prop :=
  R q.receiver p.receiver ∧ Domains R (q.arguments.1.take p.arguments.1.length) p.arguments.1 ∧
    IntoRest elem R (q.arguments.1.drop p.arguments.1.length) p.arguments.2 ∧
    R q.arguments.2 p.arguments.2 ∧ R p.result q.result ∧ p.effect.covers q.effect = true

/-- Declarative overload coverage. Every recursive obligation carries the
complete target signature, so splitting domains cannot lose its effect.
Combining result guarantees must also establish the target effect. -/
inductive CallArrow (compat : ι → ι → Bool) (elem : List ι → Option (List ι))
    (R : List ι → List ι → Prop) (L : List (Arrow (List ι))) (S : List (RestArrow (List ι))) :
    Arrow (List ι) → Prop where
  | emptyRecv : q.receiver = [] → CallArrow compat elem R L S q
  | empty : [] ∈ q.arguments → CallArrow compat elem R L S q
  | source : p ∈ L → R q.receiver p.receiver → Domains R q.arguments p.arguments →
      (p.result = [] ∨ R p.result q.result) → p.effect.covers q.effect = true →
      CallArrow compat elem R L S q
  | rest : s ∈ S → RestFixed elem R s q → CallArrow compat elem R L S q
  | union : q.arguments = pre ++ (a ++ b) :: suffix →
      CallArrow compat elem R L S { q with arguments := pre ++ a :: suffix } →
      CallArrow compat elem R L S { q with arguments := pre ++ b :: suffix } →
      CallArrow compat elem R L S q
  | recvUnion : q.receiver = a ++ b →
      CallArrow compat elem R L S { q with receiver := a } →
      CallArrow compat elem R L S { q with receiver := b } → CallArrow compat elem R L S q
  | combine : CallArrow compat elem R L S { q with result := b, effect := e } →
      CallArrow compat elem R L S { q with result := b', effect := e' } →
      (∀ i ∈ b, ∀ k ∈ b', compat i k = true → R [i] q.result) →
      (e.meet e').covers q.effect = true → CallArrow compat elem R L S q

/-- An arrow's source result within the target's, or empty. -/
theorem arrow_result {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop} {n : Nat} {r d : List ι}
    (hr : ∀ j, j < n → ∀ a b, R a b → FamLeAt G η a b j) (hc : r = [] ∨ R r d) :
    ∀ m, m < n → ∀ (V : WorldT m) u, mixedValues G η r m V u → mixedValues G η d m V u := by
  intro m hm V u hu
  rcases hc with he | he
  · obtain ⟨i, hi, _⟩ := hu; simp [he] at hi
  · exact hr m hm _ _ he V u hu

theorem CallArrow.sound {G : NormalGraph ι} {η : MixedAssignment ι} {R L S q}
    (hc : CallArrow (compatible G) (restElem G) R L S q) (n : Nat)
    (hr : ∀ j, j < n → ∀ a b, R a b → FamLeAt G η a b j)
    (W : WorldT n) (v : Val)
    (hv : CallEffects.callsT Ξ (L.map (Arrow.map (mixedValues G η))) n W v ∧
      CallEffects.restsT Ξ (S.map (RestArrow.mapWith (mixedValues G η) (mixedArgs G η))) n W v) :
    PromiseWith Ξ q.effect (ArgsShort (q.arguments.map (mixedValues G η)))
      (mixedValues G η q.receiver) (mixedValues G η q.result) n W v := by
  induction hc with
  | emptyRecv he =>
    intro j hj U hx hu heap hh r hrv hrm
    obtain ⟨i, hi, _⟩ := hrm
    simp [he] at hi
  | empty he =>
    intro j hj U hx hu heap hh r hrv hrm args hvals ha
    exact False.elim (short_empty he ha)
  | source hm hrecv hd hres he =>
    exact (hv.1.2 _ (List.mem_map_of_mem hm)).weaken (Effect.covers_sound he)
      (fun j hj U r hrm => hr j hj _ _ hrecv U r hrm)
      (fun j hj U args ha => Domains.short (hr j hj) hd ha) (arrow_result hr hres)
  | rest hs hrf =>
    obtain ⟨hrecv, hd, hel, hres, he⟩ := hrf
    unfold ElemRest at hel
    split at hel
    · rename_i El hE
      exact (hv.2.2 _ (List.mem_map_of_mem hs)).weaken (Effect.covers_sound he)
        (fun j hj U r hrm => hr j hj _ _ hrecv U r hrm)
        (fun j hj U args ha => rest_short (hr j hj) hE hd hel ha) (arrow_result hr hres)
    · exact hel.elim
  | union he _ _ hl hh =>
    intro j hj U hx hu heap hok r hrv hrm args hvals ha
    rw [he] at ha
    rcases short_union _ _ _ _ ha with ha | ha
    · exact hl j hj U hx hu heap hok r hrv hrm args hvals ha
    · exact hh j hj U hx hu heap hok r hrv hrm args hvals ha
  | recvUnion he _ _ hl hh =>
    intro j hj U hx hu heap hok r hrv hrm args hvals ha
    obtain ⟨i, hi, hvi⟩ := hrm
    rw [he] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hl j hj U hx hu heap hok r hrv ⟨i, hi, hvi⟩ args hvals ha
    · exact hh j hj U hx hu heap hok r hrv ⟨i, hi, hvi⟩ args hvals ha
  | combine _ _ hg he hl hh =>
    have combined := hl.combine hh (fun j hj r hb V V' heap h1 h2 u hv1 hv2 => by
      obtain ⟨i, hi, hv1⟩ := hv1
      obtain ⟨k, hk, hv2⟩ := hv2
      exact hr r (by omega) _ _ (hg i hi k hk (mixed_compatible hv1 hv2)) V u
        ⟨i, by simp, hv1⟩)
    exact combined.weaken (Effect.covers_sound he)
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)

theorem rest_covers_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {p q : RestArrow (List ι)} (hc : RestCovers (restElem G) R p q) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (W : WorldT n) (v : Val)
    (hv : PromiseWith Ξ p.effect (ArgsRest (p.arguments.1.map (mixedValues G η)) (mixedArgs G η p.arguments.2))
      (mixedValues G η p.receiver) (mixedValues G η p.result) n W v) :
    PromiseWith Ξ q.effect (ArgsRest (q.arguments.1.map (mixedValues G η)) (mixedArgs G η q.arguments.2))
      (mixedValues G η q.receiver) (mixedValues G η q.result) n W v := by
  obtain ⟨hrecv, hd, hel, he, hres, heffect⟩ := hc
  exact hv.weaken (Effect.covers_sound heffect) (fun j hj U r hrm => hr j hj _ _ hrecv U r hrm)
    (fun j hj U args ha => rest_rest (hr j hj) (hpa j hj _ _ he) hd hel ha)
    (fun m hm U u hu => hr m hm _ _ hres U u hu)

/-- One record conjunction covers another when every field any target operand
names is named by some source operand, with contracts that imply each other.
Fields the target does not name are not compared: a record type is open, so
covering never requires the source to forget a field. -/
abbrev CoversFields (R : List ι → List ι → Prop)
    (source target : List (List (PropKey × List ι))) : Prop :=
  ∀ b ∈ target, ∀ q ∈ b, ∃ p ∈ source.flatten, p.1 = q.1 ∧ R p.2 q.2 ∧ R q.2 p.2

/-- A type holding every number: one of its clauses is the number family. -/
@[nospecialize] def numIn (G : NormalGraph ι) (T : List ι) : Bool :=
  (expand G T).any fun c => match c with | .num => true | _ => false

theorem numIn_sound {G : NormalGraph ι} {T : List ι} (h : numIn G T = true) (η : MixedAssignment ι)
    {j : Nat} {W : WorldT j} (b : UInt64) : mixedValues G η T j W (.num b) := by
  obtain ⟨c, hc, hs⟩ := List.any_eq_true.mp h
  cases c <;> simp only [Bool.false_eq_true] at hs
  exact mixed_expand_mpr ⟨.num, expand_sub hc, ⟨b, rfl⟩, builtinInvariant_of_withoutInvariant rfl _ _ _⟩

/-- A view field is covered by a source field of the same name whose contract
implies it: an invariant field or a view, either way a sound upper bound. -/
abbrev CoversViews (G : NormalGraph ι) (R : List ι → List ι → Prop)
    (source : List (List (PropKey × List ι))) (views target : List (PropKey × List ι)) : Prop :=
  ∀ q ∈ target, (∃ p ∈ source.flatten ++ views, p.1 = q.1 ∧ R p.2 q.2) ∨
    (q.1 = lengthKey ∧ ((source.flatten ++ views).any (·.1 == arrayStoreKey) && numIn G q.2) = true)

/-- A class value's readonly static field is covered by a source static
field or readonly static field of the same name whose contract implies it. -/
abbrev CoversBagViews (R : List ι → List ι → Prop)
    (source : List (List (PropKey × List ι))) (views target : List (PropKey × List ι)) : Prop :=
  ∀ q ∈ target, ∃ p ∈ source.flatten ++ views, p.1 = q.1 ∧ R p.2 q.2

/-- A key some bound excludes: no object under the bounds owns it. -/
abbrev Excludes (bounds : List KeyBound) (k : PropKey) : Prop := ∃ K ∈ bounds, K.admits k = false

/-- The source slots that can cover an optional field: invariant fields,
views, which are readonly, and optional fields with their own flag. -/
@[nospecialize] def optionalSources (source : List (List (PropKey × List ι))) (views : List (PropKey × List ι))
    (optional : List (OptionalField (List ι))) : List (OptionalField (List ι)) :=
  source.flatten.map (fun p => ⟨p.1, false, p.2⟩) ++
    (views.filter (·.1 != lengthKey)).map (fun p => ⟨p.1, true, p.2⟩) ++ optional

/-- An optional field is covered by a source slot of the same key: an
invariant field, a view or an optional field. Its type is within the target's;
a writable target also needs an equivalent type and a writable slot, so no
location is retyped. Where the object lacks the key, only an optional source
field allows it, and that field says the object has no prototype. Key
bounds of the source excluding both the key and the prototype key cover it
too: the object lacks the key and has no prototype, so every read of it is
`undefined`. Neither a view nor an optional source field covers a required
target field, since neither says the key is present. -/
abbrev CoversOptional (R : List ι → List ι → Prop)
    (source : List (List (PropKey × List ι))) (views : List (PropKey × List ι))
    (optional : List (OptionalField (List ι))) (bounds : List KeyBound)
    (target : List (OptionalField (List ι))) : Prop :=
  ∀ q ∈ target, (∃ p ∈ optionalSources source views optional, p.key = q.key ∧
    (q.readonly = false → p.readonly = false) ∧ R p.type q.type ∧
    (q.readonly = false → R q.type p.type)) ∨
    Excludes bounds q.key ∧ Excludes bounds CallArguments.protoField

/-- A meet row's clauses: what its parameter is intersected with. -/
@[nospecialize] def meetClauses (G : NormalGraph ι) (i : ι) : List (Clause (List ι)) :=
  ((G.meets i).map (·.2)).getD []

/-- A meet row's parts other than its clauses: its parameters and, in an
equation graph, its scheme parts (RECURSIVE-EQUATIONS §3.3). -/
@[nospecialize] def meetParts (G : NormalGraph ι) (i : ι) : List ι :=
  match G.meets i with
  | some (p, _) => p :: G.meetParams i
  | none => []

theorem meetParts_of {G : NormalGraph ι} {i p : ι} {cs : List (Clause (List ι))}
    (h : G.meets i = some (p, cs)) : meetParts G i = p :: G.meetParams i := by
  simp [meetParts, h]

/-- The rows a row reads: a clause row its operands, a scheme row its
signatures' rows, a meet row its clauses' operands. -/
@[nospecialize] def reads (G : NormalGraph ι) (i : ι) : List ι :=
  match G.schemes i with
  | some s => s.signatures.flatMap (fun p => p.operands.flatten) ++
      s.bounds.flatMap (·.2) ++
      s.variadic.flatMap (fun p => p.operands.flatten)
  | none => (G i ++ meetClauses G i).flatMap fun c => c.operands.flatten

/-- A scheme row's bound types: read at its own assignment, not under its
binders. -/
@[nospecialize] def boundReads (G : NormalGraph ι) (i : ι) : List ι :=
  match G.schemes i with
  | some s => s.bounds.flatMap (·.2)
  | none => []

/-! ### Free parameter rows -/

abbrev FreeMap (ι : Type) := List (ι × List ι)

/-- The parameter rows a row may depend on, as a certificate states them. -/
@[nospecialize] def fv [DecidableEq ι] (V : FreeMap ι) (i : ι) : List ι := (V.lookup i).getD []

/-- `V` over-approximates the free parameter rows of the rows of `D`, which is
closed under what its rows read: a parameter row is free in itself, and a row
reading another has that row's free parameters, except a scheme row's own
binders. A meet row depends on its parameter parts, and on its other parts'
free rows. -/
@[nospecialize] def FreeOk [DecidableEq ι] (G : NormalGraph ι) (D : List ι) (V : FreeMap ι) : Bool :=
  D.all fun i =>
    (!G.params i || (fv V i).contains i) &&
    (meetParts G i).all (fun q => if G.params q then (fv V i).contains q else
      D.contains q && (fv V q).all (fv V i).contains) &&
    (reads G i).all (fun l => D.contains l &&
      (fv V l).all fun p => (fv V i).contains p ||
        (match G.schemes i with | some s => s.binders.contains p | none => false)) &&
    (boundReads G i).all fun l => (fv V l).all fun p => (fv V i).contains p

/-- `FreeOk` with each row's free rows looked up once, not once per read: what
the compiler runs. -/
@[nospecialize] def FreeOkFast [DecidableEq ι] (G : NormalGraph ι) (D : List ι) (V : FreeMap ι) : Bool :=
  D.all fun i =>
    let fi := fv V i
    (!G.params i || fi.contains i) &&
    (meetParts G i).all (fun q => if G.params q then fi.contains q else
      D.contains q && (fv V q).all fi.contains) &&
    (reads G i).all (fun l => D.contains l &&
      (fv V l).all fun p => fi.contains p ||
        (match G.schemes i with | some s => s.binders.contains p | none => false)) &&
    (boundReads G i).all fun l => (fv V l).all fun p => fi.contains p

@[csimp] theorem FreeOk_eq_fast : @FreeOk = @FreeOkFast := rfl

/-- The rows `S` reads, transitively, without repeats, in the order they are
first reached. Only the rows added by the last step are read again: the rows
before them have had their reads added already, so each row is read once. -/
@[nospecialize] def readsFrom [DecidableEq ι] (G : NormalGraph ι) (fuel : Nat) (S : List ι) : List ι :=
  let S := S.eraseDups
  go fuel S S
where
  go : Nat → List ι → List ι → List ι
  | 0, seen, _ => seen
  | fuel + 1, seen, frontier =>
    let fresh := (frontier.flatMap (reads G)).foldl (fun acc l =>
      if seen.contains l || acc.contains l then acc else l :: acc) []
    if fresh.isEmpty then seen else go fuel (seen ++ fresh.reverse) fresh.reverse

/-- The free parameter rows of the rows of `D`, by iteration to a fixed point:
a parameter row is free in itself, and a row has the free rows of what it
reads, except a scheme row's own binders. Untrusted: `FreeOk` checks it. -/
@[nospecialize] def freeMapOf [DecidableEq ι] (G : NormalGraph ι) (D : List ι) : Nat → FreeMap ι → FreeMap ι
  | 0, V => V
  | fuel + 1, V =>
    let step (i : ι) : List ι :=
      let bound := match G.schemes i with
        | some s => s.binders
        | none => []
      ((if G.params i then [i] else []) ++
        (meetParts G i).flatMap (fun q => if G.params q then [q] else fv V q) ++ fv V i ++
        (reads G i).flatMap fun l => (fv V l).filter (fun p => !bound.contains p)).eraseDups
    let V' := D.map fun i => (i, step i)
    if D.all (fun i => (fv V' i).length == (fv V i).length) then V' else freeMapOf G D fuel V'

/-- How far to follow a graph's rows. -/
def closureFuel : Nat := 4096


/-- A method signature covers another of the same key: each fixed target
signature is covered by a fixed source one taking as many parameters, each at
least as wide, with a result at most as wide; each variadic target signature
by a variadic source one, its further fixed parameters taken into the source's
rest, its rest within the source's and results covariant. The receiver is the
host on both sides, so receivers are not compared; each type the source's
host must meet is met by the target's host, being within one the target's
must meet. -/
@[nospecialize] def CoversSig (elem : List ι → Option (List ι)) (R : List ι → List ι → Prop)
    (p q : MethodMembers.Sig (List ι)) : Prop :=
  (∀ t ∈ q.calls, ∃ s ∈ p.calls, Domains R t.arguments s.arguments ∧ R s.result t.result ∧ s.effect.covers t.effect = true) ∧
  (∀ t ∈ q.rests, ∃ s ∈ p.rests, Domains R (t.arguments.1.take s.arguments.1.length) s.arguments.1 ∧
    IntoRest elem R (t.arguments.1.drop s.arguments.1.length) s.arguments.2 ∧ R t.arguments.2 s.arguments.2 ∧ R s.result t.result ∧ s.effect.covers t.effect = true) ∧
  (∀ t ∈ q.schemes, ∃ s ∈ p.schemes, R s t) ∧
  ∀ T ∈ p.receivers, ∃ T' ∈ q.receivers, R T' T

/-- A method signature is covered by a function the source object holds in a
field or view: each target signature by one of the function's taking at least
as wide parameters and giving an at most as wide result, whose receiver the
object's own type `self`, or a type the target's host must meet, is within.
Invoked on the object, such a function behaves as typed, so it meets the
host-relative member. -/
@[nospecialize] def CoversArrows (G : NormalGraph ι) (R : List ι → List ι → Prop) (self : List ι)
    (L : Ops ι) (S : List (RestArrow (List ι)))
    (q : MethodMembers.Sig (List ι)) : Prop :=
  q.schemes = [] ∧ (∀ t ∈ q.calls, ∃ s ∈ L, (R self s.receiver ∨ ∃ T ∈ q.receivers, R T s.receiver) ∧
    Domains R t.arguments s.arguments ∧ R s.result t.result ∧ s.effect.covers t.effect = true) ∧
  (∀ t ∈ q.rests, ∃ s ∈ S, (R self s.receiver ∨ ∃ T ∈ q.receivers, R T s.receiver) ∧
    Domains R (t.arguments.1.take s.arguments.1.length) s.arguments.1 ∧
    IntoRest (restElem G) R (t.arguments.1.drop s.arguments.1.length) s.arguments.2 ∧ R t.arguments.2 s.arguments.2 ∧ R s.result t.result ∧ s.effect.covers t.effect = true)

/-- The receivers of a scheme's signatures. -/
@[nospecialize] def schemeReceivers (s : SchemeRow ι) : List ι :=
  s.signatures.flatMap (·.receiver) ++ s.variadic.flatMap (·.receiver)

/-- A type reads none of the rows `bs`: a checked free map of the rows it
reaches gives none of them (`FreeOk`), so it means the same at every
reassignment of them (`bindersFree_values`). -/
@[nospecialize] def bindersFree [DecidableEq ι] (G : NormalGraph ι) (bs : List ι) (A : List ι) : Bool :=
  let D := readsFrom G closureFuel A
  let V := freeMapOf G D closureFuel []
  FreeOk G D V && A.all fun l => D.contains l && (fv V l).all fun p => !bs.contains p

/-- Simultaneous replacement of the parameters a context names; any other
row stands for itself. -/
@[nospecialize] def replace [DecidableEq ι] (σ : List (ι × List ι)) (p : ι) : List ι := (σ.lookup p).getD [p]

/-- Syntactic substitution and free support for a graph's types, with the
semantic laws that justify them, and the rows reserved for family
variables. Supplied by verified code for a representation (equation graphs
have one), never by a certificate; the finite graph has none, so its
checks rename no binder and use no variable. -/
structure Renaming [DecidableEq ι] (G : NormalGraph ι) where
  substitute : List (ι × List ι) → List ι → List ι
  free : List ι → List ι
  /-- Rows that may be family variables. -/
  familyVar : ι → Bool
  /-- Whether a type mentions a row anywhere in its syntax. -/
  mentions : List ι → ι → Bool
  substitute_meaning : ∀ (η θ : MixedAssignment ι) (σ : List (ι × List ι)),
    (∀ p, G.params p = true → mixedMeaning G η [p] = mixedMeaning G θ (replace σ p)) →
    ∀ A, mixedMeaning G η A = mixedMeaning G θ (substitute σ A)
  agree_free : ∀ (η θ : MixedAssignment ι) (A : List ι), (∀ p ∈ free A, η.1 p = θ.1 p) →
    mixedMeaning G η A = mixedMeaning G θ A
  familyVar_param : ∀ x, familyVar x = true → G.params x = true
  /-- No scheme binds a variable, so entering one keeps the hypotheses. -/
  familyVar_unbound : ∀ i s x, G.schemes i = some s → familyVar x = true → x ∉ s.binders
  /-- A label's size: an application's arguments are smaller than it
  (`Inst`'s premises decrease). No law: the checker compares sizes it computes. -/
  size : ι → Nat
  /-- The renaming of bound rows that carries a table pair to another pair,
  proposed by matching (`TabRen`). No law: the checker checks what it proposes. -/
  rename : List ι × List ι → List ι → List ι → List (ι × List ι)
  /-- The definition a label applies, if any. Search only: evidence search
  tells a pair recurring with growing arguments by it. -/
  head : ι → Option Nat := fun _ => none

/-- Signatures `L`, `M` a scheme's received by the host cover, receivers
aside (both are the host's: the bound function's is any, `s`'s is the host,
which `CoversByScheme` checks): each is covered by one of `s`'s. -/
@[nospecialize] def BoundSigsCover (G : NormalGraph ι) (R : List ι → List ι → Prop) (s : SchemeRow ι)
    (L : Ops ι) (M : List (RestArrow (List ι))) : Prop :=
  (∀ t ∈ L, ∃ p ∈ s.signatures, Domains R t.arguments p.arguments ∧ R p.result t.result ∧ p.effect.covers t.effect = true) ∧
  (∀ t ∈ M, ∃ p ∈ s.variadic, Domains R (t.arguments.1.take p.arguments.1.length) p.arguments.1 ∧
    IntoRest (restElem G) R (t.arguments.1.drop p.arguments.1.length) p.arguments.2 ∧ R t.arguments.2 p.arguments.2 ∧
    R p.result t.result ∧ p.effect.covers t.effect = true)

/-- The renaming of a target scheme's binders `qs` to a source scheme's `ps`,
as a substitution. -/
@[nospecialize] def renamingOf (ps qs : List ι) : List (ι × List ι) := qs.zip (ps.map fun p => [p])

/-- A target quantified signature `S'` a scheme `s` received by the host
covers (`BoundSigsCover`): `S'` binds `s`'s rows, each bound of `s` among
`S'`'s; or, up to renaming (quantified-α, RECURSIVE-EQUATIONS §4.1), `S'`
binds as many distinct rows of the same kinds, each bound of `s` matched by
`S'`'s bound on the renamed binder, which is within it, no binder of `s`
free in `S'`'s signatures but as a binder of `S'`, and `s`'s signatures
cover `S'`'s with its binders renamed to `s`'s. The renaming is the
checker's own substitution (`sub`), never a certificate's. -/
@[nospecialize] def SchemeBinds [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G))
    (R : List ι → List ι → Prop) (s : SchemeRow ι) (S' : List ι) : Prop :=
  match S' with
  | [j] => match G.schemes j with
    | some s' => G.params j = false ∧ s'.construct = false ∧ sameShape s s' = true ∧
      ((s.binders = s'.binders ∧ (∀ b ∈ s.bounds, b ∈ s'.bounds) ∧
          BoundSigsCover G R s s'.signatures s'.variadic) ∨
        match sub with
        | some r =>
          s.binders.length = s'.binders.length ∧ s.binders.Nodup ∧ s'.binders.Nodup ∧
          (∀ pq ∈ s.binders.zip s'.binders, G.parameterKinds pq.1 = G.parameterKinds pq.2) ∧
          (∀ b ∈ s.bounds, ∃ b' ∈ s'.bounds,
            (s.binders.zip s'.binders).lookup b.1 = some b'.1 ∧ R b'.2 b.2) ∧
          (∀ A ∈ (Clause.arrs s'.signatures s'.variadic).operands, ∀ x ∈ r.free A,
            x ∈ s.binders → x ∈ s'.binders) ∧
          BoundSigsCover G R s
            (s'.signatures.map (Arrow.map (r.substitute (renamingOf s.binders s'.binders))))
            (s'.variadic.map (RestArrow.map (r.substitute (renamingOf s.binders s'.binders))))
        | none => False)
    | none => False
  | _ => False

/-- A generic function the source holds, a scheme received by the host (a
class's generic method on its prototype, received by the instance), covering a
target member of quantified signatures: the source type is within each of the
scheme's receivers, which read none of its binders, so the host is in them at
every instance; bound to the host, the function meets each of the target's
schemes it binds as (`SchemeBinds`). -/
@[nospecialize] def CoversByScheme [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G))
    (R : List ι → List ι → Prop) (self : List ι)
    (F : List ι) (q : MethodMembers.Sig (List ι)) : Prop :=
  match F with
  | [i] => match G.schemes i with
    | some s => s.construct = false ∧ q.calls = [] ∧ q.rests = [] ∧ G.params i = false ∧
        bindersFree G s.binders (schemeReceivers s) = true ∧
        (∀ r ∈ s.signatures.map (·.receiver) ++ s.variadic.map (·.receiver), R self r) ∧
        ∀ S' ∈ q.schemes, SchemeBinds G sub R s S'
    | none => False
  | _ => False

/-- The same, for a function type: its one arrow clause, or a scheme received
by the host. -/
@[nospecialize] def CoversByFunction [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (R : List ι → List ι → Prop) (self : List ι)
    (F : List ι) (q : MethodMembers.Sig (List ι)) : Prop :=
  match expand G F with
  | [.arrs L S] => CoversArrows G R self L S q
  | _ => CoversByScheme G sub R self F q

/-- The field or view a type's one record clause holds under a key. -/
@[nospecialize] def viewOf (G : NormalGraph ι) (P : List ι) (k : PropKey) : Option (List ι) :=
  match expand G P with
  | [.refs a bs vs _ _ _] => (((a :: bs).flatten ++ vs.filter (·.1 != lengthKey)).find? (·.1 == k)).map (·.2)
  | _ => none

/-- Whether a type's one record clause has an own-key bound excluding a key:
its members lack it. -/
@[nospecialize] def lacksKey (G : NormalGraph ι) (P : List ι) (k : PropKey) : Prop :=
  match expand G P with
  | [.refs _ _ _ _ _ ks] => Excludes ks k
  | _ => False

/-- A prototype type holds a method signature's key at a field or view that
covers it with the object as receiver: a known row below arrows covering it
(typically a generic prototype member and its instance at the array's element
type: `Array.prototype[Symbol.iterator]` at `number`), or a function type
covering it, as `CoversByFunction`. -/
@[nospecialize] def FoundOn [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (R : List ι → List ι → Prop) (known : Known ι)
    (self : List ι) (q : MethodMembers.Sig (List ι)) (P : List ι) : Prop :=
  (∃ k ∈ known, viewOf G P q.key = some k.1 ∧ CoversArrows G R self k.2.1 k.2.2 q) ∨
    ∃ F ∈ (viewOf G P q.key).toList, CoversByFunction G sub R self F q

/-- A method signature is found along a prototype chain from prototype type
`P`, at most `d` further prototypes up: on `P` itself (`FoundOn`), or, where
`P`'s key bound excludes the key, along the prototype `P`'s own prototype
field or view holds. JavaScript's lookup does the same. -/
@[nospecialize] def ProtoHolds [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (R : List ι → List ι → Prop) (known : Known ι)
    (self : List ι) (q : MethodMembers.Sig (List ι)) : Nat → List ι → Prop
  | 0, P => FoundOn G sub R known self q P
  | d + 1, P => FoundOn G sub R known self q P ∨ (lacksKey G P q.key ∧
      ∃ P' ∈ (viewOf G P CallArguments.protoField).toList, ProtoHolds G sub R known self q d P')

/-- How many prototypes up a method is looked for: a class hierarchy deeper
than this has its inherited methods refused, never wrongly admitted. -/
def protoChainDepth : Nat := 16

/-- A method signature is covered through the source's prototype chain: a key
bound of the source excludes the key (`Excludes`), so the object lacks it, and
its prototype field's type holds it, on that prototype or further up
(`ProtoHolds`). -/
@[nospecialize] def CoversByProto [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (R : List ι → List ι → Prop) (known : Known ι)
    (self : List ι) (fields : List (PropKey × List ι)) (bounds : List KeyBound)
    (q : MethodMembers.Sig (List ι)) : Prop :=
  Excludes bounds q.key ∧ ∃ f ∈ fields, f.1 = CallArguments.protoField ∧
    ProtoHolds G sub R known self q protoChainDepth f.2

/-- Every target method is covered by a source method of the same key, by a
function the source holds under that key whose receiver the source's own type
is within, or by such a function along its prototype chain. -/
abbrev CoversMethods [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (R : List ι → List ι → Prop) (known : Known ι)
    (self : List ι) (fields : List (PropKey × List ι)) (bounds : List KeyBound)
    (source target : List (MethodMembers.Sig (List ι))) : Prop :=
  ∀ q ∈ target, (∃ p ∈ source, p.key = q.key ∧ CoversSig (restElem G) R p q) ∨
    (∃ f ∈ fields, f.1 = q.key ∧ CoversByFunction G sub R self f.2 q) ∨
    CoversByProto G sub R known self fields bounds q

/-- Index contracts met through an own-key bound: the object's own keys are
among `K`, which lists no prototype key, so the object has no prototype; each
key of `K` an index's class may admit (`IndexKeys.may`) is a source field or
view whose contract implies that index view, and a source field whose contract
agrees with that writable index. No other key exists, so a fresh literal, whose
own keys are exactly its fields, is a dictionary of what its fields fit. A key
a class provably does not admit, such as `name` for a number index, needs
nothing of it. A bound excluding keys says nothing of the others, so it meets
no index. A writable index is met so only at an uninhabited contract, where
code holding it can add no key (`CoversWith`). -/
abbrev CoversKeys (R : List ι → List ι → Prop) (fields views : List (PropKey × List ι))
    (bounds : List KeyBound) (ix cx : List (IndexKeys × List ι)) : Prop :=
  ∃ K ∈ bounds, K.among = true ∧ CallArguments.protoField ∉ K.keys ∧ ∀ k ∈ K.keys,
    (∀ y ∈ ix, y.1.may k = true → ∃ p ∈ fields ++ views, p.1 = k ∧ R p.2 y.2) ∧
    ∀ y ∈ cx, y.1.may k = true → ∃ p ∈ fields, p.1 = k ∧ R p.2 y.2 ∧ R y.2 p.2

/-- A type with no member: plain rows naming no clause. A writable index at
such a contract admits no added key, since no value meets it. -/
abbrev Uninhabited (G : NormalGraph ι) (S : List ι) : Prop :=
  G.plainTy S = true ∧ (expand G S).isEmpty = true

/-- Every source bound keeps the keys of every writable target index whose
contract some value meets. -/
abbrev KeepsKeys (G : NormalGraph ι) (bounds : List KeyBound)
    (cells : List (IndexKeys × List ι)) : Prop :=
  ∀ y ∈ cells, Uninhabited G y.2 ∨ ∀ K ∈ bounds, K.keeps y.1 = true

/-- A target key bound follows from the source's bounds: every key they let
the object own, it admits. A target excluding keys needs each excluded by some
source bound; a target listing keys needs a source bound listing keys, each of
which the target lists or some source bound excludes. -/
def CoversBound (source : List KeyBound) (target : KeyBound) : Prop :=
  if target.among then
    ∃ K ∈ source, K.among = true ∧ ∀ k ∈ K.keys, k ∈ target.keys ∨ Excludes source k
  else ∀ k ∈ target.keys, Excludes source k

instance CoversBound.decidable (source : List KeyBound) (target : KeyBound) :
    Decidable (CoversBound source target) := by
  unfold CoversBound; infer_instance

/-- Every target key bound follows from the source's. -/
abbrev CoversBounds (source target : List KeyBound) : Prop :=
  ∀ K ∈ target, CoversBound source K

/-- A record's member is an object. -/
theorem recT_obj {fs : Fields} {n : Nat} {W : WorldT n} {v : Val} (h : recT fs n W v) :
    ∃ (flds : List (PropKey × Nat)) (oid : Nat), v = .objAt flds .absent oid := by
  obtain ⟨flds, oid, he, -⟩ := h
  exact ⟨flds, oid, he⟩

theorem covers_bounds_sound {source target : List KeyBound} (hc : CoversBounds source target)
    {n : Nat} {W : WorldT n} {v : Val} (hobj : ∃ (flds : List (PropKey × Nat)) (oid : Nat), v = .objAt flds .absent oid)
    (hv : ∀ K ∈ source, ownKeysT K n W v) :
    ∀ K ∈ target, ownKeysT K n W v := by
  obtain ⟨flds, oid, rfl⟩ := hobj
  -- A key some source bound excludes is not the object's own.
  have excluded : ∀ {k}, Excludes source k → ∀ p ∈ flds, p.1 ≠ k := by
    rintro k ⟨K, hK, hk⟩ p hp rfl
    obtain ⟨flds', oid', he, hall⟩ := hv K hK
    cases he
    have := hall p hp
    simp_all
  intro T hT
  have hc := hc T hT
  unfold CoversBound at hc
  refine ⟨flds, oid, rfl, fun p hp => ?_⟩
  split at hc
  · rename_i hamong
    obtain ⟨K, hK, hKa, hsub⟩ := hc
    obtain ⟨flds', oid', he, hk⟩ := hv K hK
    cases he
    have hp' := hk p hp
    simp only [KeyBound.admits, hKa, beq_true, List.contains_iff_mem] at hp'
    rcases hsub p.1 hp' with h | h
    · simp [KeyBound.admits, hamong, h]
    · exact absurd rfl (excluded h p hp)
  · rename_i hamong
    simp only [Bool.not_eq_true] at hamong
    simp only [KeyBound.admits, hamong]
    cases hm : T.keys.contains p.1
    · rfl
    · exact absurd rfl (excluded (hc p.1 (by simpa using hm)) p hp)

/-- Two rest contracts agree: both absent, or both present and equivalent. -/
@[nospecialize] def CoversRest (R : List ι → List ι → Prop) (readonly : Bool) : Option (List ι) → Option (List ι) → Prop
  | none, none => True
  | some x, some y => R x y ∧ (readonly = false → R y x)
  | _, _ => False

/-- Same-shape tuple contracts compare element read types covariantly for a
readonly target. A writable target needs a writable source and equivalent
element contracts; no location is retyped. -/
@[nospecialize] def CoversShape (R : List ι → List ι → Prop) (p q : Tuple (List ι)) : Prop :=
  p.required.length = q.required.length ∧ p.optional.length = q.optional.length ∧
  (∀ x ∈ p.required.zip q.required, R x.1 x.2 ∧ (q.readonly = false → R x.2 x.1)) ∧
  (∀ x ∈ p.optional.zip q.optional, R x.1 x.2 ∧ (q.readonly = false → R x.2 x.1)) ∧
  CoversRest R q.readonly p.rest q.rest ∧ (q.readonly = false → p.readonly = false)

/-- A fixed construct signature `(Ps, B)` covers a variadic one `(Qs, P, D)`
whose rest is one exact tuple: its fixed parameters, then the tuple's
positions, are within the source's parameters, and the source's result is
within the target's. An exact tuple holds its actuals at their positions at the
current level, whatever the positions' types. -/
@[nospecialize] def FixedCoversPack (G : NormalGraph ι) (R : List ι → List ι → Prop)
    (p : List (List ι) × List ι) (t : List (List ι) × List ι × List ι) : Prop :=
  match expand G t.2.1 with
  | [.pack τ []] => τ.optional = [] ∧ τ.rest = none ∧
      Domains R (t.1 ++ τ.required) p.1 ∧ R p.2 t.2.2
  | _ => False

/-- A fixed call signature `(Rc, Ps, B)` covers a variadic one `(Rt, Qs, P, D)`
whose rest is one exact tuple: the target's receiver is
within the source's, its fixed parameters, then the tuple's positions, are
within the source's parameters, and results are covariant. -/
@[nospecialize] def FixedCallsPack (G : NormalGraph ι) (R : List ι → List ι → Prop)
    (p : Arrow (List ι)) (t : RestArrow (List ι)) : Prop :=
  match expand G t.arguments.2 with
  | [.pack τ []] => τ.optional = [] ∧ τ.rest = none ∧
      R t.receiver p.receiver ∧ Domains R (t.arguments.1 ++ τ.required) p.arguments ∧ R p.result t.result ∧ p.effect.covers t.effect = true
  | _ => False

/-- A fixed signature meets a variadic one whose rest is an exact tuple: at
every level the list's actuals are at their positions, so the call is one the
fixed signature admits. -/
theorem fixed_calls_pack_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {p : Arrow (List ι)} {t : RestArrow (List ι)}
    (hc : FixedCallsPack G R p t) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (W : WorldT n) (v : Val)
    (hv : PromiseWith Ξ p.effect (ArgsShort (p.arguments.map (mixedValues G η))) (mixedValues G η p.receiver) (mixedValues G η p.result) n W v) :
    PromiseWith Ξ t.effect (ArgsRest (t.arguments.1.map (mixedValues G η)) (mixedArgs G η t.arguments.2)) (mixedValues G η t.receiver)
      (mixedValues G η t.result) n W v := by
  unfold FixedCallsPack at hc
  split at hc
  · rename_i τ hP
    obtain ⟨hopt, hrest, hrecv, hd, hres, heff⟩ := hc
    intro j hj U hx hu heap hh r hrv hrm args hvals ha
    obtain ⟨hshort, hpack⟩ := ha
    simp only [List.length_map] at hshort hpack
    have htup := mixed_pack_exact hP hopt hrest hpack
    have hall : ArgsShort ((t.arguments.1 ++ τ.required).map (mixedValues G η)) j U args := by
      by_cases hl : args.length ≤ t.arguments.1.length
      · rw [List.drop_eq_nil_of_le hl] at htup
        have hreq : τ.required = [] := List.eq_nil_of_length_eq_zero (by
          have := ArgsT_length htup
          simp at this
          omega)
        rw [hreq, List.append_nil]
        rwa [List.take_of_length_le hl] at hshort
      · have htl : (args.take t.arguments.1.length).length = t.arguments.1.length := by simp; omega
        have hfix : ArgsT (t.arguments.1.map (mixedValues G η)) j U (args.take t.arguments.1.length) := by
          have := hshort.2.1
          rw [htl, show t.arguments.1.length = (t.arguments.1.map (mixedValues G η)).length by simp,
            List.take_length] at this
          simpa using this
        have := ArgsT_append hfix htup
        rw [List.take_append_drop, ← List.map_append] at this
        exact ArgsShort_of_exact this
    obtain ⟨result, hi, hsafe⟩ := hv j hj U hx hu heap hh r hrv
      (hr j hj _ _ hrecv U r hrm) args hvals (Domains.short (hr j hj) hd hall)
    exact ⟨result, hi, HeapObservations.consequence_below (fun m hm V u hu => hr m (by omega) _ _ hres V u hu)
      (Effect.covers_sound heff heap) hsafe⟩
  · exact hc.elim

/-- A position covered by another: a present source position needs a target
position whose operand it is within. -/
@[nospecialize] def PositionCovers (R : List ι → List ι → Prop) : Option (List ι) → Option (List ι) → Prop
  | some a, some b => R a b
  | some _, none => False
  | none, _ => True

instance PositionCovers.decidable {R : List ι → List ι → Prop} [∀ a b, Decidable (R a b)] :
    ∀ x y, Decidable (PositionCovers R x y)
  | some a, some b => inferInstanceAs (Decidable (R a b))
  | some _, none => isFalse id
  | none, _ => isTrue trivial

/-- One pack contract within another: every argument list the source admits,
the target admits. The source requires at least as many positions; a target
without a rest bounds the source's length; and each position's operand is
within the target's, covariantly, since a pack holds values rather than
locations. Past both contracts' fixed positions every index has the rests, so
checking the positions up to that bound checks all. -/
@[nospecialize] def CoversPack (R : List ι → List ι → Prop) (p q : Tuple (List ι)) : Prop :=
  q.required.length ≤ p.required.length ∧
  (q.rest = none → p.rest = none ∧
    p.required.length + p.optional.length ≤ q.required.length + q.optional.length) ∧
  ∀ i ∈ List.range (max (p.required.length + p.optional.length)
      (q.required.length + q.optional.length) + 1),
    PositionCovers R (p.position i) (q.position i)

/-- Finite, conservative tests for undefined membership. Parameter rows are
never treated as empty merely because they have no clauses to expand. -/
@[nospecialize] def AdmitsUndefined (G : NormalGraph ι) (A : List ι) : Prop :=
  ∃ c ∈ expand G A, shape c = 4 ∨ shape c = 7

@[nospecialize] def ExcludesUndefined (G : NormalGraph ι) (A : List ι) : Prop :=
  G.plainTy A = true ∧ ∀ c ∈ expand G A, shape c ≠ 4 ∧ shape c ≠ 7

instance (G : NormalGraph ι) (A : List ι) : Decidable (AdmitsUndefined G A) := by
  unfold AdmitsUndefined; infer_instance

instance (G : NormalGraph ι) (A : List ι) : Decidable (ExcludesUndefined G A) := by
  unfold ExcludesUndefined; infer_instance

/-- Only the hole-reading guarantee changes; element locations retain their
separate read/write contracts. -/
@[nospecialize] def CoversPresence (G : NormalGraph ι) (R : List ι → List ι → Prop)
    (p q : Tuple (List ι)) : Prop :=
  match q.presence with
  | .sparse => True
  | .dense => p.presence = .dense ∨
      (p.presence = .readable ∧ ∀ A ∈ p.required ++ p.optional ++ p.rest.toList, ExcludesUndefined G A)
  | .readable => p.presence = .dense ∨
      (p.presence = .readable ∧ CoversPack R p q) ∨
      (∀ A ∈ q.required ++ q.optional ++ q.rest.toList, AdmitsUndefined G A)

instance (G : NormalGraph ι) {R : List ι → List ι → Prop} [DecidableRel R]
    (p q : Tuple (List ι)) : Decidable (CoversPresence G R p q) := by
  unfold CoversPresence; split <;> (try unfold CoversPack) <;> infer_instance

/-- A tuple contract within another. A writable target needs a writable source
of the same shape with equivalent element contracts (`CoversShape`): no
location is retyped. A readonly target only reads the elements present, each
at its position, so, as for an argument pack, the source's length bounds lie
within the target's and each position's operand is within the target's
(`CoversPack`): `[number, number]` is a `readonly (number | null)[]`. -/
@[nospecialize] def CoversTuple (G : NormalGraph ι) (R : List ι → List ι → Prop) (p q : Tuple (List ι)) : Prop :=
  CoversPresence G R p q ∧
    (if q.readonly then CoversPack R p q else CoversShape R p q)

/-- Coverage has one definition for both derivations and certificate checking.
Only fixed-arrow coverage needs evidence; the remaining conditions are finite
checks over the supplied subtype relation. -/
@[nospecialize] def CoversWith [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop)
    (self : List ι) : Clause (List ι) → Clause (List ι) → Prop
  | _, .top => True
  | a, .source => sourceClause a = true
  | .list a bs, .list c ds => ∀ q ∈ c :: ds, ∃ p ∈ a :: bs, CoversTuple G R p q
  | .nul, .nul => True
  | .undef, .undef => True
  | .bool, .bool => True
  | .boolLit _, .bool => True
  | .boolLit a, .boolLit b => a = b
  | .num, .num => True
  | .numLit _, .num => True
  | .numLit a, .numLit b => a = b
  | .str, .str => True
  | .strLit _, .str => True
  | .strLit a, .strLit b => a = b
  | .bigint, .bigint => True
  | .symbol, .symbol => True
  | .bigintLit _, .bigint => True
  | .bigintLit a, .bigintLit b => a = b
  | .symbolLit _, .symbol => True
  | .symbolLit a, .symbolLit b => a = b
  | .refs a bs vs os ms ks, .refs c ds ws ps ns ls => CoversFields R (a :: bs) (c :: ds) ∧
      CoversViews G R (a :: bs) vs ws ∧ CoversOptional R (a :: bs) vs os ks ps ∧
      CoversMethods G sub R known self ((a :: bs).flatten ++ vs.filter (·.1 != lengthKey)) ks ms ns ∧ CoversBounds ks ls
  -- A record whose own keys are bounded meets a dictionary's index contracts
  -- through the bound (`CoversKeys`), and its named members as a record's. It
  -- meets a writable index only at an uninhabited contract: a holder of one
  -- may add a key the bound says is absent.
  | .refs a bs vs os ms ks, .dict c ds ws iy ps ns ls cy =>
      CoversKeys R (a :: bs).flatten (vs.filter (·.1 != lengthKey)) ks iy cy ∧
      CoversFields R (a :: bs) (c :: ds) ∧ CoversViews G R (a :: bs) vs ws ∧
      CoversOptional R (a :: bs) vs os ks ps ∧
      CoversMethods G sub R known self ((a :: bs).flatten ++ vs.filter (·.1 != lengthKey)) ks ms ns ∧ CoversBounds ks ls ∧
      ∀ y ∈ cy, Uninhabited G y.2
  -- A dictionary meets a record's members as a record does; the record has
  -- no index, so the dictionary's index contracts are forgotten.
  | .dict a bs vs _ os ms ks _, .refs c ds ws ps ns ls =>
      CoversFields R (a :: bs) (c :: ds) ∧ CoversViews G R (a :: bs) vs ws ∧
      CoversOptional R (a :: bs) vs os ks ps ∧
      CoversMethods G sub R known self ((a :: bs).flatten ++ vs.filter (·.1 != lengthKey)) ks ms ns ∧ CoversBounds ks ls
  -- A target index view is within some source index view over as many keys
  -- (`IndexKeys.within`); a writable target index needs a writable source
  -- index over as many keys of an equivalent contract, as an invariant field
  -- does, so no location is retyped. Code holding the target may add keys of
  -- its class at its contract (the trust boundary of a writable index), so
  -- every source index and optional field over such a key must admit the
  -- contract: a mutable `{ [k: string]: S; [k: number]: N }` is not a mutable
  -- `{ [k: string]: S }`, through which a numeric key could get an `S` value;
  -- and every source own-key bound must keep the class (`KeepsKeys`): none
  -- may say a key the holder can add is absent, unless no value meets the
  -- contract, so none is added.
  | .dict a bs vs ix os ms ks cx, .dict c ds ws iy ps ns ls cy =>
      CoversFields R (a :: bs) (c :: ds) ∧ CoversViews G R (a :: bs) vs ws ∧
      ((∀ y ∈ iy, ∃ x ∈ ix, y.1.within x.1 = true ∧ R x.2 y.2) ∧
        ∀ y ∈ cy, (∃ x ∈ cx, y.1.within x.1 = true ∧ R x.2 y.2 ∧ R y.2 x.2) ∧
          (∀ z ∈ ix, y.1.overlaps z.1 = true → R y.2 z.2) ∧
          ∀ o ∈ os, y.1.may o.key = true → R y.2 o.type) ∧
      CoversOptional R (a :: bs) vs os ks ps ∧
      CoversMethods G sub R known self ((a :: bs).flatten ++ vs.filter (·.1 != lengthKey)) ks ms ns ∧ CoversBounds ks ls ∧
      KeepsKeys G ks cy
  | .arrs L S, .arrs M T | .callable _ _ L S, .arrs M T =>
      arrows L S M ∧
      ∀ t ∈ T, (∃ s ∈ S, RestCovers (restElem G) R s t) ∨ ∃ p ∈ L, FixedCallsPack G R p t
  | .callable a bs L S, .callable c ds M T =>
      CoversFields R (a :: bs) (c :: ds) ∧
      arrows L S M ∧
      ∀ t ∈ T, (∃ s ∈ S, RestCovers (restElem G) R s t) ∨ ∃ p ∈ L, FixedCallsPack G R p t
  -- A construct signature is covered by one taking as many parameters, each
  -- at least as wide, with a result at most as wide. One with a `never`
  -- parameter admits no actual list, so any class value meets it; the
  -- results are still compared, as TypeScript compares them.
  -- A static field the target states is one the source states at the same
  -- contract, as a callable object's bag field; a readonly one, a field or
  -- a view the source states within it.
  | .ctors L S a bs vs, .ctors M T c ds ws => ((∀ q ∈ M, ∃ p ∈ L, (Domains R q.1 p.1 ∨ [] ∈ q.1) ∧ R p.2 q.2) ∧
      -- A variadic one by one taking as many fixed parameters, each at least as
      -- wide, a rest at least as wide and a result at most as wide; or by a
      -- fixed one, when its rest is an exact tuple.
      ∀ t ∈ T, (∃ s ∈ S, Domains R t.1 s.1 ∧ R t.2.1 s.2.1 ∧ R s.2.2 t.2.2) ∨
        ∃ p ∈ L, FixedCoversPack G R p t) ∧ CoversFields R (a :: bs) (c :: ds) ∧ CoversBagViews R (a :: bs) vs ws
  -- Every target contract has a source contract within it.
  | .pack a bs, .pack c ds => ∀ q ∈ c :: ds, ∃ p ∈ a :: bs, CoversPack R p q
  | _, _ => False

/-- Declarative coverage supplies derivations for the fixed-arrow obligations. -/
abbrev Covers [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (R : List ι → List ι → Prop) (known : Known ι) :=
  CoversWith G sub R known (fun L S M => ∀ p ∈ M,
    CallArrow (compatible G) (restElem G) R L S p)

/-- Replacing the arrow interpreter preserves all the shared coverage conditions. -/
theorem CoversWith.mono [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {R : List ι → List ι → Prop} {known : Known ι}
    {arrows arrows' : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    (ha : ∀ L S M, arrows L S M → arrows' L S M) {self a b}
    (h : CoversWith G sub R known arrows self a b) : CoversWith G sub R known arrows' self a b := by
  unfold CoversWith at h ⊢
  cases a <;> cases b <;> simp only at *
  all_goals first
    | exact h
    | exact ⟨ha _ _ _ h.1, h.2⟩
    | exact ⟨h.1, ha _ _ _ h.2.1, h.2.2⟩

/-- Covering field by field is enough: the operands all constrain the same
object, so a field the target names is found at the location the source already
fixed, under a contract the two relations identify. -/
theorem covers_recs {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {a c : List (PropKey × List ι)} {bs ds : List (List (PropKey × List ι))}
    (hc : CoversFields R (a :: bs) (c :: ds)) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j)
    (W : WorldT n) (flds : List (PropKey × Nat))
    (hsrc : ∀ x ∈ a :: bs, recT (famsOf (mixedValues G η) x) n W (.objAt flds .absent oid)) :
    ∀ b ∈ c :: ds, recT (famsOf (mixedValues G η) b) n W (.objAt flds .absent oid) := by
  intro b hb
  refine ⟨flds, oid, rfl, ?_⟩
  intro f T hm
  obtain ⟨y, hy, rfl⟩ := mem_famsOf.mp hm
  obtain ⟨⟨pf, pl⟩, hp, hpf, hpy, hyp⟩ := hc b hb (f, y) hy
  simp only at hpf
  subst hpf
  obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
  obtain ⟨flds', l, c0, oid'', he', hf, hl, hag⟩ :=
    recT_at (mem_famsOf.mpr ⟨pl, hpL, rfl⟩) (hsrc L hL)
  cases he'
  exact ⟨l, c0, hf, hl, fun j hj W' u =>
    (hag j hj W' u).trans ⟨hr j hj pl y hpy W' u, hr j hj y pl hyp W' u⟩⟩

theorem covers_fields_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {a c : List (PropKey × List ι)} {bs ds : List (List (PropKey × List ι))}
    (hc : CoversFields R (a :: bs) (c :: ds)) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j)
    (W : WorldT n) (v : Val)
    (hv : refsT (famsOf (mixedValues G η) a) (bs.map (famsOf (mixedValues G η))) n W v) :
    refsT (famsOf (mixedValues G η) c) (ds.map (famsOf (mixedValues G η))) n W v := by
  obtain ⟨flds, oid, he, -⟩ := hv.1
  subst he
  have hsrc : ∀ x ∈ a :: bs, recT (famsOf (mixedValues G η) x) n W (.objAt flds .absent oid) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv.1
    · exact hv.2 _ (List.mem_map_of_mem hx)
  have key := covers_recs hc n hr W flds hsrc
  exact ⟨key c (by simp), fun B hB => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
    exact key b (List.mem_cons_of_mem c hb)⟩

/-- A covered view field reads a location whose contract implies its family,
whether the source states that location invariantly or as a view. -/
theorem covers_views_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {a : List (PropKey × List ι)} {bs : List (List (PropKey × List ι))}
    {vs ws : List (PropKey × List ι)}
    (hc : CoversViews G R (a :: bs) vs ws) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j)
    (W : WorldT n) (v : Val)
    (hv : refsT (famsOf (mixedValues G η) a) (bs.map (famsOf (mixedValues G η))) n W v ∧
      viewsT (famsOf (mixedValues G η) vs) n W v) :
    viewsT (famsOf (mixedValues G η) ws) n W v := by
  -- The source's slot at a key: a field of an operand, or a view.
  have field : ∀ p ∈ (a :: bs).flatten, ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr n) (oid : Nat),
      v = .objAt flds .absent oid ∧ flds.lookup p.1 = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < n) (W' : WorldT j) (u : Val), c j hj W' u → mixedValues G η p.2 j W' u := by
    intro p hp
    obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
    have hsrc : recT (famsOf (mixedValues G η) L) n W v := by
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hv.1.1
      · exact hv.1.2 _ (List.mem_map_of_mem hL)
    obtain ⟨flds, l, c0, oid, he, hf, hl, hag⟩ := recT_at (mem_famsOf.mpr ⟨p.2, hpL, rfl⟩) hsrc
    exact ⟨flds, l, c0, oid, he, hf, hl, fun j hj W' u hu => (hag j hj W' u).mp hu⟩
  intro f T hm
  obtain ⟨y, hy, rfl⟩ := mem_famsOf.mp hm
  rcases hc (f, y) hy with ⟨⟨pf, pl⟩, hp, hpf, hpy⟩ | ⟨hfl, hst⟩
  · simp only at hpf
    subst hpf
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨flds, l, c0, oid, he, hf, hl, hag⟩ := field _ hp
      exact .inl (viewT_single ⟨flds, l, c0, oid, he, hf, hl,
        fun j hj W' u hu => hr j hj pl y hpy W' u (hag j hj W' u hu)⟩)
    · rcases hv.2 pf _ (mem_famsOf.mpr ⟨pl, hp, rfl⟩) with hw | ⟨hl, hown, hall⟩
      · obtain ⟨flds, l, c0, oid, he, hf, hl, hag⟩ := viewT_at (List.mem_singleton_self _) hw
        exact .inl (viewT_single ⟨flds, l, c0, oid, he, hf, hl,
          fun j hj W' u hu => hr j hj pl y hpy W' u (hag j hj W' u hu)⟩)
      · exact .inr ⟨hl, hown, fun j hj W' m => hr j hj pl y hpy W' _ (hall j hj W' m)⟩
  · simp only at hfl
    simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hst
    obtain ⟨⟨p, hp, hpσ⟩, hnum⟩ := hst
    -- The object owns the store: a field or a view names it.
    have hown : ∃ flds oid, v = .objAt flds .absent oid ∧ (flds.lookup arrayStoreKey).isSome = true := by
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨flds, l, -, oid, he, hf, -⟩ := field p hp
        exact ⟨flds, oid, he, by rw [← hpσ, hf]; rfl⟩
      · obtain ⟨flds, l, -, oid, he, hf, -⟩ :=
          viewsT_at (mem_famsOf.mpr ⟨p.2, hp, rfl⟩) (by rw [hpσ]; decide) hv.2
        exact ⟨flds, oid, he, by rw [← hpσ, hf]; rfl⟩
    exact .inr ⟨hfl, hown, fun j _ W' m => numIn_sound hnum η _⟩

/-- A covered optional field. Where the key is present, the location is the
one the source slot names, whose contract is within the target's type, and
equivalent to it for a writable target; where it is absent, the source slot is
optional, so the object has no prototype. -/
theorem covers_optional_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {a : List (PropKey × List ι)} {bs : List (List (PropKey × List ι))}
    {vs : List (PropKey × List ι)} {os ps : List (OptionalField (List ι))}
    {ks : List KeyBound}
    (hc : CoversOptional R (a :: bs) vs os ks ps) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j)
    (W : WorldT n) (v : Val)
    (hv : refsT (famsOf (mixedValues G η) a) (bs.map (famsOf (mixedValues G η))) n W v ∧
      viewsT (famsOf (mixedValues G η) vs) n W v ∧
      optT (os.map (·.map (mixedValues G η))) n W v)
    (hks : ∀ K ∈ ks, ownKeysT K n W v) :
    optT (ps.map (·.map (mixedValues G η))) n W v := by
  obtain ⟨flds, oid, he, -⟩ := hv.1.1
  subst he
  have hsrc : ∀ L ∈ a :: bs, recT (famsOf (mixedValues G η) L) n W (.objAt flds .absent oid) := by
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hv.1.1
    · exact hv.1.2 _ (List.mem_map_of_mem hL)
  -- What each source slot says of its key: present, with a contract within its
  -- type (equivalent when writable), or, for an optional slot, possibly absent
  -- with no prototype.
  have slot : ∀ p ∈ optionalSources (a :: bs) vs os,
      (flds.lookup p.key = none → flds.lookup CallArguments.protoField = none) ∧
      ∀ l, flds.lookup p.key = some l → ∃ c : Ctr n, lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < n) (W' : WorldT j) (u : Val),
          SlotContract p.readonly (c j hj W' u) (mixedValues G η p.type j W' u) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    rcases List.mem_append.mp hp with hp | hp
    all_goals try obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    · obtain ⟨L, hL, hqL⟩ := List.mem_flatten.mp hq
      obtain ⟨flds', l, c, oid'', he', hf, hw, hag⟩ := recT_at (mem_famsOf.mpr ⟨q.2, hqL, rfl⟩) (hsrc L hL)
      cases he'
      refine ⟨(fun hl => by simp [hl] at hf), fun l' hl' => ?_⟩
      rw [hl'] at hf
      cases hf
      exact ⟨c, hw, fun j hj W' u => ⟨(hag j hj W' u).mp, fun _ => (hag j hj W' u).mpr⟩⟩
    · obtain ⟨hq, hql⟩ := List.mem_filter.mp hq
      obtain ⟨flds', l, c, oid'', he', hf, hw, hag⟩ :=
        viewsT_at (mem_famsOf.mpr ⟨q.2, hq, rfl⟩) (by simpa using hql) hv.2.1
      cases he'
      refine ⟨(fun hl => by simp [hl] at hf), fun l' hl' => ?_⟩
      rw [hl'] at hf
      cases hf
      exact ⟨c, hw, fun j hj W' u => ⟨hag j hj W' u, fun h => nomatch h⟩⟩
    · have hm : p.map (mixedValues G η) ∈ os.map (·.map (mixedValues G η)) := List.mem_map_of_mem hp
      exact ⟨fun hl => optT_no_proto hm hv.2.2 hl, fun l hl => optT_present hm hv.2.2 hl⟩
  refine ⟨flds, oid, rfl, fun o hm hl => ?_, fun o hm l hl => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    rcases hc q hq with ⟨p, hp, hk, -, -, -⟩ | ⟨-, K, hK, hpK⟩
    · exact (slot p hp).1 (by rw [hk]; exact hl)
    · exact ownKeysT_lookup (hks K hK) hpK
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    rcases hc q hq with ⟨p, hp, hk, hmode, hpq, hqp⟩ | ⟨⟨K, hK, hqK⟩, -⟩
    · obtain ⟨c, hw, hag⟩ := (slot p hp).2 l (by rw [hk]; exact hl)
      exact ⟨c, hw, fun j hj W' u => (hag j hj W' u).weaken hmode (hr j hj _ _ hpq W' u)
        (fun hq' => hr j hj _ _ (hqp hq') W' u)⟩
    · have := ownKeysT_lookup (hks K hK) hqK
      simp only [OptionalField.map] at hl
      rw [this] at hl
      cases hl


/-- A covered method signature holds of the same value read from the same
host: parameters contravariant, results covariant, the host on both sides. -/
theorem covers_sig_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {p q : MethodMembers.Sig (List ι)} (hc : CoversSig (restElem G) R p q) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hrn : ∀ S T, R S T → FamLeAt G η S T n)
    (W : WorldT n) (v u : Val)
    (h : MethodMembers.onHost Ξ v (MethodMembers.Member.of (mixedValues G η) (mixedArgs G η) p) n W u) :
    MethodMembers.onHost Ξ v (MethodMembers.Member.of (mixedValues G η) (mixedArgs G η) q) n W u := by
  obtain ⟨hcalls, hrests, hschemes, hrecv⟩ := hc
  obtain ⟨⟨hinv, hL⟩, ⟨_, hS⟩, hB⟩ := h
  -- The host, in each type the target's host must meet, is in each the
  -- source's must.
  have host : ∀ j, j < n → ∀ (U : WorldT j) r,
      MethodMembers.hostIn v (q.receivers.map (mixedValues G η)) j U r →
      MethodMembers.hostIn v (p.receivers.map (mixedValues G η)) j U r := by
    intro j hj U r ⟨hrv, hq⟩
    refine ⟨hrv, fun T hT => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hT
    obtain ⟨t', ht', hR⟩ := hrecv t ht
    exact hr j hj _ _ hR U r (hq _ (List.mem_map_of_mem ht'))
  refine ⟨⟨hinv, fun x hx => ?_⟩, ⟨hinv, fun x hx => ?_⟩, fun oid F hF => ?_⟩
  rotate_left 2
  · -- A quantified signature: the member bound to the host meets a source
    -- scheme within the target's.
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hF
    obtain ⟨s, hs, hst⟩ := hschemes t ht
    exact hrn _ _ hst W _ (hB oid _ (List.mem_map_of_mem hs))
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    obtain ⟨s, hs, hd, hres, heff⟩ := hcalls t ht
    exact (hL _ (List.mem_map_of_mem (List.mem_map_of_mem hs))).weaken (Effect.covers_sound heff) host
      (fun j hj U args ha => by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using Domains.short (hr j hj) hd (by simpa [Contract.withReceiver, MethodArrow.map, MethodRestArrow.mapWith, Contract.map] using ha))
      (fun m hm U w hw => hr m hm _ _ hres U w hw)
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    obtain ⟨s, hs, hd, hin, he, hres, heff⟩ := hrests t ht
    exact (hS _ (List.mem_map_of_mem (List.mem_map_of_mem hs))).weaken (Effect.covers_sound heff) host
      (fun j hj U args ha => by
        simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using rest_rest (hr j hj) (hpa j hj _ _ he) (by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using hd) (by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using hin)
          (by simpa [Contract.withReceiver, MethodArrow.map, MethodRestArrow.mapWith, Contract.map] using ha))
      (fun m hm U w hw => hr m hm _ _ hres U w hw)

theorem lookup_zip_none [DecidableEq ι] {src : List ι} {ys : List β} {p : ι} (hp : p ∉ src) :
    (src.zip ys).lookup p = none := by
  induction src generalizing ys with
  | nil => rfl
  | cons b src ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [List.zip_cons_cons, List.lookup_cons]
      have hb : p ≠ b := fun e => hp (e ▸ List.mem_cons_self)
      rw [beq_false_of_ne hb]
      exact ih fun h => hp (List.mem_cons_of_mem _ h)

/-- An empty type has no member. -/
theorem mixedMeaning_nil (G : NormalGraph ι) (η : MixedAssignment ι) :
    mixedMeaning G η [] = fun _ _ _ => False := by
  funext n W x
  apply propext
  cases x <;> simp [mixedMeaning, mixedParameters, graphArguments, setSem]

/-- A clause whose operands are mapped to types of the same meanings means
the same. -/
theorem semWithArgs_map_meaning [DecidableEq ι] {G : NormalGraph ι} {η θ : MixedAssignment ι}
    {f : List ι → List ι} {c : Clause (List ι)}
    (h : ∀ S, S ∈ c.operands ∨ S = [] → mixedMeaning G η (f S) = mixedMeaning G θ S) :
    semWithArgs Ξ (mixedValues G η) (mixedArgs G η) (c.map f) =
      semWithArgs Ξ (mixedValues G θ) (mixedArgs G θ) c := by
  let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
  have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
  rw [semWithArgs_map, ← hcr, semWithArgs_map, semWithArgs_map]
  have hr : ∀ S, mixedMeaning G η (f (r S)) = mixedMeaning G θ (r S) := fun S => by
    by_cases hS : S ∈ c.operands
    · simp only [r, hS, if_true]; exact h S (.inl hS)
    · simp only [r, hS, if_false]; exact h [] (.inr rfl)
  have h1 : (fun a => mixedValues G η (f (r a))) = fun a => mixedValues G θ (r a) := by
    funext a n W v
    exact congrFun (congrFun (congrFun (hr a) n) W) (.inl v)
  have h2 : (fun a => mixedArgs G η (f (r a))) = fun a => mixedArgs G θ (r a) := by
    funext a n W vs
    exact congrFun (congrFun (congrFun (hr a) n) W) (.inr vs)
  rw [h1, h2]

theorem assign_getElem (η : ParameterAssignment k ι) {bs : List ι}
    {As : List (ParameterFamily k)} (unique : bs.Nodup) (lengths : As.length = bs.length)
    (i : Nat) (hi : i < bs.length) :
    (assign η bs As).1 bs[i] = (As[i]'(by omega)).1 := by
  induction bs generalizing As i with
  | nil => simp at hi
  | cons b bs ih =>
    cases As with
    | nil => simp at lengths
    | cons A As =>
      cases i with
      | zero => exact assign_cons_head η b bs A As
      | succ i =>
        have hb : bs[i]'(by simpa using hi) ≠ b := by
          intro he
          exact (List.nodup_cons.mp unique).1 (he ▸ List.getElem_mem (by simpa using hi))
        rw [List.getElem_cons_succ, assign_cons_ne η bs A As hb]
        exact ih (List.nodup_cons.mp unique).2 (by simpa using lengths) i (by simpa using hi)

theorem lookup_zip_index [DecidableEq ι] :
    ∀ {bs : List ι} {ys : List β} {x : ι} {y : β}, (bs.zip ys).lookup x = some y →
      ∃ k, ∃ (h1 : k < bs.length) (h2 : k < ys.length), bs[k] = x ∧ ys[k] = y
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | b :: bs, c :: ys, x, y, h => by
    simp only [List.zip_cons_cons, List.lookup_cons] at h
    by_cases hx : x = b
    · subst hx
      simp only [beq_self_eq_true] at h
      cases h
      exact ⟨0, by simp, by simp, rfl, rfl⟩
    · rw [beq_false_of_ne hx] at h
      obtain ⟨k, h1, h2, hb, hy⟩ := lookup_zip_index h
      exact ⟨k + 1, by simpa using h1, by simpa using h2, hb, hy⟩

theorem lookup_zip_getElem [DecidableEq ι] :
    ∀ {bs : List ι} {ys : List β}, bs.Nodup → ∀ k (h1 : k < bs.length) (h2 : k < ys.length),
      (bs.zip ys).lookup bs[k] = some ys[k]
  | [], _, _, k, h1, _ => by simp at h1
  | _ :: _, [], _, k, _, h2 => by simp at h2
  | b :: bs, c :: ys, hn, k, h1, h2 => by
    cases k with
    | zero => simp
    | succ k =>
      have hne : bs[k]'(by simpa using h1) ≠ b := fun he =>
        (List.nodup_cons.mp hn).1 (he ▸ List.getElem_mem _)
      simp only [List.zip_cons_cons, List.lookup_cons, List.getElem_cons_succ, beq_false_of_ne hne]
      exact lookup_zip_getElem (List.nodup_cons.mp hn).2 k _ _

/-- A parameter row means its selected component of the assignment. -/
theorem mixedMeaning_param_eq {G : NormalGraph ι} {η θ : MixedAssignment ι} {p q : ι}
    (hk : G.parameterKinds p = G.parameterKinds q) (hp : G.params p = true)
    (he : η.1 p = θ.1 q) : mixedMeaning G η [p] = mixedMeaning G θ [q] := by
  obtain ⟨kind, hkind⟩ : ∃ kind, G.parameterKinds p = some kind := by
    simpa [NormalGraph.params, Option.isSome_iff_exists] using hp
  rw [mixedMeaning_parameter G η p kind hkind, mixedMeaning_parameter G θ q kind (hk ▸ hkind), he]

/-- Renaming the target's binders to the source's: at the source's instance,
a renamed target type means the target type at the same instance of its own
binders, when no source binder is free in it but as a target binder. -/
theorem renamed_meaning [DecidableEq ι] {G : NormalGraph ι} (r : Renaming G)
    (η : MixedAssignment ι) {ps qs : List ι} {As : List MixedFamily}
    (hlen : ps.length = qs.length) (hnp : ps.Nodup) (hnq : qs.Nodup)
    (hkinds : ∀ pq ∈ ps.zip qs, G.parameterKinds pq.1 = G.parameterKinds pq.2)
    (hAs : As.length = ps.length) (S : List ι)
    (hfresh : S = [] ∨ ∀ x ∈ r.free S, x ∈ ps → x ∈ qs) :
    mixedMeaning G (assign η ps As) (r.substitute (qs.zip (ps.map fun p => [p])) S) =
      mixedMeaning G (assign η qs As) S := by
  let θ := assign η ps As
  let ζ := assign θ qs As
  have images : ∀ x, G.params x = true →
      mixedMeaning G ζ [x] = mixedMeaning G θ (replace (qs.zip (ps.map fun p => [p])) x) := by
    intro x hx
    by_cases hq : x ∈ qs
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
      have hkp : k < ps.length := by omega
      have hl := lookup_zip_getElem (ys := ps.map fun p => [p]) hnq k hk (by simpa using hkp)
      simp only [replace, hl, List.getElem_map, Option.getD_some]
      apply mixedMeaning_param_eq _ hx
      · rw [assign_getElem θ hnq (by omega) k hk, assign_getElem η hnp hAs k hkp]
      · have := hkinds (ps[k], qs[k]) (by
          rw [List.mem_iff_getElem]
          exact ⟨k, by simp; omega, by simp⟩)
        exact this.symm
    · have hl := lookup_zip_none (ys := ps.map fun p => [p]) hq
      simp only [replace, hl, Option.getD_none]
      exact mixedMeaning_param_eq rfl hx (assign_nmem θ qs As hq)
  rw [← r.substitute_meaning ζ θ _ images S]
  rcases hfresh with rfl | hfresh
  · rw [mixedMeaning_nil, mixedMeaning_nil]
  apply r.agree_free
  intro x hx
  by_cases hq : x ∈ qs
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
    rw [assign_getElem θ hnq (by omega) k hk, assign_getElem η hnq (by omega) k hk]
  · rw [assign_nmem θ qs As hq, assign_nmem η qs As hq]
    exact assign_nmem η ps As fun hp => hq (hfresh x hx hp)

/-! ### Free parameter rows, semantically

A row means the same at two assignments agreeing on its free parameter rows
(`agree_freeWith`): what the instance tables below and a scheme a
prototype holds for its instances (`CoversByScheme`) rely on. -/

/-- Local operand agreement for the shared value interpretation. Argument
operands have their own agreement premise, independent of value membership. -/
theorem semWithArgs_congr_on [DecidableEq ι] {D : List ι} {c : Clause (List ι)}
    (hops : ∀ S ∈ c.operands, ∀ l ∈ S, l ∈ D) (X Y : ι → Fam)
    (P Q : List ι → ArgFam) (n : Nat)
    (h : ∀ l ∈ D, Agree (X l) (Y l) n)
    (ha : ∀ S, (∀ l ∈ S, l ∈ D) → Agree (P S) (Q S) n) (W : WorldT n) (v : Val) :
    semWithArgs Ξ (setSem X) P c n W v ↔ semWithArgs Ξ (setSem Y) Q c n W v := by
  let r : List ι → List ι := fun S => S.filter fun l => decide (l ∈ D)
  have hcr : c.map r = c := map_of_operands fun S hS =>
    List.filter_eq_self.mpr fun l hl => by simpa using hops S hS l hl
  rw [← hcr, semWithArgs_map, semWithArgs_map]
  have hin : ∀ S l, l ∈ r S → l ∈ D := fun S l hl => by
    simpa using (List.mem_filter.mp hl).2
  apply semWithArgs_congr _ _ _ _ n (fun _ _ _ _ => Iff.rfl) (fun S m hm U u => ?_) (fun S => ha _ (hin S)) c W v
  exact exists_congr fun l => and_congr_right fun hl => h l (hin S l hl) m hm U u

/-- Local agreement for argument rows is at the current level. -/
theorem clauseArguments_congr_on [DecidableEq ι] {D : List ι} {c : Clause (List ι)}
    (hops : ∀ S ∈ c.operands, ∀ l ∈ S, l ∈ D) (X Y : ι → Fam) (n : Nat)
    (h : ∀ l ∈ D, ∀ W v, X l n W v ↔ Y l n W v) (W : WorldT n) (vs : List Val) :
    clauseArguments (setSem X) c n W vs ↔ clauseArguments (setSem Y) c n W vs := by
  let r : List ι → List ι := fun S => S.filter fun l => decide (l ∈ D)
  have hcr : c.map r = c := map_of_operands fun S hS =>
    List.filter_eq_self.mpr fun l hl => by simpa using hops S hS l hl
  rw [← hcr, clauseArguments_map, clauseArguments_map]
  apply clauseArguments_congr _ _ c n W (fun S v => ?_) vs
  exact exists_congr fun l => and_congr_right fun hl =>
    h l (by simpa using (List.mem_filter.mp hl).2) W v

/-- Local operand agreement for a clause read in a row: its operands; the
builtins's prototype type is read by the same family on both sides. -/
theorem rowSem_congr_on [DecidableEq ι] {G : NormalGraph ι} {D : List ι} {c : Clause (List ι)}
    (hops : ∀ S ∈ c.operands, ∀ l ∈ S, l ∈ D) (A : List ι → Fam)
    (X Y : ι → Fam) (P Q : List ι → ArgFam) (n : Nat)
    (h : ∀ l ∈ D, Agree (X l) (Y l) n)
    (ha : ∀ S, (∀ l ∈ S, l ∈ D) → Agree (P S) (Q S) n) (W : WorldT n) (v : Val) :
    rowSem G A (setSem X) P c n W v ↔ rowSem G A (setSem Y) Q c n W v :=
  and_congr (semWithArgs_congr_on hops X Y P Q n h ha W v) Iff.rfl

theorem freeOk_row [DecidableEq ι] {G : NormalGraph ι} {D : List ι} {V : FreeMap ι}
    (hF : FreeOk G D V = true) {i : ι} (hi : i ∈ D) :
    (G.params i = true → i ∈ fv V i) ∧ (∀ l ∈ reads G i, l ∈ D ∧ ∀ p ∈ fv V l,
      p ∈ fv V i ∨ (∃ s, G.schemes i = some s ∧ p ∈ s.binders)) ∧
    ∀ l ∈ boundReads G i, ∀ p ∈ fv V l, p ∈ fv V i := by
  have h := List.all_eq_true.mp hF i hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.contains_iff_mem] at h
  refine ⟨fun hp => by simpa [hp] using h.1.1.1, fun l hl => ⟨by simpa using (h.1.2 l hl).1, fun p hp => ?_⟩,
    fun l hl p hp => by simpa using h.2 l hl p hp⟩
  have := (h.1.2 l hl).2 p hp
  rcases this with h1 | h2
  · exact .inl (by simpa using h1)
  · right
    cases hs : G.schemes i with
    | none => simp [hs] at h2
    | some s => exact ⟨s, rfl, by simpa [hs] using h2⟩

/-- A meet row's part supports it: a parameter part is free in it, and any
other part is in the domain with its free rows among the meet's. -/
@[nospecialize] def MeetPartSupport (G : NormalGraph ι) (D : ι → Prop) (V : ι → List ι) (i q : ι) : Prop :=
  (G.params q = true → q ∈ V i) ∧ (G.params q = false → D q ∧ ∀ r ∈ V q, r ∈ V i)

/-- Each part of a meet row supports it. -/
theorem freeOk_meet [DecidableEq ι] {G : NormalGraph ι} {D : List ι} {V : FreeMap ι}
    (hF : FreeOk G D V = true) {i : ι} (hi : i ∈ D) {q : ι} (hq : q ∈ meetParts G i) :
    MeetPartSupport G (· ∈ D) (fv V) i q := by
  have h := List.all_eq_true.mp hF i hi
  simp only [Bool.and_eq_true] at h
  have hq := List.all_eq_true.mp h.1.1.2 q hq
  constructor
  · intro hp
    simpa [hp] using hq
  · intro hp
    simp only [hp, Bool.false_eq_true, ite_false, Bool.and_eq_true, List.contains_iff_mem,
      List.all_eq_true] at hq
    exact ⟨hq.1, fun r hr => by simpa using hq.2 r hr⟩

/-- A local closure condition for free-parameter support. The domain and
support function need not be finite: equation graphs can establish these laws
from their templates. The existing finite certificate checks the same laws. -/
structure FreeSupport (G : NormalGraph ι) (D : ι → Prop) (V : ι → List ι) : Prop where
  row : ∀ {i}, D i →
    (G.params i = true → i ∈ V i) ∧
    (∀ l ∈ reads G i, D l ∧ ∀ p ∈ V l,
      p ∈ V i ∨ (∃ s, G.schemes i = some s ∧ p ∈ s.binders)) ∧
    (∀ l ∈ boundReads G i, ∀ p ∈ V l, p ∈ V i)
  meet : ∀ {i}, D i → ∀ q ∈ meetParts G i, MeetPartSupport G D V i q

/-- The executable finite check discharges the representation-independent
support obligation; it is not a second semantic proof. -/
theorem freeOk_support [DecidableEq ι] {G : NormalGraph ι} {D : List ι} {V : FreeMap ι}
    (hF : FreeOk G D V = true) : FreeSupport G (· ∈ D) (fv V) :=
  ⟨freeOk_row hF, fun hi _ hq => freeOk_meet hF hi hq⟩

/-- Free-variable independence is an invariant of the approximations, not an
extra delay on argument-list membership. -/
@[nospecialize] def FreeIndependent [DecidableEq ι] (D : ι → Prop) (V : ι → List ι) (I : ParameterInterpretation ι k)
    (X : ParameterAssignment k ι × ι → Fam) : Prop :=
  ∀ η θ i, D i → (∀ p ∈ V i, I.parameter p (η.1 p) = I.parameter p (θ.1 p)) → X (η, i) = X (θ, i)

private theorem independent_set [DecidableEq ι] {D : ι → Prop} {V : ι → List ι}
    {I : ParameterInterpretation ι k}
    {X : ParameterAssignment k ι × ι → Fam} (hX : FreeIndependent D V I X)
    (η θ : ParameterAssignment k ι) (S : List ι) (hS : ∀ i ∈ S, D i)
    (h : ∀ i ∈ S, ∀ p ∈ V i, I.parameter p (η.1 p) = I.parameter p (θ.1 p)) :
    setSem (fun i => X (η, i)) S = setSem (fun i => X (θ, i)) S := by
  funext n W v
  apply propext
  exact exists_congr fun i => and_congr_right fun hi => by
    dsimp only
    rw [hX η θ i (hS i hi) (h i hi)]

/-- An interpretation reads only the free parameters of its operand rows.
This is proved for each interpretation; it is not a certificate assumption. -/
structure RespectsFree [DecidableEq ι] (D : ι → Prop) (V : ι → List ι)
    (I : ParameterInterpretation ι k) : Prop where
  arguments : ∀ X, FreeIndependent D V I X → ∀ η θ S,
    (∀ i ∈ S, D i) → (∀ i ∈ S, ∀ p ∈ V i, I.parameter p (η.1 p) = I.parameter p (θ.1 p)) →
    I.arguments η (setSem fun i => X (η, i)) S =
      I.arguments θ (setSem fun i => X (θ, i)) S
  bound : ∀ X, FreeIndependent D V I X → ∀ η θ S,
    (∀ i ∈ S, D i) → (∀ i ∈ S, ∀ p ∈ V i, I.parameter p (η.1 p) = I.parameter p (θ.1 p)) →
    I.bound η (setSem fun i => X (η, i)) S =
      I.bound θ (setSem fun i => X (θ, i)) S

/-- Argument rows respect the same checked free-variable map as value rows.
Tuple elements use the approximation's independence at the current level. -/
theorem graphArguments_support [DecidableEq ι] {G : NormalGraph ι} {D : ι → Prop} {V : ι → List ι}
    (hF : FreeSupport G D V) (X : MixedAssignment ι × ι → Fam)
    (hX : FreeIndependent D V (mixedParameters G) X) (η θ : MixedAssignment ι) (S : List ι)
    (hS : ∀ i ∈ S, D i) (h : ∀ i ∈ S, ∀ p ∈ V i, (mixedParameters G).parameter p (η.1 p) = (mixedParameters G).parameter p (θ.1 p)) :
    graphArguments G η (setSem fun i => X (η, i)) S =
      graphArguments G θ (setSem fun i => X (θ, i)) S := by
  funext n W vs
  apply propext
  apply exists_congr fun i => and_congr_right fun hi => ?_
  have ⟨hself, hreads, _⟩ := hF.row (hS i hi)
  by_cases hp : G.listParam i = true
  · simp only [hp, if_true]
    have hk := NormalGraph.listParam_iff.mp hp
    have he := congrFun (congrFun (congrFun
      (h i hi i (hself (by rcases hk with hk | hk <;> simp [NormalGraph.params, hk]))) n) W) (.inr vs)
    rcases hk with hk | hk <;> simpa [mixedParameters, selectParameter, hk] using iff_of_eq he
  · simp only [hp, if_false, Bool.false_eq_true]
    apply exists_congr fun c => and_congr_right fun hc => ?_
    have hplain := NormalGraph.plain_of_clauses hc
    have hq : G.schemes i = none := (NormalGraph.plain_iff.mp hplain).2.1
    apply clauseArguments_congr_on (D := reads G i) (fun T hT l hl => ?_) _ _ n
      (fun l hl U v => ?_) W vs
    · simp only [reads, hq]
      exact List.mem_flatMap.mpr ⟨c, List.mem_append_left _ hc, List.mem_flatten.mpr ⟨T, hT, hl⟩⟩
    · rw [hX η θ l (hreads l hl).1 (fun p hp => ?_)]
      rcases (hreads l hl).2 p hp with hp | ⟨s, hs, _⟩
      · exact h i hi p hp
      · rw [hq] at hs; cases hs

theorem mixed_respectsSupport [DecidableEq ι] {G : NormalGraph ι} {D : ι → Prop} {V : ι → List ι}
    (hF : FreeSupport G D V) : RespectsFree D V (mixedParameters G) := by
  constructor
  · exact graphArguments_support hF
  · intro X hX η θ S hS h
    have hv := independent_set hX η θ S hS h
    have ha := graphArguments_support hF X hX η θ S hS h
    funext n W x
    cases x with
    | inl v => exact congrFun (congrFun (congrFun hv n) W) v
    | inr vs => exact congrFun (congrFun (congrFun ha n) W) vs

/-- A part reads only its free parameters. -/
theorem partSem_support [DecidableEq ι] {G : NormalGraph ι} {D : ι → Prop} {V : ι → List ι}
    (hF : FreeSupport G D V) (I : ParameterInterpretation ι k) (hI : RespectsFree D V I)
    (X : ParameterAssignment k ι × ι → Fam) (hX : FreeIndependent D V I X)
    (η η' : ParameterAssignment k ι) (i : ι) (hi : D i)
    (hag : ∀ p ∈ V i, I.parameter p (η.1 p) = I.parameter p (η'.1 p)) :
    partSemWithArgs G I X η i = partSemWithArgs G I X η' i := by
  funext n W v
  apply propext
  have ⟨hself, hreads, hbounds⟩ := hF.row hi
  unfold partSemWithArgs
  cases hp : G.params i
  · simp only [Bool.false_eq_true, if_false]
    cases hq : G.schemes i with
    | some s =>
      refine and_congr Iff.rfl (forall_congr' fun q => forall_congr' fun hq' => forall_congr' fun As => forall_congr' fun hl =>
        forall_congr' fun _ => imp_congr ?_ ?_)
      · -- The bounds are read at the scheme's own assignment.
        have hbr : ∀ b ∈ s.bounds, ∀ l ∈ b.2, l ∈ reads G i ∧ l ∈ boundReads G i := by
          intro b hb l hl'
          refine ⟨?_, ?_⟩
          · simp only [reads, hq]
            exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, hl'⟩))
          · simp only [boundReads, hq]
            exact List.mem_flatMap.mpr ⟨b, hb, hl'⟩
        unfold Bounded
        refine forall_congr' fun b => forall_congr' fun hbm => forall_congr' fun hbin =>
          forall_congr' fun j => forall_congr' fun hj => forall_congr' fun U =>
          forall_congr' fun u => ?_
        rw [assign_mem_eq η η' s.binders As hbin hl]
        have hb := hI.bound X hX η η' b.2
          (fun l hl' => (hreads l (hbr b hbm l hl').1).1)
          (fun l hl' p hp => hag p (hbounds l (hbr b hbm l hl').2 p hp))
        dsimp only
        rw [hb]
      let W := trunc q hq' W
      let n := q
      have hin : ∀ l ∈ reads G i, ∀ p ∈ V l,
          I.parameter p ((assign η s.binders As).1 p) = I.parameter p ((assign η' s.binders As).1 p) := by
        intro l hlS p hpv
        by_cases hb : p ∈ s.binders
        · rw [assign_mem_eq η η' s.binders As hb hl]
        · rw [assign_nmem η s.binders As hb, assign_nmem η' s.binders As hb]
          rcases (hreads l hlS).2 p hpv with h1 | ⟨s', hs', h2⟩
          · exact hag p h1
          · rw [hq] at hs'; cases hs'; exact absurd h2 hb
      have hrow : ∀ S, (∀ l ∈ S, l ∈ reads G i) → Agree
          (setSem (fun l => X (assign η s.binders As, l)) S)
          (setSem (fun l => X (assign η' s.binders As, l)) S) n := by
        intro S hS
        rw [independent_set hX _ _ S (fun l hl => (hreads l (hS l hl)).1)
          (fun l hl => hin l (hS l hl))]
        exact fun _ _ _ _ => Iff.rfl
      have hpack : ∀ S, (∀ l ∈ S, l ∈ reads G i) → Agree
          (I.arguments (assign η s.binders As) (setSem fun l => X (assign η s.binders As, l)) S)
          (I.arguments (assign η' s.binders As) (setSem fun l => X (assign η' s.binders As, l)) S) n := by
        intro S hS
        rw [hI.arguments X hX _ _ S (fun l hl => (hreads l (hS l hl)).1)
          (fun l hl => hin l (hS l hl))]
        exact fun _ _ _ _ => Iff.rfl
      have hargs : ∀ Ss : List (List ι), (∀ S ∈ Ss, ∀ l ∈ S, l ∈ reads G i) → ArgsAgree n
          (Ss.map (setSem fun l => X (assign η s.binders As, l)))
          (Ss.map (setSem fun l => X (assign η' s.binders As, l))) := by
        intro Ss hSs
        induction Ss with
        | nil => exact .nil
        | cons S Ss ihs =>
          exact .cons (hrow S (hSs S List.mem_cons_self))
            (ihs fun T hT => hSs T (List.mem_cons_of_mem _ hT))
      simp only [instanceTWithArgs, instanceSigs, instanceRestsWithArgs]
      refine sigsT_congr s.construct s.signatures (Arrow.map (setSem fun l => X (assign η s.binders As, l))) (Arrow.map (setSem fun l => X (assign η' s.binders As, l))) s.variadic (RestArrow.mapWith (setSem fun l => X (assign η s.binders As, l)) (I.arguments (assign η s.binders As) (setSem fun l => X (assign η s.binders As, l)))) (RestArrow.mapWith (setSem fun l => X (assign η' s.binders As, l)) (I.arguments (assign η' s.binders As) (setSem fun l => X (assign η' s.binders As, l)))) (fun _ _ _ _ => Iff.rfl) (fun _ _ => rfl) (fun p hps => by
        have hin : ∀ l ∈ p.receiver ++ p.arguments.flatten ++ p.result, l ∈ reads G i := fun l hl => by
          simp only [reads, hq]
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hps, by simpa [Arrow.operands, RestArrow.operands, List.append_assoc] using hl⟩))
        refine ⟨hrow _ fun l hl => hin l (by simp [hl]), hargs _ fun S hS l hl => hin l ?_,
          hrow _ fun l hl => hin l (by simp [hl])⟩
        simp only [List.mem_append, List.mem_flatten]
        exact .inl (.inr ⟨S, hS, hl⟩)) (fun _ _ => rfl) (fun p hps => by
        have hin : ∀ l ∈ p.receiver ++ p.arguments.1.flatten ++ p.arguments.2 ++ p.result, l ∈ reads G i :=
          fun l hl => by
            simp only [reads, hq]
            exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hps, by simpa [Arrow.operands, RestArrow.operands, List.append_assoc] using hl⟩)
        refine ⟨hrow _ fun l hl => hin l (by simp [hl]), hargs _ fun S hS l hl => hin l ?_,
          hpack _ (fun l hl => hin l (by simp [hl])), hrow _ fun l hl => hin l (by simp [hl])⟩
        simp only [List.mem_append, List.mem_flatten]
        exact .inl (.inl (.inr ⟨S, hS, hl⟩))) W v
    | none =>
      simp only [setSem]
      have hagi := hag
      have hag : ∀ l ∈ reads G i, ∀ p ∈ V l, I.parameter p (η.1 p) = I.parameter p (η'.1 p) := by
        intro l hl p hpv
        rcases (hreads l hl).2 p hpv with h1 | ⟨s', hs', _⟩
        · exact hag p h1
        · rw [hq] at hs'; cases hs'
      have hag' : ∀ l ∈ reads G i, Agree (X (η, l)) (X (η', l)) n := by
        intro l hl
        rw [hX η η' l (hreads l hl).1 (hag l hl)]
        exact fun _ _ _ _ => Iff.rfl
      have hpack : ∀ S, (∀ l ∈ S, l ∈ reads G i) → Agree
          (I.arguments η (setSem fun l => X (η, l)) S)
          (I.arguments η' (setSem fun l => X (η', l)) S) n := by
        intro S hS
        rw [hI.arguments X hX η η' S (fun l hl => (hreads l (hS l hl)).1)
          (fun l hl => hag l (hS l hl))]
        exact fun _ _ _ _ => Iff.rfl
      have hops : ∀ c ∈ G i ++ meetClauses G i, ∀ S ∈ c.operands, ∀ l ∈ S, l ∈ reads G i := by
        intro c hc S hS l hl
        simp only [reads, hq]
        exact List.mem_flatMap.mpr ⟨c, hc, List.mem_flatten.mpr ⟨S, hS, hl⟩⟩
      have cl : ∀ cs, (∀ c ∈ cs, c ∈ G i ++ meetClauses G i) →
          (setSem (rowSem G (setSem fun l => X (I.builtinsAt, l)) (setSem fun l => X (η, l)) (I.arguments η (setSem fun l => X (η, l)))) cs n W v ↔
            setSem (rowSem G (setSem fun l => X (I.builtinsAt, l)) (setSem fun l => X (η', l)) (I.arguments η' (setSem fun l => X (η', l)))) cs n W v) := by
        intro cs hcs
        constructor
        · rintro ⟨c, hc, h⟩
          exact ⟨c, hc, (rowSem_congr_on (hops c (hcs c hc)) _ _ _ _ _ n hag' hpack W v).mp h⟩
        · rintro ⟨c, hc, h⟩
          exact ⟨c, hc, (rowSem_congr_on (hops c (hcs c hc)) _ _ _ _ _ n hag' hpack W v).mpr h⟩
      exact cl _ fun c hc => List.mem_append_left _ hc
  · simp only [if_true]
    rw [I.value_parameter i _ _ (hag i (hself hp))]


theorem qLayer_support [DecidableEq ι] {G : NormalGraph ι} {D : ι → Prop} {V : ι → List ι}
    (hF : FreeSupport G D V) (I : ParameterInterpretation ι k) (hI : RespectsFree D V I)
    (X : ParameterAssignment k ι × ι → Fam) (hX : FreeIndependent D V I X) :
    FreeIndependent D V I (qLayerWithArgs G I X) := by
  intro η η' i hi hag
  by_cases hmeet : G.params i = true ∨ (G.schemes i).isSome = true ∨ G.meets i = none
  · rw [qLayer_part hmeet, qLayer_part hmeet]
    exact partSem_support hF I hI X hX η η' i hi hag
  simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hmeet
  obtain ⟨hp, hq, hm⟩ := hmeet
  obtain ⟨⟨p, cs⟩, hm⟩ := Option.ne_none_iff_exists'.mp hm
  have ⟨_, hreads, _⟩ := hF.row hi
  -- Each part: a parameter free in the meet, or a row supported by the meet.
  have hpart : ∀ q ∈ p :: G.meetParams i,
      partSemWithArgs G I X η q = partSemWithArgs G I X η' q := by
    intro q hqm
    have hs := hF.meet hi q (by rw [meetParts_of hm]; exact hqm)
    cases hqp : G.params q
    · obtain ⟨hDq, hVq⟩ := hs.2 hqp
      exact partSem_support hF I hI X hX η η' q hDq (fun r hr => hag r (hVq r hr))
    · rw [partSemWithArgs_param hqp, partSemWithArgs_param hqp,
        I.value_parameter q _ _ (hag q (hs.1 hqp))]
  have hag2 : ∀ l ∈ reads G i, ∀ r ∈ V l, I.parameter r (η.1 r) = I.parameter r (η'.1 r) := by
    intro l hl r hrv
    rcases (hreads l hl).2 r hrv with h1 | ⟨s', hs', _⟩
    · exact hag r h1
    · rw [hq] at hs'; cases hs'
  funext n W v
  apply propext
  unfold qLayerWithArgs
  simp only [hp, hq, hm, Bool.false_eq_true, ite_false]
  have hag' : ∀ l ∈ reads G i, Agree (X (η, l)) (X (η', l)) n := by
    intro l hl
    rw [hX η η' l (hreads l hl).1 (hag2 l hl)]
    exact fun _ _ _ _ => Iff.rfl
  have hpack : ∀ S, (∀ l ∈ S, l ∈ reads G i) → Agree
      (I.arguments η (setSem fun l => X (η, l)) S)
      (I.arguments η' (setSem fun l => X (η', l)) S) n := by
    intro S hS
    rw [hI.arguments X hX η η' S (fun l hl => (hreads l (hS l hl)).1)
      (fun l hl => hag2 l (hS l hl))]
    exact fun _ _ _ _ => Iff.rfl
  have hops : ∀ c ∈ cs, ∀ S ∈ c.operands, ∀ l ∈ S, l ∈ reads G i := by
    intro c hc S hS l hl
    simp only [reads, hq]
    exact List.mem_flatMap.mpr ⟨c, List.mem_append_right _ (by simp [meetClauses, hm, hc]),
      List.mem_flatten.mpr ⟨S, hS, hl⟩⟩
  refine and_congr (and_congr ?_ (forall_congr' fun q => imp_congr_right fun hqm => ?_)) ?_
  · rw [hpart p List.mem_cons_self]
  · rw [hpart q (List.mem_cons_of_mem _ hqm)]
  · constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨c, hc, (rowSem_congr_on (hops c hc) _ _ _ _ _ n hag' hpack W v).mp h⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨c, hc, (rowSem_congr_on (hops c hc) _ _ _ _ _ n hag' hpack W v).mpr h⟩

/-- Independence for the shared recursive interpretation, including mixed pack
parameters and bounds. It follows from one approximation invariant. -/
theorem agree_supportWith [DecidableEq ι] {G : NormalGraph ι} {D : ι → Prop} {V : ι → List ι}
    (hF : FreeSupport G D V) (I : ParameterInterpretation ι k) (hI : RespectsFree D V I) :
    FreeIndependent D V I (qDenoteWithArgs G I) := by
  intro η θ i hi h
  funext n W v
  exact congrFun (congrFun (congrFun
    (Tower.approx_inv (FreeIndependent D V I)
      (fun _ _ _ _ _ => rfl) (qLayer_support hF I hI) (n + 1) η θ i hi h) n) W) v

/-- Finite-certificate specialization of the shared support theorem. -/
theorem graphArguments_free [DecidableEq ι] {G : NormalGraph ι} {D : List ι} {V : FreeMap ι}
    (hF : FreeOk G D V = true) (X : MixedAssignment ι × ι → Fam)
    (hX : FreeIndependent (· ∈ D) (fv V) (mixedParameters G) X)
    (η θ : MixedAssignment ι) (S : List ι) (hS : ∀ i ∈ S, i ∈ D)
    (h : ∀ i ∈ S, ∀ p ∈ fv V i,
      (mixedParameters G).parameter p (η.1 p) = (mixedParameters G).parameter p (θ.1 p)) :
    graphArguments G η (setSem fun i => X (η, i)) S =
      graphArguments G θ (setSem fun i => X (θ, i)) S :=
  graphArguments_support (freeOk_support hF) X hX η θ S hS h

theorem mixed_respectsFree [DecidableEq ι] {G : NormalGraph ι} {D : List ι} {V : FreeMap ι}
    (hF : FreeOk G D V = true) : RespectsFree (· ∈ D) (fv V) (mixedParameters G) :=
  mixed_respectsSupport (freeOk_support hF)

theorem agree_freeWith [DecidableEq ι] {G : NormalGraph ι} {D : List ι} {V : FreeMap ι}
    (hF : FreeOk G D V = true) (I : ParameterInterpretation ι k)
    (hI : RespectsFree (· ∈ D) (fv V) I) :
    FreeIndependent (· ∈ D) (fv V) I (qDenoteWithArgs G I) :=
  agree_supportWith (freeOk_support hF) I hI

/-- Arrows covering a signature, with the host within their receivers below
the level in every extending world, meet the host-relative member. -/
theorem covers_arrows_sound {G : NormalGraph ι} {η : MixedAssignment ι}
    {R : List ι → List ι → Prop} {self : List ι} {L : Ops ι}
    {S : List (RestArrow (List ι))} {q : MethodMembers.Sig (List ι)}
    (hby : CoversArrows G R self L S q) {n : Nat}
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    {W : WorldT n} {v : Val}
    (hself : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      mixedValues G η self j U v)
    {j : Nat} (hj : j < n) {U : WorldT j} (hU : WExt (trunc j (Nat.le_of_lt hj) W) U) {u : Val}
    (hsem : mixedSem G η (.arrs L S) j U u) :
    MethodMembers.onHost (excOf G) v (MethodMembers.Member.of (mixedValues G η) (mixedArgs G η) q) j U u := by
  obtain ⟨hnone, hcalls, hrests⟩ := hby
  -- The host is in `self`, and in each type the target's host must meet;
  -- so in the function's receiver, below `j`.
  have host : ∀ (s : List ι), (R self s ∨ ∃ T ∈ q.receivers, R T s) → ∀ j' (hj' : j' < j) (U' : WorldT j'),
      WExt (trunc j' (Nat.le_of_lt hj') U) U' → ∀ r,
      MethodMembers.hostIn v (q.receivers.map (mixedValues G η)) j' U' r →
      mixedValues G η s j' U' r := by
    intro s hs j' hj' U' hU' r ⟨hrv, hq⟩
    rcases hs with hs | ⟨T, hT, hs⟩
    · cases hrv
      have hx : WExt (trunc j' (Nat.le_of_lt (Nat.lt_trans hj' hj)) W) U' := by
        have := WExt_trunc (Nat.le_of_lt hj') hU
        rw [trunc_trunc] at this
        exact WExt_trans this hU'
      exact hr j' (by omega) _ _ hs U' _ (hself j' (by omega) U' hx)
    · exact hr j' (by omega) _ _ hs U' r (hq _ (List.mem_map_of_mem hT))
  obtain ⟨hsem, -⟩ := hsem
  refine ⟨⟨hsem.1.1, fun x hx => ?_⟩, ⟨hsem.1.1, fun x hx => ?_⟩, fun _ F hF => ?_⟩
  rotate_left 2
  · simp [MethodMembers.Member.of, hnone] at hF
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    obtain ⟨s, hs, hsr, hd, hres, heff⟩ := hcalls t ht
    exact ((hsem.1.2 _ (List.mem_map_of_mem hs)).weaken (Effect.covers_sound heff) (fun _ _ _ r h => h)
      (fun j' hj' U' args ha => by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using Domains.short (hr j' (by omega)) hd (by simpa [Contract.withReceiver, MethodArrow.map, MethodRestArrow.mapWith, Contract.map] using ha))
      (fun m hm U' w hw => hr m (by omega) _ _ hres U' w hw)).weaken_recv
      (fun j' hj' U' hU' r hr' => host s.receiver hsr j' hj' U' hU' r hr')
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    obtain ⟨s, hs, hsr, hd, hin, he, hres, heff⟩ := hrests t ht
    exact ((hsem.2.2 _ (List.mem_map_of_mem hs)).weaken (Effect.covers_sound heff) (fun _ _ _ r h => h)
      (fun j' hj' U' args ha => by
        simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using rest_rest (hr j' (by omega)) (hpa j' (by omega) _ _ he) (by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using hd)
          (by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using hin) (by simpa [Contract.withReceiver, MethodArrow.map, MethodRestArrow.mapWith, Contract.map] using ha))
      (fun m hm U' w hw => hr m (by omega) _ _ hres U' w hw)).weaken_recv
      (fun j' hj' U' hU' r hr' => host s.receiver hsr j' hj' U' hU' r hr')

/-- A row of a type reading none of `bs` means the same at every
reassignment of them. -/
theorem bindersFree_row [DecidableEq ι] {G : NormalGraph ι} {bs A : List ι}
    (h : bindersFree G bs A = true) (η : MixedAssignment ι) (As : List MixedFamily)
    {l : ι} (hl : l ∈ A) :
    qDenoteWithArgs G (mixedParameters G) (assign η bs As, l) =
      qDenoteWithArgs G (mixedParameters G) (η, l) := by
  unfold bindersFree at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at h
  obtain ⟨hF, hA⟩ := h
  exact agree_freeWith hF (mixedParameters G) (mixed_respectsFree hF) (assign η bs As) η l
    (hA l hl).1 (fun p hp => by
      have hnot : p ∉ bs := by simpa using (hA l hl).2 p hp
      rw [assign_nmem η bs As hnot])

/-- So a type whose rows are among such a type's. -/
theorem bindersFree_values [DecidableEq ι] {G : NormalGraph ι} {bs A : List ι}
    (h : bindersFree G bs A = true) (η : MixedAssignment ι) (As : List MixedFamily)
    {r : List ι} (hr : ∀ l ∈ r, l ∈ A) :
    mixedValues G (assign η bs As) r = mixedValues G η r := by
  funext n W v
  apply propext
  show (∃ l ∈ r, _) ↔ (∃ l ∈ r, _)
  refine exists_congr fun l => and_congr_right fun hl => ?_
  show qDenoteWithArgs G (mixedParameters G) (assign η bs As, l) n W v ↔
    qDenoteWithArgs G (mixedParameters G) (η, l) n W v
  rw [bindersFree_row h η As (hr l hl)]

/-- Premises hold below a level at every reassignment of a scheme row's
binders: what entering a quantified signature reads. A checked table holds
at every assignment, so it gives this at any `η`; a family entry's premises
hold where its hypotheses do, which such a reassignment preserves when no
hypothesis names a binder. -/
@[nospecialize] def ReassignSound (G : NormalGraph ι) (η : MixedAssignment ι) (R : List ι → List ι → Prop)
    (n : Nat) : Prop :=
  ∀ (i : ι) (s : SchemeRow ι) (As : List MixedFamily), G.schemes i = some s →
    (∀ j, j < n → ∀ S T, R S T → FamLeAt G (assign η s.binders As) S T j) ∧
      ArgsLeBelow G (assign η s.binders As) R n

/-- **Signatures a bound scheme meets.** At an assignment `θ` where a
function `u` meets a scheme's signatures and the host `v` is in each of their
receivers, `.bind`'s forwarding function meets, at any receiver, each
signature the scheme's cover (`callsT_bound`, `restsT_bound`), the coverage
premises read at `θ`. -/
theorem bound_sigs_sound [DecidableEq ι] {G : NormalGraph ι} {θ : MixedAssignment ι}
    {R : List ι → List ι → Prop} {s : SchemeRow ι} {L : Ops ι} {M : List (RestArrow (List ι))}
    (hsig : BoundSigsCover G R s L M) {j : Nat}
    (hr : ∀ k, k < j → ∀ S T, R S T → FamLeAt G θ S T k) (hpa : ArgsLeBelow G θ R j)
    {U : WorldT j} {u v : Val}
    (hi : semWithArgs Ξ (mixedValues G θ) (mixedArgs G θ) (.arrs s.signatures s.variadic) j U u)
    (hval : isVal v = true ∧ Scoped 0 v)
    (hrv : ∀ r ∈ s.signatures.map (·.receiver) ++ s.variadic.map (·.receiver), mixedValues G θ r j U v)
    (hinvB : Invocable (.objAt [] (.bound u v []) oid)) :
    semWithArgs Ξ (mixedValues G θ) (mixedArgs G θ) (.arrs L M) j U (.objAt [] (.bound u v []) oid) := by
  have hadm : ∀ (S : List ι), Adm (mixedValues G θ S) :=
    fun S => setSem_adm (fun i => qDenoteWithArgs_adm G (mixedParameters G) (θ, i)) S
  have hargsAdm : ∀ (S : List ι), Adm (mixedArgs G θ S) :=
    fun S => graphArguments_adm G θ (mixedValues G θ) hadm S
  obtain ⟨hsig, hvar⟩ := hsig
  refine ⟨CallEffects.callsT_of_signatures hinvB fun x hx => ?_, CallEffects.restsT_of_signatures hinvB fun x hx => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨p, hp, hd, hres, heff⟩ := hsig t ht
    have hc := CallEffects.callsT_select hi.1 (List.mem_map_of_mem hp)
    have hrv := hrv p.receiver (List.mem_append_left _ (List.mem_map_of_mem hp))
    have hbd := CallEffects.callsT_bound (Ps := []) (Rc := mixedValues G θ t.receiver)
      (Ds := p.arguments.map (mixedValues G θ))
      (R := mixedValues G θ p.result)
      (fs := []) (oid := oid) (pre := []) (hadm p.receiver) (by simp)
      (fun A hA => by obtain ⟨b, -, rfl⟩ := List.mem_map.mp hA; exact hadm b)
      (by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using hc) hval.1 hval.2 hrv trivial (by simp [CallArguments.Values]) (by simp)
    refine ⟨hbd.1, fun y hy => ?_⟩
    cases List.mem_singleton.mp hy
    exact (hbd.2 _ (List.mem_singleton_self _)).weaken (Effect.covers_sound heff) (fun _ _ _ r h => h)
      (fun j'' hj'' U' args ha => by
        simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using Domains.short (hr j'' (by omega)) hd (by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using ha))
      (fun m hm U' w hw => hr m (by omega) _ _ hres U' w hw)
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨p, hp, hd, hin, he, hres, heff⟩ := hvar t ht
    have hc := CallEffects.restsT_select hi.2 (List.mem_map_of_mem hp)
    have hrv := hrv p.receiver (List.mem_append_right _ (List.mem_map_of_mem hp))
    have hbd := CallEffects.restsT_bound (Rc := mixedValues G θ t.receiver)
      (Ps := p.arguments.1.map (mixedValues G θ))
      (E := mixedArgs G θ p.arguments.2)
      (R := mixedValues G θ p.result)
      (fs := []) (oid := oid) (pre := []) (hadm p.receiver)
      (fun A hA => by obtain ⟨b, -, rfl⟩ := List.mem_map.mp hA; exact hadm b)
      (hargsAdm p.arguments.2) hc hval.1 hval.2 hrv
      (by simp only [List.take_nil, List.take_zero, List.length_nil]; exact trivial)
      (fun _ _ _ _ ys hys => by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using hys)
      (by simp [CallArguments.Values]) (by simp)
    refine ⟨hbd.1, fun y hy => ?_⟩
    cases List.mem_singleton.mp hy
    exact ((by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using hbd.2 _ (List.mem_singleton_self _)) :
      PromiseWith Ξ p.effect (ArgsRest (p.arguments.1.map (mixedValues G θ))
        (mixedArgs G θ p.arguments.2))
        (mixedValues G θ t.receiver)
        (mixedValues G θ p.result) j U _).weaken (Effect.covers_sound heff) (fun _ _ _ r h => h)
      (fun j'' hj'' U' args ha => by
        simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using rest_rest (hr j'' (by omega)) (hpa j'' (by omega) _ _ he)
          (by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using hd) (by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using hin) (by simpa [Arrow.map, RestArrow.mapWith, MethodArrow.map, MethodRestArrow.mapWith, Contract.map, Contract.withReceiver] using ha))
      (fun m hm U' w hw => hr m (by omega) _ _ hres U' w hw)

/-- **A scheme received by the host.** A generic function the host reaches
under a member's key, whose receivers read none of its binders and hold the
host, meets bound to the host each target scheme it binds as: at every
instance the target admits, which the source admits too at its own binders,
the host is in the source signature's receiver (the same as at the table's
assignment), so the bound function meets the covered signatures
(`bound_sigs_sound`). With the same rows these are the target's; renamed,
they are the target's signatures with its binders renamed to the source's,
which at the source's instance mean the target's at its own
(`renamed_meaning`). -/
theorem covers_by_scheme_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {η : MixedAssignment ι}
    {R : List ι → List ι → Prop} {self F : List ι} {q : MethodMembers.Sig (List ι)}
    (hby : CoversByScheme G sub R self F q) {n : Nat}
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n)
    {W : WorldT n} {v : Val}
    (hself : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      mixedValues G η self j U v)
    {j : Nat} (hj : j < n) {U : WorldT j} (hU : WExt (trunc j (Nat.le_of_lt hj) W) U) {u : Val}
    (hu : mixedValues G η F j U u) :
    MethodMembers.onHost (excOf G) v (MethodMembers.Member.of (mixedValues G η) (mixedArgs G η) q) j U u := by
  unfold CoversByScheme at hby
  split at hby
  · rename_i i
    split at hby
    · rename_i s hs
      obtain ⟨hcon, hcalls, hrests, hpi, hfree, hrecv, hschemes⟩ := hby
      obtain ⟨i', hi', hv⟩ := hu
      cases List.mem_singleton.mp hi'
      rw [qDenoteWithArgs_unfold] at hv
      simp only [qLayerWithArgs, hpi, hs, Bool.false_eq_true, if_false] at hv
      simp only [schemeSemWithArgs, boundedSem, instanceTWithArgs, sigsT, Callee, hcon,
        Bool.false_eq_true, if_false] at hv
      obtain ⟨hinv, hall⟩ := hv
      have hvself := hself j hj U hU
      have hval : isVal v = true ∧ Scoped 0 v := by
        obtain ⟨l, _, hl⟩ := hvself
        exact mixedDenote_value G η l hl
      -- The host is in every receiver of the scheme, at every instance: at
      -- the table's assignment by the premises, and the receivers read none
      -- of the binders.
      have hhost : ∀ r ∈ s.signatures.map (·.receiver) ++ s.variadic.map (·.receiver), ∀ As : List MixedFamily,
          mixedValues G (assign η s.binders As) r j U v := by
        intro r hrm As
        have hsub : ∀ l ∈ r, l ∈ schemeReceivers s := by
          intro l hl
          simp only [schemeReceivers, List.mem_append, List.mem_flatMap]
          rcases List.mem_append.mp hrm with h | h
          · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
            exact .inl ⟨p, hp, hl⟩
          · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
            exact .inr ⟨p, hp, hl⟩
        rw [bindersFree_values hfree η As hsub]
        exact hr j hj self r (hrecv r hrm) U v hvself
      have hinvB : ∀ oid, Invocable (.objAt [] (.bound u v []) oid) := fun oid =>
        ⟨[], _, oid, rfl, rfl, by simp only [Scoped, scopedArgs_iff]; exact ⟨hinv.scoped, hval.2, by simp⟩⟩
      -- At each instance of the source's binders within its bounds, the
      -- bound function meets every signature the source's cover.
      have hat : ∀ qlevel (hlevel : qlevel ≤ j), ∀ oid, ∀ As : List MixedFamily, As.length = s.binders.length →
          G.domain.allowed s As → Bounded (fun θ S => (mixedParameters G).bound θ
            (setSem (fun l => qDenoteWithArgs G (mixedParameters G) (θ, l))) S) η s As qlevel →
          ∀ L M, BoundSigsCover G R s L M →
          semWithArgs (excOf G) (mixedValues G (assign η s.binders As)) (mixedArgs G (assign η s.binders As))
            (.arrs L M) qlevel (trunc qlevel hlevel U) (.objAt [] (.bound u v []) oid) := by
        intro qlevel hlevel oid As hl hal hb' L M hc
        exact bound_sigs_sound hc (fun k hk => (hre i s As hs).1 k (by omega))
          (fun k hk => (hre i s As hs).2 k (by omega)) (hall qlevel hlevel As hl hal hb') hval
          (fun r hrm => (setSem_adm (fun l => qDenoteWithArgs_adm G (mixedParameters G) _) r).down_le j qlevel hlevel U v (hhost r hrm As)) (hinvB oid)
      refine ⟨⟨hinv, fun p hp => ?_⟩, ⟨hinv, fun p hp => ?_⟩, fun oid B hB => ?_⟩
      · simp [MethodMembers.Member.of, hcalls] at hp
      · simp [MethodMembers.Member.of, hrests] at hp
      obtain ⟨S', hS', rfl⟩ := List.mem_map.mp hB
      have hb := hschemes S' hS'
      unfold SchemeBinds at hb
      split at hb
      · rename_i j'
        split at hb
        · rename_i s' hs'
          obtain ⟨hpj, hcon', hord, hcase⟩ := hb
          refine ⟨j', List.mem_singleton_self j', ?_⟩
          show qDenoteWithArgs G (mixedParameters G) (η, j') j U _
          rw [qDenoteWithArgs_unfold]
          simp only [qLayerWithArgs, hpj, hs', Bool.false_eq_true, if_false]
          simp only [schemeSemWithArgs, boundedSem, instanceTWithArgs, sigsT, Callee, hcon',
            Bool.false_eq_true, if_false]
          refine ⟨hinvB oid, fun qlevel hlevel As hl _hal hbd => ?_⟩
          have hal := (sameShape_allowed G.domain hord As).mpr _hal
          show semWithArgs (excOf G) (mixedValues G (assign η s'.binders As)) (mixedArgs G (assign η s'.binders As))
              (.arrs s'.signatures s'.variadic) qlevel (trunc qlevel hlevel U) (.objAt [] (.bound u v []) oid)
          rcases hcase with ⟨hbs, hbnd, hcov⟩ | hren
          · have hb' : Bounded (fun θ S => (mixedParameters G).bound θ
                (setSem (fun l => qDenoteWithArgs G (mixedParameters G) (θ, l))) S) η s As qlevel := by
              intro b hbm hbin j'' hj'' U' w hw
              rw [hbs] at hbin hw
              exact hbd b (hbnd b hbm) hbin j'' hj'' U' w hw
            rw [← hbs]
            exact hat qlevel hlevel oid As (by rw [hbs]; exact hl) hal hb' _ _ hcov
          · cases sub with
            | none => exact hren.elim
            | some r =>
              obtain ⟨hlen, hnp, hnq, hkinds, hbnd, hfresh, hcov⟩ := hren
              -- Each source bound holds at the instance: the target's bound on
              -- the renamed binder does, and is within it.
              have hb' : Bounded (fun θ S => (mixedParameters G).bound θ
                  (setSem (fun l => qDenoteWithArgs G (mixedParameters G) (θ, l))) S) η s As qlevel := by
                intro b hbm hbin k hk U' w hw
                obtain ⟨b', hb'm, hlk, hR⟩ := hbnd b hbm
                obtain ⟨m, hm1, hm2, hpb', hqb'⟩ := lookup_zip_index hlk
                have heq : (assign η s.binders As).1 b.1 = (assign η s'.binders As).1 b'.1 := by
                  rw [← hpb', ← hqb', assign_getElem η hnp (by omega) m hm1,
                    assign_getElem η hnq (by omega) m hm2]
                have hin : b'.1 ∈ s'.binders := hqb' ▸ List.getElem_mem hm2
                have hw' := hbd b' hb'm hin k hk U' w (heq ▸ hw)
                cases w with
                | inl w => exact hr k (by omega) _ _ hR U' w hw'
                | inr ws => exact hpa k (by omega) _ _ hR U' ws hw'
              have hsrc := hat qlevel hlevel oid As (by rw [hlen]; exact hl) hal hb' _ _ hcov
              rw [← semWithArgs_map_meaning (η := assign η s.binders As)
                (f := r.substitute (renamingOf s.binders s'.binders)) fun S hS => ?_]
              · exact hsrc
              · apply renamed_meaning r η hlen hnp hnq hkinds (by omega) S
                rcases hS with hS | rfl
                · exact .inr (hfresh S hS)
                · exact .inl rfl
        · exact hb.elim
      · exact hb.elim
    · exact hby.elim
  · exact hby.elim

/-- A function covering a signature meets the host-relative member. -/
theorem covers_by_function_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {η : MixedAssignment ι}
    {R : List ι → List ι → Prop} {self F : List ι} {q : MethodMembers.Sig (List ι)}
    (hby : CoversByFunction G sub R self F q) {n : Nat}
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n)
    {W : WorldT n} {v : Val}
    (hself : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      mixedValues G η self j U v)
    {j : Nat} (hj : j < n) {U : WorldT j} (hU : WExt (trunc j (Nat.le_of_lt hj) W) U) {u : Val}
    (hu : mixedValues G η F j U u) :
    MethodMembers.onHost (excOf G) v (MethodMembers.Member.of (mixedValues G η) (mixedArgs G η) q) j U u := by
  unfold CoversByFunction at hby
  split at hby
  · rename_i L S hE
    have hplain := plain_of_mem_expand (G := G) (S := F) (c := .arrs L S) (by simp [hE])
    obtain ⟨c', hc', hsem⟩ := (mixed_expand η hplain j U u).mp hu
    rw [hE, List.mem_singleton] at hc'
    subst hc'
    exact covers_arrows_sound hby hr hpa hself hj hU hsem
  · exact covers_by_scheme_sound hby hr hpa hre hself hj hU hu

/-- A record's invariant fields and views are at its locations, whose contracts
imply their operands' families. -/
theorem fields_at {G : NormalGraph ι} {η : MixedAssignment ι} {a : List (PropKey × List ι)}
    {bs : List (List (PropKey × List ι))} {vs : List (PropKey × List ι)} {n : Nat} {W : WorldT n} {v : Val}
    (hr : refsT (famsOf (mixedValues G η) a) (bs.map (famsOf (mixedValues G η))) n W v)
    (hw : viewsT (famsOf (mixedValues G η) vs) n W v) :
    ∀ f ∈ (a :: bs).flatten ++ vs.filter (·.1 != lengthKey), ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr n) (oid : Nat),
      v = .objAt flds .absent oid ∧ flds.lookup f.1 = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → mixedValues G η f.2 j U u := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨L, hL, hfL⟩ := List.mem_flatten.mp hf
    have hrec : recT (famsOf (mixedValues G η) L) n W v := by
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hr.1
      · exact hr.2 _ (List.mem_map_of_mem hL)
    obtain ⟨flds, l, c, oid', he, hfl, hl, hag⟩ := recT_at (mem_famsOf.mpr ⟨f.2, hfL, rfl⟩) hrec
    exact ⟨flds, l, c, oid', he, hfl, hl, fun j hj U u hu => (hag j hj U u).mp hu⟩
  · obtain ⟨hf, hfl⟩ := List.mem_filter.mp hf
    exact viewsT_at (mem_famsOf.mpr ⟨f.2, hf, rfl⟩) (by simpa using hfl) hw

/-- A record's invariant field is at its location, whose contract agrees with
the field's family. -/
theorem fields_agree {G : NormalGraph ι} {η : MixedAssignment ι} {a : List (PropKey × List ι)}
    {bs : List (List (PropKey × List ι))} {n : Nat} {W : WorldT n} {v : Val}
    (hr : refsT (famsOf (mixedValues G η) a) (bs.map (famsOf (mixedValues G η))) n W v) :
    ∀ f ∈ (a :: bs).flatten, ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr n) (oid : Nat),
      v = .objAt flds .absent oid ∧ flds.lookup f.1 = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ mixedValues G η f.2 j U u := by
  intro f hf
  obtain ⟨L, hL, hfL⟩ := List.mem_flatten.mp hf
  have hrec : recT (famsOf (mixedValues G η) L) n W v := by
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hr.1
    · exact hr.2 _ (List.mem_map_of_mem hL)
  exact recT_at (mem_famsOf.mpr ⟨f.2, hfL, rfl⟩) hrec

/-- A present own key of an object whose own keys a bound lists is in it. -/
private theorem ownKeysT_mem {K : KeyBound} (ha : K.among = true) {k : Nat} {W : WorldT k}
    {flds : List (PropKey × Nat)} (h : ownKeysT K k W (.objAt flds .absent oid))
    {f : PropKey} {l : Nat} (hl : flds.lookup f = some l) : f ∈ K.keys := by
  simpa [KeyBound.admits, ha] using ownKeysT_admits h hl

/-- **Index contracts through an own-key bound.** No prototype key is among
the object's own keys, and every present key an index's class admits, which
it may admit (`IndexKeys.may_of_admits`), is a source member whose location's
contract implies, or for a writable index agrees with, the index. -/
theorem covers_keys_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {a : List (PropKey × List ι)} {bs : List (List (PropKey × List ι))} {vs : List (PropKey × List ι)}
    {ks : List KeyBound} {iy cy : List (IndexKeys × List ι)}
    (hc : CoversKeys R (a :: bs).flatten (vs.filter (·.1 != lengthKey)) ks iy cy) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (W : WorldT n) (v : Val)
    (hrefs : refsT (famsOf (mixedValues G η) a) (bs.map (famsOf (mixedValues G η))) n W v)
    (hw : viewsT (famsOf (mixedValues G η) vs) n W v) (hb : ∀ K ∈ ks, ownKeysT K n W v) :
    (∀ y ∈ iy, dictViewT y.1 (mixedValues G η y.2) n W v) ∧
      ∀ y ∈ cy, dictCellT y.1 (mixedValues G η y.2) n W v := by
  obtain ⟨K, hK, ha, hproto, hkeys⟩ := hc
  obtain ⟨flds, oid, rfl, -⟩ := hb K hK
  have hown := hb K hK
  have hnp := ownKeysT_lookup (f := CallArguments.protoField) hown (by simp [KeyBound.admits, ha, hproto])
  refine ⟨fun y hy => ⟨flds, oid, rfl, hnp, fun f l hl hk => ?_⟩,
    fun y hy => ⟨flds, oid, rfl, hnp, fun f l hl hk => ?_⟩⟩
  · obtain ⟨p, hp, hpk, hpy⟩ :=
      (hkeys _ (ownKeysT_mem ha hown hl)).1 y hy (IndexKeys.may_of_admits hk)
    obtain ⟨flds', l', c, oid', he, hl', hc, hag⟩ := fields_at hrefs hw p hp
    cases he
    rw [hpk, hl] at hl'
    cases hl'
    exact ⟨c, hc, fun j hj W' u hu => hr j hj _ _ hpy W' u (hag j hj W' u hu)⟩
  · obtain ⟨p, hp, hpk, hpy, hyp⟩ :=
      (hkeys _ (ownKeysT_mem ha hown hl)).2 y hy (IndexKeys.may_of_admits hk)
    obtain ⟨flds', l', c, oid', he, hl', hc, hag⟩ := fields_agree hrefs p hp
    cases he
    rw [hpk, hl] at hl'
    cases hl'
    exact ⟨c, hc, fun j hj W' u => ⟨fun hu => hr j hj _ _ hpy W' u ((hag j hj W' u).mp hu),
      fun hu => (hag j hj W' u).mpr (hr j hj _ _ hyp W' u hu)⟩⟩

/-- A record's field or view named by `viewOf` is at its location, whose
contract implies the field's family. -/
theorem viewOf_at {G : NormalGraph ι} {η : MixedAssignment ι} {P F : List ι} {k : PropKey}
    (hF : viewOf G P k = some F) {n : Nat} {W : WorldT n} {p : Val}
    (hp : mixedValues G η P n W p) :
    ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr n) (oid : Nat),
      p = .objAt flds .absent oid ∧ flds.lookup k = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → mixedValues G η F j U u := by
  unfold viewOf at hF
  split at hF
  · rename_i a bs vs os ms ks hE
    have hplain := plain_of_mem_expand (G := G) (S := P) (c := .refs a bs vs os ms ks) (by simp [hE])
    obtain ⟨c', hc', hsem, -⟩ := (mixed_expand η hplain n W p).mp hp
    rw [hE, List.mem_singleton] at hc'
    subst hc'
    obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hF
    have hk : f.1 = k := by simpa using List.find?_some hf
    obtain ⟨flds, l, c, oid, hρ, hl1, hl2, hag⟩ := fields_at hsem.1 hsem.2.1 f (List.mem_of_find?_eq_some hf)
    exact ⟨flds, l, c, oid, hρ, hk ▸ hl1, hl2, hag⟩
  · cases hF

/-- A member of a type whose one record clause excludes a key lacks it. -/
theorem lacksKey_at {G : NormalGraph ι} {η : MixedAssignment ι} {P : List ι} {k : PropKey}
    (hk : lacksKey G P k) {n : Nat} {W : WorldT n} {p : Val} (hp : mixedValues G η P n W p) :
    ∃ (flds : List (PropKey × Nat)) (oid : Nat), p = .objAt flds .absent oid ∧ flds.lookup k = none := by
  unfold lacksKey at hk
  split at hk
  · rename_i a bs vs os ms ks hE
    have hplain := plain_of_mem_expand (G := G) (S := P) (c := .refs a bs vs os ms ks) (by simp [hE])
    obtain ⟨c', hc', hsem, -⟩ := (mixed_expand η hplain n W p).mp hp
    rw [hE, List.mem_singleton] at hc'
    subst hc'
    obtain ⟨K, hK, hnot⟩ := hk
    have hown := hsem.2.2.2.2 K hK
    obtain ⟨flds, oid, rfl, -⟩ := hown
    exact ⟨flds, oid, rfl, ownKeysT_lookup (hsem.2.2.2.2 K hK) hnot⟩
  · exact hk.elim

/-- A prototype found along the chain holds the member: every member of the
prototype type, below the level, in every world extending the host's, holds
the key the same number of prototypes up, its contract implying the target's
signatures invoked on the host. -/
theorem protoHolds_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {known : Known ι} {self : List ι} {q : MethodMembers.Sig (List ι)}
    (hknown : ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    {n : Nat} (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n)
    {W : WorldT n} {v : Val}
    (hself : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      mixedValues G η self j U v) :
    ∀ (d : Nat) (P : List ι), ProtoHolds G sub R known self q d P → ∃ e : Nat,
      ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
        ∀ p, mixedValues G η P j U p →
          MethodMembers.along q.key
            (MethodMembers.onHost (excOf G) v (MethodMembers.Member.of (mixedValues G η) (mixedArgs G η) q)) e j U p := by
  -- Found on the prototype itself: its field or view of the key holds a
  -- function covering the signature, as an own one would.
  have found : ∀ P, FoundOn G sub R known self q P →
      ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
        ∀ p, mixedValues G η P j U p →
          MethodMembers.along q.key
            (MethodMembers.onHost (excOf G) v (MethodMembers.Member.of (mixedValues G η) (mixedArgs G η) q)) 0 j U p := by
    intro P hview j hj U hU p hp
    have hx : ∀ i (hi : i < j) (U' : WorldT i), WExt (trunc i (Nat.le_of_lt hi) U) U' →
        WExt (trunc i (Nat.le_of_lt (Nat.lt_trans hi hj)) W) U' := by
      intro i hi U' hU'
      have := WExt_trunc (Nat.le_of_lt hi) hU
      rw [trunc_trunc] at this
      exact WExt_trans this hU'
    rcases hview with ⟨k, hk, hF, hby⟩ | ⟨F, hF, hby⟩
    · obtain ⟨pf, l, c, oid, rfl, hl1, hl2, hag⟩ := viewOf_at hF hp
      exact ⟨pf, l, c, oid, rfl, hl1, hl2, fun i hi U' hU' u hu =>
        covers_arrows_sound hby hr hpa hself (Nat.lt_trans hi hj) (hx i hi U' hU')
          (hknown k hk i U' u (hag i hi U' u hu))⟩
    · obtain ⟨pf, l, c, oid, rfl, hl1, hl2, hag⟩ := viewOf_at (Option.mem_toList.mp hF) hp
      exact ⟨pf, l, c, oid, rfl, hl1, hl2, fun i hi U' hU' u hu =>
        covers_by_function_sound hby hr hpa hre hself (Nat.lt_trans hi hj) (hx i hi U' hU')
          (hag i hi U' u hu)⟩
  intro d
  induction d with
  | zero => intro P h; exact ⟨0, found P h⟩
  | succ d ih =>
    intro P h
    rcases h with h | ⟨hk, P', hP', h⟩
    · exact ⟨0, found P h⟩
    · -- Further up: the prototype lacks the key, and its own prototype
      -- location holds one of `P'`, which holds the key `e` up.
      obtain ⟨e, he⟩ := ih P' h
      refine ⟨e + 1, fun j hj U hU p hp => ?_⟩
      obtain ⟨pf, oid, rfl, hmiss⟩ := lacksKey_at hk hp
      obtain ⟨pf', l, c, oid', hρ, hl1, hl2, hag⟩ := viewOf_at (Option.mem_toList.mp hP') hp
      cases hρ
      refine ⟨pf, oid, rfl, hmiss, pf, l, c, oid, rfl, hl1, hl2, fun i hi U' hU' u hu => ?_⟩
      have hx : WExt (trunc i (Nat.le_of_lt (Nat.lt_trans hi hj)) W) U' := by
        have := WExt_trunc (Nat.le_of_lt hi) hU
        rw [trunc_trunc] at this
        exact WExt_trans this hU'
      exact he i (Nat.lt_trans hi hj) U' hx u (hag i hi U' u hu)

/-- Covered methods: each target member is read from the location a source
member of its key names, whose contract implies the target's signatures on the
same host; or from a field or view holding a function whose receiver the host
is in, below the level, in every extending world; or, when the object lacks
the key, from such a function its prototype holds. -/
theorem covers_methods_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {known : Known ι} {self : List ι} {fields : List (PropKey × List ι)} {bounds : List KeyBound}
    {ms ns : List (MethodMembers.Sig (List ι))} (hc : CoversMethods G sub R known self fields bounds ms ns)
    (hknown : ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n)
    (W : WorldT n) (v : Val)
    (hself : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      mixedValues G η self j U v)
    (hfields : ∀ f ∈ fields, ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr n) (oid : Nat),
      v = .objAt flds .absent oid ∧ flds.lookup f.1 = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → mixedValues G η f.2 j U u)
    (hbounds : ∀ K ∈ bounds, ownKeysT K n W v)
    (hv : MethodMembers.methodT (excOf G) (ms.map (MethodMembers.Member.of (mixedValues G η) (mixedArgs G η))) n W v) :
    MethodMembers.methodT (excOf G) (ns.map (MethodMembers.Member.of (mixedValues G η) (mixedArgs G η))) n W v := by
  intro mq hmq
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmq
  rcases hc q hq with ⟨p, hp, hkey, hpq⟩ | ⟨f, hf, hkey, hby⟩ | ⟨⟨K, hK, hnot⟩, f, hf, hpk, hview⟩
  · exact MethodMembers.memberT_mono (by simpa [MethodMembers.Member.of] using hkey)
      (fun w j hj U u hu => covers_sig_sound hpq j (fun i hi => hr i (by omega))
        (fun i hi => hpa i (by omega)) (hr j hj) U w u hu)
      (MethodMembers.methodT_at (List.mem_map_of_mem hp) hv)
  · obtain ⟨flds, l, c, oid, hρ, hfl, hl, hag⟩ := hfields f hf
    exact ⟨0, flds, l, c, oid, hρ, by simpa [MethodMembers.Member.of, ← hkey] using hfl, hl,
      fun j hj U hU u hu => covers_by_function_sound hby hr hpa hre hself hj hU (hag j hj U u hu)⟩
  · obtain ⟨flds, lp, cp, oid, rfl, hfl, hlp, hpag⟩ := hfields f hf
    obtain ⟨e, he⟩ := protoHolds_sound hknown hr hpa hre hself protoChainDepth f.2 hview
    exact ⟨e + 1, flds, oid, rfl, ownKeysT_lookup (hbounds K hK) hnot,
      flds, lp, cp, oid, rfl, by rw [← hpk]; exact hfl, hlp,
      fun j hj U hU p hp => he j hj U hU p (hpag j hj U p hp)⟩

/-- The same argument for a callable object's property bag, which forgets the
call slot but names the same locations. -/
theorem covers_bags_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {a c : List (PropKey × List ι)} {bs ds : List (List (PropKey × List ι))}
    (hc : CoversFields R (a :: bs) (c :: ds)) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j)
    (W : WorldT n) (v : Val)
    (hv : CallableConjunctions.propsT (famsOf (mixedValues G η) a)
      (bs.map (famsOf (mixedValues G η))) n W v) :
    CallableConjunctions.propsT (famsOf (mixedValues G η) c)
      (ds.map (famsOf (mixedValues G η))) n W v := by
  obtain ⟨flds, code, oid, he, hval, hbag⟩ := hv.1
  subst he
  have hsrc : ∀ x ∈ a :: bs, recT (famsOf (mixedValues G η) x) n W (.objAt flds .absent oid) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hbag
    · obtain ⟨flds', code', oid', he', -, hbag'⟩ := hv.2 _ (List.mem_map_of_mem hx)
      cases he'
      exact hbag'
  have key := covers_recs hc n hr W flds hsrc
  exact ⟨⟨flds, code, oid, rfl, hval, key c (by simp)⟩, fun B hB => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
    exact ⟨flds, code, oid, rfl, hval, key b (List.mem_cons_of_mem c hb)⟩⟩

/-- The same argument for a class value's readonly static fields: each
target view is a source field or view within it, on the one object the bag
is of. -/
theorem covers_bag_views_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {a : List (PropKey × List ι)} {bs : List (List (PropKey × List ι))}
    {vs ws : List (PropKey × List ι)}
    (hc : CoversBagViews R (a :: bs) vs ws) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j)
    (W : WorldT n) (v : Val)
    (hp : CallableConjunctions.propsT (famsOf (mixedValues G η) a)
      (bs.map (famsOf (mixedValues G η))) n W v)
    (hv : CallableConjunctions.viewsT (famsOf (mixedValues G η) vs) n W v) :
    CallableConjunctions.viewsT (famsOf (mixedValues G η) ws) n W v := by
  obtain ⟨flds, code, oid, rfl, -, ha⟩ := hp.1
  have hsrc : refsT (famsOf (mixedValues G η) a) (bs.map (famsOf (mixedValues G η))) n W
      (.objAt flds .absent oid) := by
    refine ⟨ha, fun B hB => ?_⟩
    obtain ⟨flds', code', oid', he, -, hb⟩ := hp.2 B hB
    cases he
    exact hb
  have hvv : viewT (famsOf (mixedValues G η) vs) n W (.objAt flds .absent oid) := by
    obtain ⟨flds', code', oid', he, h⟩ := hv
    cases he
    exact h
  refine ⟨flds, code, oid, rfl, fun f T hm => ?_⟩
  obtain ⟨y, hy, rfl⟩ := mem_famsOf.mp hm
  obtain ⟨⟨pf, pl⟩, hp, hpf, hpy⟩ := hc (f, y) hy
  simp only at hpf
  subst hpf
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
    have hL' : recT (famsOf (mixedValues G η) L) n W (.objAt flds .absent oid) := by
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hsrc.1
      · exact hsrc.2 _ (List.mem_map_of_mem hL)
    obtain ⟨flds', l, c0, oid', he, hf, hl, hag⟩ := recT_at (mem_famsOf.mpr ⟨pl, hpL, rfl⟩) hL'
    exact ⟨flds', l, c0, oid', he, hf, hl, fun j hj W' u hu => hr j hj pl y hpy W' u ((hag j hj W' u).mp hu)⟩
  · obtain ⟨flds', l, c0, oid', he, hf, hl, hag⟩ := viewT_at (mem_famsOf.mpr ⟨pl, hp, rfl⟩) hvv
    exact ⟨flds', l, c0, oid', he, hf, hl, fun j hj W' u hu => hr j hj pl y hpy W' u (hag j hj W' u hu)⟩

theorem CoversPack.position {R : List ι → List ι → Prop} {p q : Tuple (List ι)}
    (hc : CoversPack R p q) : ∀ i a, p.position i = some a → ∃ b, q.position i = some b ∧ R a b := by
  have hpos := hc.2.2
  intro i a ha
  have hcov : PositionCovers R (p.position i) (q.position i) := by
    by_cases hiN : i ≤ max (p.required.length + p.optional.length)
        (q.required.length + q.optional.length)
    · exact hpos i (List.mem_range.mpr (by omega))
    · have h := hpos _ (List.mem_range.mpr (Nat.lt_succ_self _))
      have e1 : p.position i = p.position (max (p.required.length + p.optional.length)
          (q.required.length + q.optional.length)) := by
        rw [Tuple.position_beyond (by omega), Tuple.position_beyond (by omega)]
      have e2 : q.position i = q.position (max (p.required.length + p.optional.length)
          (q.required.length + q.optional.length)) := by
        rw [Tuple.position_beyond (by omega), Tuple.position_beyond (by omega)]
      rwa [e1, e2]
  rw [ha] at hcov
  cases hq : q.position i with
  | none => rw [hq] at hcov; exact hcov.elim
  | some b => rw [hq] at hcov; exact ⟨b, rfl, hcov⟩

theorem Tuple.position_mem {t : Tuple α} {i : Nat} {A : α} (h : t.position i = some A) :
    A ∈ t.required ++ t.optional ++ t.rest.toList := by
  unfold Tuple.position at h
  split at h
  · rename_i a ha; cases h; simp [List.mem_of_getElem? ha]
  · split at h
    · rename_i a ha; cases h; simp [List.mem_of_getElem? ha]
    · split at h
      · simp [h]
      · cases h

theorem admitsUndefined_sound {G : NormalGraph ι} {η : MixedAssignment ι} {A : List ι}
    (h : AdmitsUndefined G A) (j : Nat) (U : WorldT j) : mixedValues G η A j U .undef := by
  obtain ⟨c, hc, he⟩ := h
  have he : c = .undef ∨ c = .top ∨ c = .source := by cases c <;> simp_all [shape]
  apply mixed_expand_mpr
  rcases he with rfl | rfl | rfl
  · exact ⟨.undef, expand_sub hc, ⟨rfl, builtinInvariant_of_withoutInvariant rfl _ _ _⟩⟩
  · exact ⟨.top, expand_sub hc, ⟨⟨rfl, trivial⟩, builtinInvariant_of_withoutInvariant rfl _ _ _⟩⟩
  · exact ⟨.source, expand_sub hc, ⟨⟨rfl, trivial⟩, builtinInvariant_of_not_plain (fun _ _ h => nomatch h)⟩⟩

theorem excludesUndefined_sound {G : NormalGraph ι} {η : MixedAssignment ι} {A : List ι}
    (h : ExcludesUndefined G A) (j : Nat) (U : WorldT j) : ¬ mixedValues G η A j U .undef := by
  intro hv
  obtain ⟨c, hc, hs⟩ := (mixed_expand η h.1 j U .undef).mp hv
  have hc' := h.2 c hc
  have hn : c ≠ .top := by intro he; subst he; exact hc'.2 rfl
  have hj : c ≠ .source := by intro he; subst he; exact hc'.2 rfl
  exact hc'.1 (semWithArgs_shape hn hj hs.1).symm

theorem covers_presence_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {p q : Tuple (List ι)} (hc : CoversPresence G R p q) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j)
    (ls : List (Option Nat))
    (hb : p.rest = none → ls.length ≤ p.required.length + p.optional.length)
    (hd : ∀ j, j < n → StorePresence (tupleFams (mixedValues G η) p) ls j) :
    ∀ j, j < n → StorePresence (tupleFams (mixedValues G η) q) ls j := by
  have named : ∀ i, ls[i]? = some none → ∃ A, p.position i = some A := by
    intro i hi
    cases ha : p.position i with
    | some A => exact ⟨A, rfl⟩
    | none =>
      obtain ⟨h1,h2⟩ := Tuple.position_none ha
      have := hb h2
      have := (List.getElem?_eq_some_iff.mp hi).1
      omega
  intro j hj
  have hd := hd j hj
  cases hq : q.presence with
  | sparse => simp [StorePresence, tupleFams, hq]
  | dense =>
    simp only [CoversPresence, hq] at hc
    simp only [StorePresence, tupleFams, hq]
    rcases hc with hp | ⟨hp, hex⟩
    · simpa [StorePresence, tupleFams, hp] using hd
    · intro hm
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
      obtain ⟨A, ha⟩ := named i hi
      simp only [StorePresence, show (tupleFams (mixedValues G η) p).presence = .readable from hp] at hd
      have hs := hd i hi _ (by rw [positionFam_tupleFams, ha]; rfl)
      exact excludesUndefined_sound (hex A (Tuple.position_mem ha)) j (ofList []) (hs (ofList []))
  | readable =>
    simp only [CoversPresence, hq] at hc
    rcases hc with hp | ⟨hp, hc⟩ | ha
    · exact StorePresence.of_dense (by simpa [StorePresence, tupleFams, hp] using hd) j
    · simp only [StorePresence, show (tupleFams (mixedValues G η) q).presence = .readable from hq]
      intro i hi B hB U
      obtain ⟨A, hA⟩ := named i hi
      obtain ⟨b, hb, hab⟩ := CoversPack.position hc i A hA
      rw [positionFam_tupleFams, hb] at hB
      cases hB
      simp only [StorePresence, show (tupleFams (mixedValues G η) p).presence = .readable from hp] at hd
      exact hr j hj A b hab U .undef (hd i hi _ (by rw [positionFam_tupleFams, hA]; rfl) U)
    · simp only [StorePresence, show (tupleFams (mixedValues G η) q).presence = .readable from hq]
      intro i hi B hB U
      rw [positionFam_tupleFams] at hB
      obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp hB
      exact admitsUndefined_sound (ha b (Tuple.position_mem hb)) j U

/-- A same-shape covered tuple contract holds of the same store: every
position's location carries a contract both families identify. -/
theorem covers_shape_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {p q : Tuple (List ι)} (hc : CoversShape R p q) (hpresence : CoversPresence G R p q) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j)
    (W : WorldT n) (v : Val) (hv : listT (tupleFams (mixedValues G η) p) n W v) :
    listT (tupleFams (mixedValues G η) q) n W v := by
  obtain ⟨hreqLen, hoptLen, hreqR, hoptR, hrestR, hmode⟩ := hc
  obtain ⟨ls, rfl, hd, hlen, hbound, hreq, hopt, hrest⟩ := hv
  simp only [listT, tupleFams, List.length_map, List.getElem?_map, Option.map_eq_none_iff,
    Option.map_eq_some_iff] at hlen hbound hreq hopt hrest ⊢
  refine ⟨ls, rfl, (covers_presence_sound hpresence n hr ls hbound hd), hreqLen ▸ hlen, ?_, ?_, ?_, ?_⟩
  · intro hn
    have hpn : p.rest = none := by
      cases hp : p.rest <;> cases hq : q.rest <;> simp_all [CoversRest]
    have := hbound hpn
    omega
  · rintro i A ⟨y, hy, rfl⟩
    have hi : i < q.required.length := (List.getElem?_eq_some_iff.mp hy).1
    obtain ⟨x, hx⟩ : ∃ x, p.required[i]? = some x :=
      List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩ |> fun h => ⟨_, h⟩
    obtain ⟨l, c, hl, hw, hag⟩ := hreq i (mixedValues G η x) ⟨x, hx, rfl⟩
    have hxy := hreqR (x, y) (List.getElem?_zip_eq_some.mpr ⟨hx, hy⟩ |> List.mem_of_getElem?)
    exact ⟨l, c, hl, hw, fun j hj W' u =>
      (hag j hj W' u).weaken hmode (hr j hj _ _ hxy.1 W' u) (fun hro => hr j hj _ _ (hxy.2 hro) W' u)⟩
  · rintro i A l ⟨y, hy, rfl⟩ hl
    have hi : i < q.optional.length := (List.getElem?_eq_some_iff.mp hy).1
    obtain ⟨x, hx⟩ : ∃ x, p.optional[i]? = some x :=
      List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩ |> fun h => ⟨_, h⟩
    obtain ⟨c, hw, hag⟩ := hopt i (mixedValues G η x) l ⟨x, hx, rfl⟩ (hreqLen ▸ hl)
    have hxy := hoptR (x, y) (List.getElem?_zip_eq_some.mpr ⟨hx, hy⟩ |> List.mem_of_getElem?)
    exact ⟨c, hw, fun j hj W' u =>
      (hag j hj W' u).weaken hmode (hr j hj _ _ hxy.1 W' u) (fun hro => hr j hj _ _ (hxy.2 hro) W' u)⟩
  · intro i l hi hl
    obtain ⟨E, c, ⟨e, he, rfl⟩, hw, hag⟩ := hrest i l (by omega) hl
    cases hq : q.rest with
    | none => simp [he, hq, CoversRest] at hrestR
    | some y =>
      have hx : R e y ∧ (q.readonly = false → R y e) := by simpa [he, hq, CoversRest] using hrestR
      exact ⟨mixedValues G η y, c, ⟨y, rfl, rfl⟩, hw,
        fun j hj W' u => (hag j hj W' u).weaken hmode (hr j hj _ _ hx.1 W' u) (fun hro => hr j hj _ _ (hx.2 hro) W' u)⟩

/-- A readonly tuple contract covered position by position holds of the same
store: each element present is at a position of the source, whose contract
reads within the target's position, and the target only reads. -/
theorem covers_readonly_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {p q : Tuple (List ι)} (hro : q.readonly = true) (hc : CoversPack R p q) (hpresence : CoversPresence G R p q) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j)
    (W : WorldT n) (v : Val) (hv : listT (tupleFams (mixedValues G η) p) n W v) :
    listT (tupleFams (mixedValues G η) q) n W v := by
  obtain ⟨hreqLen, hrestB, hpos⟩ := hc
  obtain ⟨ls, rfl, hd, hlen, hbound, hreq, hopt, hrest⟩ := hv
  simp only [listT, tupleFams, List.length_map, List.getElem?_map, Option.map_eq_none_iff,
    Option.map_eq_some_iff] at hlen hbound hreq hopt hrest ⊢
  -- Each element present has a location whose contract its source position
  -- identifies.
  have src : ∀ i l, ls[i]? = some (some l) → ∃ a c, p.position i = some a ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < n) (W' : WorldT j) (u : Val),
        SlotContract p.readonly (c j hj W' u) (mixedValues G η a j W' u) := by
    intro i l hl
    by_cases h1 : i < p.required.length
    · obtain ⟨x, hx⟩ : ∃ x, p.required[i]? = some x := ⟨_, List.getElem?_eq_getElem h1⟩
      obtain ⟨l', c, hl', hw, hag⟩ := hreq i _ ⟨x, hx, rfl⟩
      rw [hl] at hl'
      cases hl'
      exact ⟨x, c, by simp [Tuple.position, hx], hw, hag⟩
    · by_cases h2 : i < p.required.length + p.optional.length
      · obtain ⟨x, hx⟩ : ∃ x, p.optional[i - p.required.length]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨c, hw, hag⟩ := hopt (i - p.required.length) _ l ⟨x, hx, rfl⟩
          (by rw [show p.required.length + (i - p.required.length) = i by omega]; exact hl)
        refine ⟨x, c, ?_, hw, hag⟩
        simp [Tuple.position, List.getElem?_eq_none (show p.required.length ≤ i by omega), hx]
      · obtain ⟨E, c, ⟨e, he, rfl⟩, hw, hag⟩ := hrest i l (by omega) hl
        exact ⟨e, c, by rw [Tuple.position_beyond (by omega), he], hw, hag⟩
  have cov := CoversPack.position (R := R) (p := p) (q := q) ⟨hreqLen, hrestB, hpos⟩
  -- A readonly target's contract only reads.
  have slot : ∀ {c : Ctr n} {a b : List ι}, R a b →
      (∀ (j : Nat) (hj : j < n) (W' : WorldT j) (u : Val),
        SlotContract p.readonly (c j hj W' u) (mixedValues G η a j W' u)) →
      ∀ (j : Nat) (hj : j < n) (W' : WorldT j) (u : Val),
        SlotContract q.readonly (c j hj W' u) (mixedValues G η b j W' u) := by
    intro c a b hab hag j hj W' u
    exact (hag j hj W' u).weaken (fun h => by simp [hro] at h) (hr j hj _ _ hab W' u)
      (fun h => by simp [hro] at h)
  refine ⟨ls, rfl, (covers_presence_sound hpresence n hr ls hbound hd), by omega, ?_, ?_, ?_, ?_⟩
  · intro hn
    obtain ⟨hp, hle⟩ := hrestB hn
    have := hbound hp
    omega
  · rintro i A ⟨y, hy, rfl⟩
    have hi : i < q.required.length := (List.getElem?_eq_some_iff.mp hy).1
    obtain ⟨x, hx⟩ : ∃ x, p.required[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨l, -, hl, -, -⟩ := hreq i _ ⟨x, hx, rfl⟩
    obtain ⟨a, c, ha, hw, hag⟩ := src i l hl
    obtain ⟨b, hb, hab⟩ := cov i a ha
    have hy' : q.position i = some y := by simp [Tuple.position, hy]
    rw [hy'] at hb
    cases hb
    exact ⟨l, c, hl, hw, slot hab hag⟩
  · rintro i A l ⟨y, hy, rfl⟩ hl
    obtain ⟨a, c, ha, hw, hag⟩ := src _ l hl
    obtain ⟨b, hb, hab⟩ := cov _ a ha
    have hy' : q.position (q.required.length + i) = some y := by
      simp [Tuple.position, hy]
    rw [hy'] at hb
    cases hb
    exact ⟨c, hw, slot hab hag⟩
  · intro i l hi hl
    obtain ⟨a, c, ha, hw, hag⟩ := src i l hl
    obtain ⟨b, hb, hab⟩ := cov i a ha
    rw [Tuple.position_beyond (by omega)] at hb
    exact ⟨mixedValues G η b, c, ⟨b, hb, rfl⟩, hw, slot hab hag⟩

/-- A covered tuple contract holds of the same store. -/
theorem covers_tuple_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {p q : Tuple (List ι)} (hc : CoversTuple G R p q) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j)
    (W : WorldT n) (v : Val) (hv : listT (tupleFams (mixedValues G η) p) n W v) :
    listT (tupleFams (mixedValues G η) q) n W v := by
  obtain ⟨hpresence, hc⟩ := hc
  cases hq : q.readonly with
  | true => rw [hq] at hc; exact covers_readonly_sound hq hc hpresence n hr W v hv
  | false => rw [hq] at hc; exact covers_shape_sound hc hpresence n hr W v hv

theorem covers_lists_sound {G : NormalGraph ι} {η : MixedAssignment ι} {R : List ι → List ι → Prop}
    {a c : Tuple (List ι)} {bs ds : List (Tuple (List ι))}
    (hc : ∀ q ∈ c :: ds, ∃ p ∈ a :: bs, CoversTuple G R p q) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j)
    (W : WorldT n) (v : Val)
    (hv : listT (tupleFams (mixedValues G η) a) n W v ∧ ∀ b ∈ bs, listT (tupleFams (mixedValues G η) b) n W v) :
    listT (tupleFams (mixedValues G η) c) n W v ∧ ∀ b ∈ ds, listT (tupleFams (mixedValues G η) b) n W v := by
  have each : ∀ q ∈ c :: ds, listT (tupleFams (mixedValues G η) q) n W v := by
    intro q hq
    obtain ⟨p, hp, hpq⟩ := hc q hq
    have hpv : listT (tupleFams (mixedValues G η) p) n W v := by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hv.1
      · exact hv.2 p hp
    exact covers_tuple_sound hpq n hr W v hpv
  exact ⟨each c (by simp), fun b hb => each b (List.mem_cons_of_mem c hb)⟩

/-- Coverage depends on tuple shape and covariant element membership, not on
whether that membership is read now or below a step-index guard. -/
theorem covers_arguments {R : List ι → List ι → Prop}
    {p q : Tuple (List ι)} (hc : CoversPack R p q)
    (X : List ι → Fam) (member : Fam → Val → Prop)
    (hr : ∀ S T, R S T → ∀ v, member (X S) v → member (X T) v)
    (vs : List Val) (hv : TupleFits member (tupleFams X p) vs) :
    TupleFits member (tupleFams X q) vs := by
  obtain ⟨hreq, hrest, hpos⟩ := hc
  obtain ⟨hlen, hbound, hel⟩ := hv
  have hlen' : p.required.length ≤ vs.length := by simpa [tupleFams] using hlen
  have hbound' : p.rest = none → vs.length ≤ p.required.length + p.optional.length := by
    simpa [tupleFams] using hbound
  refine ⟨?_, ?_, ?_⟩
  · simp only [tupleFams, List.length_map]; omega
  · simp only [tupleFams, List.length_map, Option.map_eq_none_iff]
    intro hn
    obtain ⟨hp, hle⟩ := hrest hn
    have := hbound' hp
    omega
  · intro i u B hu hB
    rw [positionFam_tupleFams] at hB
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hB
    have hi : i < vs.length := (List.getElem?_eq_some_iff.mp hu).1
    cases ha : p.position i with
    | none =>
      obtain ⟨h1, h2⟩ := Tuple.position_none ha
      have := hbound' h2
      omega
    | some a =>
      have hcov : PositionCovers R (p.position i) (q.position i) := by
        by_cases hiN : i ≤ max (p.required.length + p.optional.length)
            (q.required.length + q.optional.length)
        · exact hpos i (List.mem_range.mpr (by omega))
        · have h := hpos _ (List.mem_range.mpr (Nat.lt_succ_self _))
          have e1 : p.position i = p.position (max (p.required.length + p.optional.length)
              (q.required.length + q.optional.length)) := by
            rw [Tuple.position_beyond (by omega), Tuple.position_beyond (by omega)]
          have e2 : q.position i = q.position (max (p.required.length + p.optional.length)
              (q.required.length + q.optional.length)) := by
            rw [Tuple.position_beyond (by omega), Tuple.position_beyond (by omega)]
          rwa [e1, e2]
      rw [ha, hb] at hcov
      exact hr a b hcov u
        (hel i u (X a) hu (by rw [positionFam_tupleFams, ha]; rfl))

/-- A clause the built-ins' invariant applies to is covered by no top. -/
theorem CoversWith.not_top [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {R known arrows self} {a b : Clause (List ι)}
    (hc : CoversWith G sub R known arrows self a b) (hb : b.carriesInvariant = true) : a ≠ .top := by
  rintro rfl
  unfold CoversWith at hc
  cases b <;> simp_all [Clause.carriesInvariant, sourceClause]

/-- **Construct signatures, soundly.** A class value meeting construct
signatures meets every one they cover: each target signature's actual lists
are lists of a covering source signature, and its result is within the
target's, read below the level. -/
theorem covers_ctors_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {η : MixedAssignment ι}
    {R : List ι → List ι → Prop} {known : Known ι} {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    {self : List ι} {L M : List (List (List ι) × List ι)} {S T : List (List (List ι) × List ι × List ι)}
    {a c : List (PropKey × List ι)} {bs ds : List (List (PropKey × List ι))} {vs ws : List (PropKey × List ι)}
    (hc : CoversWith G sub R known arrows self (.ctors L S a bs vs) (.ctors M T c ds ws)) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (W : WorldT n) (v : Val) :
    semWithArgs Ξ (mixedValues G η) (mixedArgs G η) (.ctors L S a bs vs) n W v →
      semWithArgs Ξ (mixedValues G η) (mixedArgs G η) (.ctors M T c ds ws) n W v := by
  unfold CoversWith at hc
  rintro ⟨⟨hv, hw⟩, hb, hvs⟩
  refine ⟨⟨⟨hv.1, fun q hq => ?_⟩, ⟨hv.1, fun t ht => ?_⟩⟩, covers_bags_sound hc.2.1 n hr W v hb,
    covers_bag_views_sound hc.2.2 n hr W v hb hvs⟩
  · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    obtain ⟨p, hp, hd, hres⟩ := hc.1.1 q0 hq0
    intro j hj U hx hu heap hh args hvals ha
    rcases hd with hd | hnever
    · obtain ⟨result, hcon, hsafe⟩ := hv.2 _ (List.mem_map_of_mem hp) j hj U hx hu heap hh args hvals
        (Domains.sound hd (fun a b hab => hr j hj a b hab) ha)
      exact ⟨result, hcon, Safe_mono j (fun m hm V u hu => hr m (by omega) _ _ hres V u hu) U heap _ hsafe⟩
    · -- No actual meets `never`: the promise is vacuous.
      obtain ⟨a, ha'⟩ := ArgsT_mem ha (List.mem_map_of_mem hnever)
      exact absurd ha' (by simp [mixedValues, setSem])
  · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
    rcases hc.1.2 t0 ht0 with ⟨s, hs, hd, hrest, hres⟩ | ⟨p, hp, hfp⟩
    · intro j hj U hx hu heap hh args hvals ha
      obtain ⟨hlen, hfix, hpack⟩ := ha
      have hl : t0.1.length = s.1.length := Domains.length_eq hd
      simp only [List.length_map] at hlen hfix hpack
      obtain ⟨result, hcon, hsafe⟩ := hw.2 _ (List.mem_map_of_mem hs) j hj U hx hu heap hh args
        hvals ⟨by simpa [← hl] using hlen,
          by simpa [← hl] using Domains.sound hd (fun a b hab => hr j hj a b hab) hfix,
          by simpa [← hl] using hpa j hj _ _ hrest U _ hpack⟩
      exact ⟨result, hcon, Safe_mono j (fun m hm V u hu => hr m (by omega) _ _ hres V u hu) U heap _ hsafe⟩
    · unfold FixedCoversPack at hfp
      split at hfp
      · rename_i τ hP
        obtain ⟨hopt, hrest, hd, hres⟩ := hfp
        intro j hj U hx hu heap hh args hvals ha
        obtain ⟨hlen, hfix, hpack⟩ := ha
        simp only [List.length_map] at hlen hfix hpack
        have htup := mixed_pack_exact hP hopt hrest hpack
        have hall := ArgsT_append hfix htup
        rw [List.take_append_drop, ← List.map_append] at hall
        obtain ⟨result, hcon, hsafe⟩ := hv.2 _ (List.mem_map_of_mem hp) j hj U hx hu heap hh
          args hvals (Domains.sound hd (fun a b hab => hr j hj a b hab) hall)
        exact ⟨result, hcon, Safe_mono j (fun m hm V u hu => hr m (by omega) _ _ hres V u hu)
          U heap _ hsafe⟩
      · exact hfp.elim


/-- Coverage of the clauses themselves, the row's invariant aside. -/
theorem Covers.sound_raw [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {η : MixedAssignment ι} {R known self a b}
    (hc : Covers G sub R known self a b)
    (hknown : ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n)
    (W : WorldT n) (v : Val)
    (hself : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      mixedValues G η self j U v) :
    semWithArgs (excOf G) (mixedValues G η) (mixedArgs G η) a n W v →
      semWithArgs (excOf G) (mixedValues G η) (mixedArgs G η) b n W v := by
  by_cases hb : b = .top
  · subst hb; exact fun hv => semWithArgs_value hv
  by_cases hjs : b = .source
  · subst b
    have hc : sourceClause a = true := by unfold Covers CoversWith at hc; cases a <;> simpa using hc
    exact fun hv => sourceClause_sound hc hv
  unfold Covers CoversWith at hc
  cases a <;> cases b <;> simp only at hc
  all_goals try contradiction
  all_goals try exact absurd rfl hb
  all_goals try exact absurd rfl hjs
  case pack.pack => exact fun h => h.elim
  case refs.dict a bs vs os ms ks c ds ws iy ps ns ls cy =>
    intro hv
    exact ⟨covers_fields_sound hc.2.1 n hr W v hv.1, covers_views_sound hc.2.2.1 n hr W v ⟨hv.1, hv.2.1⟩,
      covers_keys_sound hc.1 n hr W v hv.1 hv.2.1 hv.2.2.2.2,
      covers_optional_sound hc.2.2.2.1 n hr W v ⟨hv.1, hv.2.1, hv.2.2.1⟩ hv.2.2.2.2,
      covers_methods_sound hc.2.2.2.2.1 hknown n hr hpa hre W v hself (fields_at hv.1 hv.2.1) hv.2.2.2.2
        hv.2.2.2.1,
      covers_bounds_sound hc.2.2.2.2.2.1 (recT_obj hv.1.1) hv.2.2.2.2⟩
  case dict.refs a bs vs ix os ms ks cx c ds ws ps ns ls =>
    intro hv
    exact ⟨covers_fields_sound hc.1 n hr W v hv.1, covers_views_sound hc.2.1 n hr W v ⟨hv.1, hv.2.1⟩,
      covers_optional_sound hc.2.2.1 n hr W v ⟨hv.1, hv.2.1, hv.2.2.2.1⟩ hv.2.2.2.2.2,
      covers_methods_sound hc.2.2.2.1 hknown n hr hpa hre W v hself (fields_at hv.1 hv.2.1) hv.2.2.2.2.2
        hv.2.2.2.2.1,
      covers_bounds_sound hc.2.2.2.2 (recT_obj hv.1.1) hv.2.2.2.2.2⟩
  case ctors.ctors L S a bs vs M T c ds ws =>
    exact covers_ctors_sound (sub := sub) (known := known) (self := self)
      (arrows := fun L S M => ∀ p ∈ M, CallArrow (compatible G) (restElem G) R L S p)
      (by unfold CoversWith; exact hc) n hr hpa W v
  · exact id
  · exact id
  · rename_i a bs vs os ms ks c ds ws ps ns ls
    intro hv
    exact ⟨covers_fields_sound hc.1 n hr W v hv.1, covers_views_sound hc.2.1 n hr W v ⟨hv.1, hv.2.1⟩,
      covers_optional_sound hc.2.2.1 n hr W v ⟨hv.1, hv.2.1, hv.2.2.1⟩ hv.2.2.2.2,
      covers_methods_sound hc.2.2.2.1 hknown n hr hpa hre W v hself (fields_at hv.1 hv.2.1) hv.2.2.2.2
        hv.2.2.2.1,
      covers_bounds_sound hc.2.2.2.2 (recT_obj hv.1.1) hv.2.2.2.2⟩
  · rename_i a bs vs ix os ms ks cx c ds ws iy ps ns ls cy
    intro hv
    refine ⟨covers_fields_sound hc.1 n hr W v hv.1,
      covers_views_sound hc.2.1 n hr W v ⟨hv.1, hv.2.1⟩, ⟨?_, ?_⟩,
      covers_optional_sound hc.2.2.2.1 n hr W v ⟨hv.1, hv.2.1, hv.2.2.2.1⟩ hv.2.2.2.2.2,


      covers_methods_sound hc.2.2.2.2.1 hknown n hr hpa hre W v hself (fields_at hv.1 hv.2.1) hv.2.2.2.2.2
        hv.2.2.2.2.1,
      covers_bounds_sound hc.2.2.2.2.2.1 (recT_obj hv.1.1) hv.2.2.2.2.2⟩
    · intro y hy
      obtain ⟨x, hx, hw, hxy⟩ := hc.2.2.1.1 y hy
      obtain ⟨flds, oid, he, hp, hfs⟩ := dictViewT_within hw (hv.2.2.1.1 x hx)
      refine ⟨flds, oid, he, hp, ?_⟩
      intro f l hl hk
      obtain ⟨c, hw, hag⟩ := hfs f l hl hk
      exact ⟨c, hw, fun j hj W' u hu => hr j hj x.2 y.2 hxy W' u (hag j hj W' u hu)⟩
    · intro y hy
      obtain ⟨x, hx, hw, hxy, hyx⟩ := (hc.2.2.1.2 y hy).1
      obtain ⟨flds, oid, he, hp, hfs⟩ := dictCellT_within hw (hv.2.2.1.2 x hx)
      refine ⟨flds, oid, he, hp, ?_⟩
      intro f l hl hk
      obtain ⟨c, hw, hag⟩ := hfs f l hl hk
      exact ⟨c, hw, fun j hj W' u => ⟨fun hu => hr j hj x.2 y.2 hxy W' u ((hag j hj W' u).mp hu),
        fun hu => (hag j hj W' u).mpr (hr j hj y.2 x.2 hyx W' u hu)⟩⟩
  · intro hv
    refine ⟨⟨hv.1.1, fun p hp => ?_⟩, ⟨hv.1.1, fun t ht => ?_⟩⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact CallArrow.sound (hc.1 q hq) n hr W v hv
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      rcases hc.2 t0 ht0 with ⟨s, hs, hst⟩ | ⟨p, hp, hfp⟩
      · exact rest_covers_sound hst n hr hpa W v (hv.2.2 _ (List.mem_map_of_mem hs))
      · exact fixed_calls_pack_sound hfp n hr W v (hv.1.2 _ (List.mem_map_of_mem hp))
  · rename_i b
    cases b <;> intro hv <;> cases hv
    · exact Or.inr rfl
    · exact Or.inl rfl
  · cases hc; exact id
  · -- num ≤ num
    exact id
  · -- numLit ≤ num: the singleton inhabits the family
    rename_i b
    intro hv; cases hv; exact ⟨b, rfl⟩
  · -- numLit ≤ numLit at equal spellings
    cases hc; exact id
  · exact id
  · intro hv
    refine ⟨⟨hv.1.2.1, fun p hp => ?_⟩, ⟨hv.1.2.1, fun t ht => ?_⟩⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact CallArrow.sound (hc.1 q hq) n hr W v ⟨hv.1.2, hv.2⟩
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      rcases hc.2 t0 ht0 with ⟨s, hs, hst⟩ | ⟨p, hp, hfp⟩
      · exact rest_covers_sound hst n hr hpa W v (hv.2.2 _ (List.mem_map_of_mem hs))
      · exact fixed_calls_pack_sound hfp n hr W v (hv.1.2.2 _ (List.mem_map_of_mem hp))
  · rename_i a bs L S c ds M T
    intro hv
    refine ⟨⟨covers_bags_sound hc.1 n hr W v hv.1.1, hv.1.2.1, fun p hp => ?_⟩,
      ⟨hv.1.2.1, fun t ht => ?_⟩⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact CallArrow.sound (hc.2.1 q hq) n hr W v ⟨hv.1.2, hv.2⟩
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      rcases hc.2.2 t0 ht0 with ⟨s, hs, hst⟩ | ⟨p, hp, hfp⟩
      · exact rest_covers_sound hst n hr hpa W v (hv.2.2 _ (List.mem_map_of_mem hs))
      · exact fixed_calls_pack_sound hfp n hr W v (hv.1.2.2 _ (List.mem_map_of_mem hp))
  · -- str ≤ str
    exact id
  · -- strLit ≤ str: the singleton inhabits the family
    rename_i s
    intro hv; cases hv; exact ⟨s, rfl⟩
  · -- strLit ≤ strLit at equal strings
    cases hc; exact id
  · rename_i a bs c ds
    intro hv
    exact covers_lists_sound hc n hr W v hv
  · -- bigint ≤ bigint
    exact id
  · -- symbol ≤ symbol
    exact id
  · -- bigintLit ≤ bigint: the singleton inhabits the family
    rename_i i
    intro hv; cases hv; exact ⟨i, rfl⟩
  · -- bigintLit ≤ bigintLit at equal integers
    cases hc; exact id
  · -- symbolLit ≤ symbol: the singleton inhabits the family
    rename_i i
    intro hv; cases hv; exact ⟨i, rfl⟩
  · -- symbolLit ≤ symbolLit at equal identities
    cases hc; exact id

/-- Coverage in a row: a record target's invariant is the record source's. -/
theorem Covers.sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {η : MixedAssignment ι} {R known self a b}
    (hc : Covers G sub R known self a b)
    (hknown : ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n)
    (W : WorldT n) (v : Val)
    (hself : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      mixedValues G η self j U v) :
    mixedSem G η a n W v → mixedSem G η b n W v := by
  rintro ⟨hv, hinv⟩
  refine ⟨Covers.sound_raw hc hknown n hr hpa hre W v hself hv, ?_⟩
  cases hbr : b.carriesInvariant
  · exact builtinInvariant_of_withoutInvariant hbr n W v
  · exact builtinInvariant_of_member ⟨hv, hinv⟩ (CoversWith.not_top hc hbr) hbr

/-- A type's meaning is a family of closed values. -/
theorem meaning_valueFam (G : NormalGraph ι) (S : List ι) : ValueFam (meaning G S) :=
  ⟨setSem_adm (normalDenote_adm G) S, fun _ _ _ ⟨_, _, h⟩ => normalDenote_value h⟩

/-- An element rest admits the lists of its element's values. -/
theorem restElem_args {G : NormalGraph ι} {E El : List ι} (hel : restElem G E = some El)
    {n W vs} : argMeaning G E n W vs ↔ ∀ v ∈ vs, meaning G El n W v :=
  mixed_restElem hel

/-- A meet row, `p ⊓ cs`: neither a parameter nor a scheme row, with a meet. -/
@[nospecialize] def _root_.Verification.PositiveGraphs.NormalGraph.meetRow (G : NormalGraph ι) (i : ι) : Bool :=
  !G.params i && (G.schemes i).isNone && (G.meets i).isSome

/-- A member of a meet row is in one of its clauses. -/
theorem meet_clause_of {G : NormalGraph ι} {η : MixedAssignment ι} {i : ι}
    (h : G.meetRow i = true) {n W v}
    (hv : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    ∃ c ∈ ((G.meets i).map (·.2)).getD [], mixedSem G η c n W v := by
  simp only [NormalGraph.meetRow, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at h
  obtain ⟨⟨hp, hs⟩, hm⟩ := h
  obtain ⟨pc, hm⟩ := Option.isSome_iff_exists.mp hm
  rw [qDenoteWithArgs_unfold] at hv
  simp only [qLayerWithArgs, hp, hs, hm, Bool.false_eq_true, ite_false] at hv
  obtain ⟨c, hc, hcv⟩ := hv.2
  exact ⟨c, by simp [hm, hc], hcv⟩

/-- A meet row below a row by its parameters: the row is one of the meet's
value parameters, or a meet row of some of them within clauses including the
meet's. `U ⊓ T` is below `T`, `U ⊓ T ⊓ B` below `T ⊓ B`, and `T ⊓ number`
below `T ⊓ (number | null)`: a value of the meet is what the assignment gives
each of its parameters, within its clauses. In a
family pair a target parameter may instead be above one of the meet's
parameters by a hypothesis (RECURSIVE-EQUATIONS §3.3, §7.3): `x ⊓ B` is below
`y ⊓ B`, and below `y`, when `x ≤ y`. -/
@[nospecialize] def meetBelow [DecidableEq ι] (G : NormalGraph ι) (i j : ι) (hyps : List (ι × ι) := []) : Bool :=
  match G.meets i with
  | some (p, cs) =>
    let ps := p :: G.meetParams i
    let reach := fun q => ps.contains q ||
      (G.params q && ps.any fun r => G.params r && hyps.contains (r, q))
    (G.parameterKinds j == some .value && reach j) ||
    (match G.meets j with
      | some (q, ds) => !G.params j && (G.schemes j).isNone && reach q &&
          (G.meetParams j).all reach &&
          (cs.all (ds.contains ·) || ds == [.top] || (ds == [.source] && cs.all sourceClause))
      | none => false)
  | none => false

/-- **Quantified signatures.** A scheme row is covered by another binding the
same parameter rows, each source bound among the target's, whose signatures,
the binders opaque, the source's cover: every instance the target admits the
source admits too, and at that instance the target's signatures follow from
the source's by the ordinary arrow coverage. This is the subtyping rule for
quantified signatures restricted as F<:'s kernel rule is (Pierce 1994): the
binders are the same, so the target's are taken rigidly and the source's are
instantiated at them, and no bound is compared, so the check stays decidable.
Its premises hold at the reassigned assignment, which the family's
induction over every assignment supplies (`family_sound`). -/
@[nospecialize] def SchemeCoversWith [DecidableEq ι] (G : NormalGraph ι) (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop)
    (i j : ι) : Prop :=
  match G.schemes i, G.schemes j with
  | some s, some s' => G.params i = false ∧ G.params j = false ∧ s.binders = s'.binders ∧
      (∀ b ∈ s.bounds, b ∈ s'.bounds) ∧ sameShape s s' = true ∧
      CoversWith G none R known arrows [] s.body s'.body
  | _, _ => False

/-- A row read as a meet part: not a meet row (RECURSIVE-EQUATIONS §3.3). -/
@[nospecialize] def _root_.Verification.PositiveGraphs.NormalGraph.partRow (G : NormalGraph ι) (q : ι) : Bool :=
  G.params q || (G.schemes q).isSome || (G.meets q).isNone

/-- A meet row with a scheme part. A finite table has none. -/
@[nospecialize] def schemeMeet (G : NormalGraph ι) (i : ι) : Bool :=
  (meetParts G i).any fun q => (G.schemes q).isSome

/-- **A meet source, read through one part** (RECURSIVE-EQUATIONS §3.3): a
parameter part below a target row (`meetBelow`), a scheme part covered by a
target scheme (`sc`), or its clauses each covered (`cover`). -/
@[nospecialize] def MeetSource [DecidableEq ι] (G : NormalGraph ι) (sc : ι → ι → Prop)
    (cover : Clause (List ι) → Prop) (T : List ι) (i : ι) : Prop :=
  T.any (meetBelow G i ·) = true ∨
    (∃ q ∈ meetParts G i, G.partRow q = true ∧ ∃ j ∈ T, sc q j) ∨
    ∀ a ∈ (meetClauses G i).flatMap splitClause, cover a

/-- Clause shapes, a meet's clause restriction, or callable membership establish
that a row contains only JavaScript values. -/
@[nospecialize] def sourceRow (G : NormalGraph ι) (i : ι) : Bool :=
  if G.params i then false else
    if (G.schemes i).isSome then true else
      match G.meets i with
      | some (_, cs) => cs.all sourceClause
      | none => (G i).all sourceClause

@[nospecialize] def sourceTy (G : NormalGraph ι) (A : List ι) : Bool :=
  A.all (sourceRow G)

theorem sourceTy_exc {G : NormalGraph ι} {A : List ι}
    (checked : sourceTy G A = true) (η : MixedAssignment ι) :
    FamLe (mixedValues G η A) (excOf G) := by
  intro n W v hv
  obtain ⟨i, hi, hv⟩ := hv
  have hc := List.all_eq_true.mp checked i hi
  unfold sourceRow at hc
  split at hc
  · cases hc
  · rename_i hp
    have hp : G.params i = false := Bool.eq_false_iff.mpr hp
    rw [qDenoteWithArgs_unfold] at hv
    simp only [qLayerWithArgs, hp, Bool.false_eq_true, ite_false] at hv
    cases hs : G.schemes i with
    | some s =>
      rw [hs] at hv
      have hn := hv.1.not_plain
      obtain ⟨fs, code, oid, rfl, hscoped⟩ := hv.1.obj
      exact ⟨⟨rfl, hscoped⟩, builtinInvariant_of_not_plain hn⟩
    | none =>
      simp only [hs, Option.isSome_none, Bool.false_eq_true, ite_false] at hc hv
      cases hm : G.meets i with
      | some p =>
        rw [hm] at hv hc
        obtain ⟨c, hc', hv⟩ := hv.2
        exact builtinExc_of_member hv (List.all_eq_true.mp hc c hc')
      | none =>
        rw [hm] at hv hc
        obtain ⟨c, hc', hv⟩ := hv
        exact builtinExc_of_member hv (List.all_eq_true.mp hc c hc')

/-- A type of JavaScript values. -/
theorem sourceTy_sound {G : NormalGraph ι} {A : List ι}
    (checked : sourceTy G A = true) (η : MixedAssignment ι) :
    FamLe (mixedValues G η A) sourceT :=
  fun n W v hv => (sourceTy_exc checked η n W v hv).1

/-- **A meet target, read part by part**: each part of a target meet row is
the source row, one of the source meet's parts, or a scheme the source row or
one of its scheme parts covers; its clauses admit every value or are the
source meet's own. -/
@[nospecialize] def MeetTarget [DecidableEq ι] (G : NormalGraph ι) (sc : ι → ι → Prop) (T : List ι) (i : ι) : Prop :=
  ∃ j ∈ T, G.meetRow j = true ∧
    (∀ q ∈ meetParts G j, G.partRow q = true ∧
      (q = i ∨ (G.meetRow i = true ∧ q ∈ meetParts G i) ∨ sc i q ∨
        (G.meetRow i = true ∧ ∃ s ∈ meetParts G i, G.partRow s = true ∧ sc s q))) ∧
    ((meetClauses G j = [.top] ∨ (meetClauses G j = [.source] ∧ sourceRow G i = true)) ∨ (G.meetRow i = true ∧ meetClauses G i = meetClauses G j))

/-- An opaque meet: a source meet row, whose clauses `meetSources` lists
unless it has a scheme part, which is then read through one part; or a
target meet read part by part. -/
@[nospecialize] def MeetOpaque [DecidableEq ι] (G : NormalGraph ι) (sc : ι → ι → Prop)
    (cover : Clause (List ι) → Prop) (T : List ι) (i : ι) : Prop :=
  (G.meetRow i = true ∧ (schemeMeet G i = false ∨ MeetSource G sc cover T i)) ∨
    MeetTarget G sc T i

theorem MeetOpaque.mono [DecidableEq ι] {G : NormalGraph ι} {sc sc' : ι → ι → Prop}
    {cover cover' : Clause (List ι) → Prop} {T : List ι} {i : ι}
    (hs : ∀ a b, sc a b → sc' a b) (hc : ∀ a, cover a → cover' a)
    (h : MeetOpaque G sc cover T i) : MeetOpaque G sc' cover' T i := by
  rcases h with ⟨hm, h | h | ⟨q, hq, hp, j, hj, h⟩ | h⟩ | ⟨j, hj, hm, hq, hcl⟩
  · exact .inl ⟨hm, .inl h⟩
  · exact .inl ⟨hm, .inr (.inl h)⟩
  · exact .inl ⟨hm, .inr (.inr (.inl ⟨q, hq, hp, j, hj, hs _ _ h⟩))⟩
  · exact .inl ⟨hm, .inr (.inr (.inr fun a ha => hc a (h a ha)))⟩
  · refine .inr ⟨j, hj, hm, fun q hqm => ?_, hcl⟩
    obtain ⟨hp, h | h | h | ⟨hi, s, hs', hsp, h⟩⟩ := hq q hqm
    · exact ⟨hp, .inl h⟩
    · exact ⟨hp, .inr (.inl h)⟩
    · exact ⟨hp, .inr (.inr (.inl (hs _ _ h)))⟩
    · exact ⟨hp, .inr (.inr (.inr ⟨hi, s, hs', hsp, hs _ _ h⟩))⟩

/-- A part row means what the step reads for it as a part. -/
theorem part_denote {G : NormalGraph ι} {η : MixedAssignment ι} {q : ι}
    (hq : G.partRow q = true) {n W v} :
    qDenoteWithArgs G (mixedParameters G) (η, q) n W v ↔
      partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) η q n W v := by
  rw [qDenoteWithArgs_unfold, qLayer_part]
  simpa [NormalGraph.partRow, Bool.or_eq_true, Option.isNone_iff_eq_none, or_assoc] using hq

/-- A value of a meet row is a value of a row it is below, given the
hypotheses at the value's level. -/
theorem meetBelow_sound [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι} {i j : ι}
    {hyps : List (ι × ι)} (hi : G.meetRow i = true) (h : meetBelow G i j hyps = true) {n W v}
    (hh : ∀ h ∈ hyps, FamLeAt G η [h.1] [h.2] n)
    (hv : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    qDenoteWithArgs G (mixedParameters G) (η, j) n W v := by
  simp only [NormalGraph.meetRow, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hi
  obtain ⟨⟨hp, hs⟩, hm⟩ := hi
  obtain ⟨⟨p, cs⟩, hm⟩ := Option.isSome_iff_exists.mp hm
  rw [qDenoteWithArgs_unfold] at hv
  simp only [qLayerWithArgs, hp, hs, hm, Bool.false_eq_true, ite_false] at hv
  obtain ⟨⟨hvp, hvq⟩, hvc⟩ := hv
  -- Each of the meet's parameters holds the value.
  have hpar : ∀ r, r ∈ p :: G.meetParams i →
      partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) η r n W v := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hvp
    · exact hvq r hr
  -- So does each parameter above one of them by a hypothesis.
  have hreach : ∀ q, (q ∈ p :: G.meetParams i ∨ G.params q = true ∧
      ∃ r ∈ p :: G.meetParams i, G.params r = true ∧ (r, q) ∈ hyps) →
      partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) η q n W v := by
    rintro q (hq | ⟨hq, r, hr, hrp, hrq⟩)
    · exact hpar q hq
    · have hrv := (part_denote (by simp [NormalGraph.partRow, hrp])).mpr (hpar r hr)
      obtain ⟨q', hq', hqv⟩ := hh (r, q) hrq W v ⟨r, List.mem_singleton_self r, hrv⟩
      cases List.mem_singleton.mp hq'
      exact (part_denote (by simp [NormalGraph.partRow, hq])).mp hqv
  unfold meetBelow at h
  simp only [hm, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
    List.any_eq_true] at h
  rcases h with ⟨hk, hj⟩ | h
  · -- A parameter of the meet, or above one by a hypothesis.
    have hjp : G.params j = true := by simp [NormalGraph.params, hk]
    rw [qDenoteWithArgs_unfold]
    simp only [qLayerWithArgs, hjp, ite_true]
    simpa [partSemWithArgs_param hjp] using hreach j hj
  · -- A meet row of such parameters within the same clauses.
    cases hmj : G.meets j with
    | none => simp [hmj] at h
    | some qd =>
      obtain ⟨q, ds⟩ := qd
      simp only [hmj, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none,
        beq_iff_eq, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
        List.all_eq_true] at h
      obtain ⟨⟨⟨⟨hjp, hjs⟩, hq⟩, hqs⟩, hcs⟩ := h
      rw [qDenoteWithArgs_unfold]
      simp only [qLayerWithArgs, hjp, hjs, hmj, Bool.false_eq_true, ite_false]
      refine ⟨⟨hreach q hq, fun r hr => hreach r (hqs r hr)⟩, ?_⟩
      rcases hcs with (hsub | rfl) | ⟨rfl, hs⟩
      · obtain ⟨c, hc, hv⟩ := hvc
        exact ⟨c, hsub c hc, hv⟩
      · obtain ⟨c, _, hv, _⟩ := hvc
        exact ⟨.top, List.mem_singleton_self _, semWithArgs_value hv,
          builtinInvariant_of_withoutInvariant rfl n W v⟩
      · obtain ⟨c, hc, hv, hinv⟩ := hvc
        exact ⟨.source, List.mem_singleton_self _, builtinExc_of_member ⟨hv, hinv⟩ (hs c hc)⟩

/-- **A meet row means its parts and its clauses**, each read at the meet's
own level. -/
theorem meet_row_iff {G : NormalGraph ι} {η : MixedAssignment ι} {i : ι}
    (h : G.meetRow i = true) {n W v} :
    qDenoteWithArgs G (mixedParameters G) (η, i) n W v ↔
      (∀ q ∈ meetParts G i,
        partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) η q n W v) ∧
      ∃ c ∈ meetClauses G i, mixedSem G η c n W v := by
  simp only [NormalGraph.meetRow, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at h
  obtain ⟨⟨hp, hs⟩, hm⟩ := h
  obtain ⟨⟨p, cs⟩, hm⟩ := Option.isSome_iff_exists.mp hm
  rw [qDenoteWithArgs_unfold]
  simp only [qLayerWithArgs, hp, hs, hm, Bool.false_eq_true, ite_false, meetParts_of hm,
    meetClauses, Option.map_some, Option.getD_some, List.forall_mem_cons]
  rfl

/-- A member of a meet row is a member of each of its part rows. -/
theorem meet_part_value {G : NormalGraph ι} {η : MixedAssignment ι} {i q : ι}
    (h : G.meetRow i = true) (hq : q ∈ meetParts G i) (hp : G.partRow q = true) {n W v}
    (hv : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    qDenoteWithArgs G (mixedParameters G) (η, q) n W v :=
  (part_denote hp).mpr (((meet_row_iff h).mp hv).1 q hq)

/-- A value in each part of a target meet row, and in its clauses, is in it. -/
theorem meet_target_value {G : NormalGraph ι} {η : MixedAssignment ι} {i j : ι}
    {sc : ι → ι → Prop} (hj : G.meetRow j = true) {n W v}
    (hsc : ∀ a b, sc a b → qDenoteWithArgs G (mixedParameters G) (η, a) n W v →
      qDenoteWithArgs G (mixedParameters G) (η, b) n W v)
    (hparts : ∀ q ∈ meetParts G j, G.partRow q = true ∧
      (q = i ∨ (G.meetRow i = true ∧ q ∈ meetParts G i) ∨ sc i q ∨
        (G.meetRow i = true ∧ ∃ s ∈ meetParts G i, G.partRow s = true ∧ sc s q)))
    (hcl : (meetClauses G j = [.top] ∨ (meetClauses G j = [.source] ∧ sourceRow G i = true)) ∨ (G.meetRow i = true ∧ meetClauses G i = meetClauses G j))
    (hv : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    qDenoteWithArgs G (mixedParameters G) (η, j) n W v := by
  refine (meet_row_iff hj).mpr ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨hqp, h | ⟨hi, hqi⟩ | h | ⟨hi, s, hs, hsp, h⟩⟩ := hparts q hq
    · subst h; exact (part_denote hqp).mp hv
    · exact ((meet_row_iff hi).mp hv).1 q hqi
    · exact (part_denote hqp).mp (hsc _ _ h hv)
    · exact (part_denote hqp).mp (hsc _ _ h (meet_part_value hi hs hsp hv))
  · rcases hcl with (h | ⟨h, hs⟩) | ⟨hi, h⟩
    · rw [h]
      exact ⟨.top, List.mem_singleton_self _, mixedDenote_value G η i hv,
        builtinInvariant_of_withoutInvariant rfl n W v⟩
    · rw [h]
      have hsource : sourceTy G [i] = true := by simpa [sourceTy] using hs
      exact ⟨.source, List.mem_singleton_self _,
        sourceTy_exc hsource η n W v ⟨i, List.mem_singleton_self _, hv⟩⟩
    · rw [← h]
      exact ((meet_row_iff hi).mp hv).2


/-- Opaque callable rows belong to the JavaScript universe; calculus top
also admits arbitrary internal values. -/
@[nospecialize] def OpaqueUniverse [DecidableEq ι] (G : NormalGraph ι) (T : List ι) (i : ι) : Prop :=
  .top ∈ clausesOf G T ∨
    (.source ∈ clausesOf G T ∧ G.params i = false ∧ (G.schemes i).isSome = true)

instance [DecidableEq ι] (G : NormalGraph ι) (T : List ι) (i : ι) :
    Decidable (OpaqueUniverse G T i) := by unfold OpaqueUniverse; infer_instance

/-- The clauses of the source's meet rows the target does not name, split as
source clauses are: a member of a meet row `p ⊓ cs` is in one of `cs`, so the
row is below a target covering each of them. A bounded binder read as its
meet with its bound is below the bound this way. -/
@[nospecialize] def meetSources [DecidableEq ι] (G : NormalGraph ι) (S T : List ι) (hyps : List (ι × ι) := []) :
    List (Clause (List ι)) :=
  ((S.filter fun i => G.meetRow i && !schemeMeet G i && decide (i ∉ T) &&
      !T.any (meetBelow G i · hyps)).flatMap
    fun i => ((G.meets i).map (·.2)).getD []).flatMap splitClause

/-- A subtype edge relates two value types or two argument-list types.
The empty type is admissible at either sort; a runtime top is not a list top. -/
@[nospecialize] def SameKind (G : NormalGraph ι) (S T : List ι) : Bool :=
  (G.hasKind .value S && G.hasKind .value T) ||
    (G.hasKind .arguments S && G.hasKind .arguments T)

/-- Sorted argument types contribute pack clauses only. -/
private theorem argument_clause {G : NormalGraph ι} {S : List ι}
    (hs : G.hasKind .arguments S = true) {c : Clause (List ι)} (hc : c ∈ clausesOf G S) :
    ∃ a bs, c = .pack a bs := by
  obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
  have hp := NormalGraph.plain_of_clauses hc
  have hparts := NormalGraph.plain_iff.mp hp
  have hkind : G.parameterKinds i = none := by simpa [NormalGraph.params] using hparts.1
  have hk := List.all_eq_true.mp hs i hi
  have hm : c ∈ G.rows i := by simpa [NormalGraph.clauses, hp] using hc
  simp only [hkind, hparts.2.1, hparts.2.2, Option.isSome_none, Bool.or_false,
    Bool.false_eq_true, ite_false] at hk
  have hh := List.all_eq_true.mp hk c hm
  cases c <;> simp_all

theorem mixedMeaning_union (G : NormalGraph ι) (η : MixedAssignment ι)
    (S : List ι) (n : Nat) (W : WorldT n) (x : Val ⊕ List Val) :
    mixedMeaning G η S n W x ↔ ∃ i ∈ S, mixedMeaning G η [i] n W x := by
  cases x <;> simp [mixedMeaning, mixedParameters, graphArguments, setSem]

theorem mixed_subset {G : NormalGraph ι} {η : MixedAssignment ι} {S T : List ι}
    (h : ∀ i ∈ S, i ∈ T) : FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  intro n W x hx
  obtain ⟨i, hi, hx⟩ := (mixedMeaning_union G η S n W x).mp hx
  exact (mixedMeaning_union G η T n W x).mpr ⟨i, h i hi, hx⟩

/-- Arrow coverage alone: a callable clause's signatures, covered, give the
target's. It reads no source type. -/
theorem covers_arrs_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {η : MixedAssignment ι} {R known self}
    {L : Ops ι} {S : List (RestArrow (List ι))}
    {M : Ops ι} {T : List (RestArrow (List ι))}
    (hc : Covers G sub R known self (.arrs L S) (.arrs M T)) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (W : WorldT n) (v : Val) :
    semWithArgs Ξ (mixedValues G η) (mixedArgs G η) (.arrs L S) n W v →
      semWithArgs Ξ (mixedValues G η) (mixedArgs G η) (.arrs M T) n W v := by
  unfold Covers CoversWith at hc
  simp only at hc
  intro hv
  refine ⟨⟨hv.1.1, fun p hp => ?_⟩, ⟨hv.1.1, fun t ht => ?_⟩⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact CallArrow.sound (hc.1 q hq) n hr W v hv
  · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
    rcases hc.2 t0 ht0 with ⟨s, hs, hst⟩ | ⟨p, hp, hfp⟩
    · exact rest_covers_sound hst n hr hpa W v (hv.2.2 _ (List.mem_map_of_mem hs))
    · exact fixed_calls_pack_sound hfp n hr W v (hv.1.2 _ (List.mem_map_of_mem hp))

/-- **A scheme body, soundly.** A scheme's body covers a clause of its own
kind, call signatures by call signatures and construct signatures by
construct signatures, by the clause's coverage. -/
theorem covers_body_sound [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι} {R known}
    {s : SchemeRow ι} {d : Clause (List ι)}
    (hc : Covers G none R known [] s.body d)
    (hd : if s.construct then (∃ M T, d = .ctors M T) else (∃ M T, d = .arrs M T)) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (W : WorldT n) (v : Val) :
    semWithArgs Ξ (mixedValues G η) (mixedArgs G η) s.body n W v →
      semWithArgs Ξ (mixedValues G η) (mixedArgs G η) d n W v := by
  unfold SchemeRow.body at hc ⊢
  cases h : s.construct
  · simp only [h, Bool.false_eq_true, if_false] at hc hd ⊢
    obtain ⟨M, T, rfl⟩ := hd
    exact covers_arrs_sound hc n hr hpa W v
  · simp only [h, if_true] at hc hd ⊢
    obtain ⟨M, T, rfl⟩ := hd
    exact covers_ctors_sound hc n hr hpa W v

/-! ## Instances of a scheme row

An instance of a scheme row is named by an instance map `θ`, sending each row a
signature reaches to a type of the graph: a binder to the type it is
instantiated at, a clause row to a clause row whose clauses are its own with
every operand mapped (the substituted copy the graph already holds, such as
`PromiseLike<boolean>` for `PromiseLike<R1>`), a scheme row to a scheme row
with the same binders and its signatures mapped, and any row that does not
depend on a moved binder to itself. Dependence is by free parameter rows,
stated by a checked certificate (`FreeOk`): a row under a scheme binding a
parameter does not depend on it, so a receiver `Promise<number>`, whose `then`
mentions `then`'s own binders, is its own image. -/

/-! ### Instance tables

An instance is checked by a finite table of entries `(row, context, image)`.
The context says what each binder in scope stands for: an instance type, or,
under a scheme the instance maps to another, that scheme's binder. Under its
context an entry's row means its image. Binder rows shared between scopes, as
the colouring of generic methods makes them, are told apart by the context. -/

/-- What the binders in scope stand for. -/
abbrev Ctx (ι : Type) := List (ι × List ι)

/-- Entries `(row, context, image)`. -/
abbrev InstTable (ι : Type) := List (ι × Ctx ι × List ι)

@[nospecialize] def entryImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (l : ι) : Option (List ι) :=
  (tbl.find? fun e => e.1 == l && e.2.1 == κ).map (·.2.2)

/-- A type's image: its rows' images, each an entry. -/
@[nospecialize] def tyImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (S : List ι) : Option (List ι) :=
  (S.mapM (entryImg tbl κ)).map List.flatten

@[nospecialize] def sigImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (p : Arrow (List ι)) : Option (Arrow (List ι)) := do
  return ⟨← tyImg tbl κ p.receiver, ← p.arguments.mapM (tyImg tbl κ), ← tyImg tbl κ p.result, p.effect⟩

@[nospecialize] def restImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (p : RestArrow (List ι)) :
    Option (RestArrow (List ι)) := do
  return ⟨← tyImg tbl κ p.receiver, (← p.arguments.1.mapM (tyImg tbl κ), ← tyImg tbl κ p.arguments.2),
    ← tyImg tbl κ p.result, p.effect⟩

/-- Two label lists with the same members. A type is the union of its labels,
so their order and repetition carry no meaning. -/
@[nospecialize] def sameLabels [DecidableEq ι] (a b : List ι) : Bool := a.all (· ∈ b) && b.all (· ∈ a)

/-- Two lists of types, position by position with the same members. -/
@[nospecialize] def sameLabelLists [DecidableEq ι] (as bs : List (List ι)) : Bool :=
  as.length == bs.length && (as.zip bs).all fun ab => sameLabels ab.1 ab.2

/-- A signature is a scheme signature's image, up to the members of each type. -/
@[nospecialize] def sigMatch [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (p q : Arrow (List ι)) : Bool :=
  match sigImg tbl κ p with
  | some q' => sameLabels q'.receiver q.receiver && sameLabelLists q'.arguments q.arguments && sameLabels q'.result q.result && q'.effect == q.effect
  | none => false

/-- A variadic signature is a scheme one's image, up to the members of each type. -/
@[nospecialize] def restMatch [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (p q : RestArrow (List ι)) : Bool :=
  match restImg tbl κ p with
  | some q' => sameLabels q'.receiver q.receiver && sameLabelLists q'.arguments.1 q.arguments.1 &&
      sameLabels q'.arguments.2 q.arguments.2 && sameLabels q'.result q.result && q'.effect == q.effect
  | none => false

/-- A signature's parameters and result are a scheme signature's images; its
receiver is not compared. -/
@[nospecialize] def sigBodyMatch [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (p q : Arrow (List ι)) : Bool :=
  match p.arguments.mapM (tyImg tbl κ), tyImg tbl κ p.result with
  | some ps, some r => sameLabelLists ps q.arguments && sameLabels r q.result && p.effect == q.effect
  | _, _ => false

/-- A variadic signature's fixed parameters, rest and result are a scheme
one's images; its receiver is not compared. -/
@[nospecialize] def restBodyMatch [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (p q : RestArrow (List ι)) : Bool :=
  match p.arguments.1.mapM (tyImg tbl κ), tyImg tbl κ p.arguments.2, tyImg tbl κ p.result with
  | some ps, some e, some r => sameLabelLists ps q.arguments.1 && sameLabels e q.arguments.2 && sameLabels r q.result && p.effect == q.effect
  | _, _, _ => false

/-- A receiver universe covers the instance's receiver without a substitution. -/
@[nospecialize] def receiverUniverse [DecidableEq ι] (G : NormalGraph ι) (P Q : List ι) : Bool :=
  expand G P == [.top] ||
    (expand G P == [.source] && sourceTy G Q)

/-- A signature an instance states: a scheme signature's image, or, where the
scheme's receiver admits every value, one whose parameters and result are its
images at any receiver. A callable invoked safely with every receiver is
invoked safely with a narrower one, such as a generic method's scheme, which
the member bound to its host meets whatever receiver it is given, at a call
whose receiver is the host. -/
@[nospecialize] def instSig [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (κ : Ctx ι)
    (p q : Arrow (List ι)) : Bool :=
  (sigMatch tbl κ p { q with effect := p.effect } ||
    (receiverUniverse G p.receiver q.receiver && sigBodyMatch tbl κ p { q with effect := p.effect })) &&
      p.effect.covers q.effect

/-- The same, for a variadic signature. -/
@[nospecialize] def instRest [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (κ : Ctx ι)
    (p q : RestArrow (List ι)) : Bool :=
  (restMatch tbl κ p { q with effect := p.effect } ||
    (receiverUniverse G p.receiver q.receiver && restBodyMatch tbl κ p { q with effect := p.effect })) &&
      p.effect.covers q.effect

/-- The context `κ` on the rows `ps` outside `src`, in the order of `ps`. -/
@[nospecialize] def keep [DecidableEq ι] (κ : Ctx ι) (src ps : List ι) : Ctx ι :=
  ps.filterMap fun p => if src.contains p then none else (κ.lookup p).map (p, ·)

/-- Entering scheme row `i` mapped to another: its binders stand for the
other's, and of the outer context only the free rows of `i` are kept, in the
order `V` lists them. Nothing inside reads another, and the contexts met while
relating recursive types, whose schemes nest without end, are then finitely
many, so their entries recur. -/
@[nospecialize] def enter [DecidableEq ι] (V : FreeMap ι) (i : ι) (κ : Ctx ι) (src tgt : List ι) : Ctx ι :=
  src.zip (tgt.map ([·])) ++ keep κ src (fv V i)

/-- A clause with every operand replaced by its image. -/
@[nospecialize] def clauseImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (c : Clause (List ι)) :
    Clause (List ι) :=
  c.map fun S => (tyImg tbl κ S).getD []

/-- A checked operand image transports a value clause. Both sorts of operands
are required; a value equality alone cannot justify a rest-parameter image. -/
theorem clauseImg_value [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (c : Clause (List ι)) (X Y : List ι → Fam) (P Q : List ι → ArgFam)
    (n : Nat) (W : WorldT n) (v : Val)
    (himg : ∀ S ∈ c.operands, ∃ T, tyImg tbl κ S = some T ∧
      Agree (X S) (Y T) n ∧ Agree (P S) (Q T) n)
    (he : Agree (X []) (Y []) n) (hp : Agree (P []) (Q []) n) :
    semWithArgs Ξ X P c n W v ↔ semWithArgs Ξ Y Q (clauseImg tbl κ c) n W v := by
  let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
  have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
  unfold clauseImg
  rw [semWithArgs_map, ← hcr, semWithArgs_map, semWithArgs_map]
  have h : ∀ S, Agree (X (r S)) (Y ((tyImg tbl κ (r S)).getD [])) n ∧
      Agree (P (r S)) (Q ((tyImg tbl κ (r S)).getD [])) n := by
    intro S
    by_cases hS : S ∈ c.operands
    · obtain ⟨T, hT, hx, ha⟩ := himg S hS
      simpa [r, hS, hT] using And.intro hx ha
    · simpa [r, hS, tyImg] using And.intro he hp
  exact semWithArgs_congr _ _ _ _ n (fun _ _ _ _ => Iff.rfl) (fun S => (h S).1) (fun S => (h S).2) c W v

/-- A checked operand image transports a clause read in a row: the built-ins'
invariant is the same of a clause and of its image. -/
theorem clauseImg_row [DecidableEq ι] {G : NormalGraph ι} (tbl : InstTable ι) (κ : Ctx ι)
    (c : Clause (List ι)) (A X Y : List ι → Fam) (P Q : List ι → ArgFam)
    (n : Nat) (W : WorldT n) (v : Val)
    (himg : ∀ S ∈ c.operands, ∃ T, tyImg tbl κ S = some T ∧
      Agree (X S) (Y T) n ∧ Agree (P S) (Q T) n)
    (he : Agree (X []) (Y []) n) (hp : Agree (P []) (Q []) n) :
    rowSem G A X P c n W v ↔ rowSem G A Y Q (clauseImg tbl κ c) n W v := by
  refine and_congr (clauseImg_value tbl κ c X Y P Q n W v himg he hp) ?_
  unfold clauseImg
  rw [builtinInvariant_map]

/-- The list component of the same checked clause image uses element equality
at this level. Requiring only agreement below it would lose object evidence. -/
theorem clauseImg_arguments [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (c : Clause (List ι)) (X Y : List ι → Fam) (n : Nat) (W : WorldT n) (vs : List Val)
    (himg : ∀ S ∈ c.operands, ∃ T, tyImg tbl κ S = some T ∧
      ∀ v, X S n W v ↔ Y T n W v)
    (he : ∀ v, X [] n W v ↔ Y [] n W v) :
    clauseArguments X c n W vs ↔ clauseArguments Y (clauseImg tbl κ c) n W vs := by
  let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
  have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
  unfold clauseImg
  rw [clauseArguments_map, ← hcr, clauseArguments_map, clauseArguments_map]
  apply clauseArguments_congr _ _ c n W (fun S v => ?_) vs
  by_cases hS : S ∈ c.operands
  · obtain ⟨T, hT, hx⟩ := himg S hS
    simpa [r, hS, hT] using hx v
  · simpa [r, hS, tyImg] using he v

/-- A label list's members, in the order of `U`. -/
@[nospecialize] def canonIn [DecidableEq ι] (U S : List ι) : List ι := U.filter fun l => decide (l ∈ S)

theorem canonIn_same [DecidableEq ι] {U S : List ι} (h : ∀ l ∈ S, l ∈ U) :
    sameLabels (canonIn U S) S = true := by
  simp only [sameLabels, canonIn, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_filter]
  exact ⟨fun l hl => hl.2, fun l hl => ⟨h l hl, by simpa using hl⟩⟩

/-- Two clause lists that are the same up to each operand's members: compared
with every operand listed in one order of all their labels. -/
@[nospecialize] def sameClauses [DecidableEq ι] (Cs Ds : List (Clause (List ι))) : Bool :=
  let U := (Cs ++ Ds).flatMap fun c => c.operands.flatten
  Cs.map (·.map (canonIn U)) == Ds.map (·.map (canonIn U))

/-- A clause's meaning depends on its operands' members only. -/
theorem semWithArgs_members [DecidableEq ι] {X : List ι → Fam} {P : List ι → ArgFam}
    (hX : ∀ S T, sameLabels S T = true → X S = X T) (hP : ∀ S T, sameLabels S T = true → P S = P T)
    {f : List ι → List ι} {c : Clause (List ι)}
    (hf : ∀ S ∈ c.operands, sameLabels (f S) S = true) (hnil : sameLabels (f []) [] = true) :
    semWithArgs Ξ X P (c.map f) = semWithArgs Ξ X P c := by
  let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
  have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
  rw [semWithArgs_map, ← hcr, semWithArgs_map, semWithArgs_map]
  have hr : ∀ S, sameLabels (f (r S)) (r S) = true := fun S => by
    by_cases hS : S ∈ c.operands
    · simpa [r, hS] using hf S hS
    · simpa [r, hS] using hnil
  have h1 : (fun a => X (f (r a))) = fun a => X (r a) := funext fun a => hX _ _ (hr a)
  have h2 : (fun a => P (f (r a))) = fun a => P (r a) := funext fun a => hP _ _ (hr a)
  rw [h1, h2]

/-- A clause's argument lists depend on its operands' members only. -/
theorem clauseArguments_members [DecidableEq ι] {X : List ι → Fam}
    (hX : ∀ S T, sameLabels S T = true → X S = X T)
    {f : List ι → List ι} {c : Clause (List ι)}
    (hf : ∀ S ∈ c.operands, sameLabels (f S) S = true) (hnil : sameLabels (f []) [] = true) :
    clauseArguments X (c.map f) = clauseArguments X c := by
  let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
  have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
  rw [clauseArguments_map, ← hcr, clauseArguments_map, clauseArguments_map]
  have hr : ∀ S, sameLabels (f (r S)) (r S) = true := fun S => by
    by_cases hS : S ∈ c.operands
    · simpa [r, hS] using hf S hS
    · simpa [r, hS] using hnil
  have h1 : (fun a => X (f (r a))) = fun a => X (r a) := funext fun a => hX _ _ (hr a)
  rw [h1]

/-- Clause lists the same up to operand members hold the same members of any
property that depends on operand members only. -/
theorem sameClauses_iff [DecidableEq ι] {Cs Ds : List (Clause (List ι))}
    (h : sameClauses Cs Ds = true) (Q : Clause (List ι) → Prop)
    (hQ : ∀ (c : Clause (List ι)) (f : List ι → List ι),
      (∀ S ∈ c.operands, sameLabels (f S) S = true) → sameLabels (f []) [] = true →
      (Q (c.map f) ↔ Q c)) :
    (∃ c ∈ Cs, Q c) ↔ (∃ d ∈ Ds, Q d) := by
  unfold sameClauses at h
  have heq := beq_iff_eq.mp h
  have canon : ∀ c ∈ Cs ++ Ds,
      Q (c.map (canonIn ((Cs ++ Ds).flatMap fun c => c.operands.flatten))) ↔ Q c := fun c hc =>
    hQ c _ (fun S hS => canonIn_same fun l hl =>
      List.mem_flatMap.mpr ⟨c, hc, List.mem_flatten.mpr ⟨S, hS, hl⟩⟩)
      (by simp [sameLabels, canonIn])
  constructor
  · rintro ⟨c, hc, hq⟩
    have hm := List.mem_map_of_mem (f := (·.map (canonIn ((Cs ++ Ds).flatMap fun c => c.operands.flatten)))) hc
    rw [heq] at hm
    obtain ⟨d, hd, hde⟩ := List.mem_map.mp hm
    exact ⟨d, hd, (canon d (List.mem_append_right _ hd)).mp
      (hde ▸ (canon c (List.mem_append_left _ hc)).mpr hq)⟩
  · rintro ⟨d, hd, hq⟩
    have hm := List.mem_map_of_mem (f := (·.map (canonIn ((Cs ++ Ds).flatMap fun c => c.operands.flatten)))) hd
    rw [← heq] at hm
    obtain ⟨c, hc, hce⟩ := List.mem_map.mp hm
    exact ⟨c, hc, (canon c (List.mem_append_left _ hc)).mp
      (hce ▸ (canon d (List.mem_append_right _ hd)).mpr hq)⟩

/-- A plain row and its checked clause image agree on argument lists, including
unions and intersections of tuple shapes. The element images are supplied by
the value-row proof at this level, not by a second recursive unfolding. -/
theorem graphArguments_image [DecidableEq ι] (G : NormalGraph ι)
    (tbl : InstTable ι) (κ : Ctx ι) (η θ : MixedAssignment ι)
    (X Y : List ι → Fam) (i j : ι) (hi : G.plain i = true) (hj : G.plain j = true)
    (hrows : sameClauses (G j) ((G i).map (clauseImg tbl κ)) = true)
    (hY : ∀ S T, sameLabels S T = true → Y S = Y T) (n : Nat) (W : WorldT n) (vs : List Val)
    (himg : ∀ c ∈ G i, ∀ S ∈ c.operands, ∃ T, tyImg tbl κ S = some T ∧
      ∀ v, X S n W v ↔ Y T n W v)
    (he : ∀ v, X [] n W v ↔ Y [] n W v) :
    graphArguments G η X [i] n W vs ↔ graphArguments G θ Y [j] n W vs := by
  have key := sameClauses_iff hrows (fun d => clauseArguments Y d n W vs)
    (fun c f hf hn => by simp only [clauseArguments_members hY hf hn])
  simp only [graphArguments, List.mem_singleton, exists_eq_left,
    NormalGraph.listParam_of_plain hi, NormalGraph.listParam_of_plain hj, Bool.false_eq_true, if_false]
  rw [key]
  simp only [List.mem_map]
  constructor
  · rintro ⟨c, hc, hv⟩
    exact ⟨_, ⟨c, hc, rfl⟩, (clauseImg_arguments tbl κ c X Y n W vs (himg c hc) he).mp hv⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, hv⟩
    exact ⟨c, hc, (clauseImg_arguments tbl κ c X Y n W vs (himg c hc) he).mpr hv⟩

/-- A bound's image: the target binder at the bound binder's position, and the
bound type's image under the outer context (a bound is read at the scheme's
own assignment, not under its binders). -/
@[nospecialize] def boundImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (src tgt : List ι)
    (b : ι × List ι) : Option (ι × List ι) :=
  match (src.zip (tgt.map ([·]))).lookup b.1 with
  | some [q] => (tyImg tbl κ b.2).map (q, ·)
  | _ => none

/-- The image of a parameter must have its declared sort. -/
@[nospecialize] def substitutionKind (G : NormalGraph ι) (b : ι) (U : List ι) : Bool :=
  match G.parameterKinds b with
  | some k => G.hasKind k U
  | none => false

/-- One kind check is shared by instantiation and table substitution. -/
@[nospecialize] def instKinds (G : NormalGraph ι) (bs : List ι) (θs : List (List ι)) : Bool :=
  (bs.zip θs).all fun (b, U) => substitutionKind G b U

/-- The context fixes row `i`: it gives each free row of `i` nothing, or that
parameter row itself (inside a scheme matched against itself, its binders
stand for themselves). -/
@[nospecialize] def fixedBy [DecidableEq ι] (G : NormalGraph ι) (κ : Ctx ι) (V : FreeMap ι) (i : ι) : Bool :=
  (fv V i).all fun p => match κ.lookup p with
    | none => true
    | some U => U == [p] && G.params p

/-- The clause lists a meet row's image meets: each parameter's image's
clauses, then the clauses mapped. -/
@[nospecialize] def meetOperands [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (κ : Ctx ι)
    (ps : List ι) (cs : List (Clause (List ι))) : List (List (Clause (List ι))) :=
  ps.map (fun p => clausesOf G ((κ.lookup p).getD [])) ++ [cs.map (clauseImg tbl κ)]

/-- A meet of clause lists, left to right: `A ⊓ B ⊓ …`. -/
def meetMany : List (List (Clause α)) → List (Clause α)
  | [] => []
  | A :: rest => rest.foldl meetLists A

/-- A meet row `ps ⊓ cs`'s image under `κ`, row `j`: with `ps` value
parameters, either a meet row whose parameters are the ones `κ` gives `ps`
(each itself where `κ` gives it nothing), with `cs` mapped, or, when `κ` gives
every one of `ps` a type of clause rows, a value clause row holding the meet
of those types' clauses with `cs` mapped, in the order `ps` then `cs`, or the
reverse. -/
@[nospecialize] def meetOk [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (κ : Ctx ι)
    (ps : List ι) (cs : List (Clause (List ι))) (j : ι) : Bool :=
  ps.all (fun p => G.parameterKinds p == some .value) &&
    cs.all (fun c => c.operands.all fun S => (tyImg tbl κ S).isSome) &&
    match G.meets j with
    | some (q, ds) =>
      !G.params j && (G.schemes j).isNone &&
        (q :: G.meetParams j).all (fun r => G.parameterKinds r == some .value) &&
        ps.all (fun p => (q :: G.meetParams j).any fun r => (κ.lookup p).getD [p] == [r]) &&
        (q :: G.meetParams j).all (fun r => ps.any fun p => (κ.lookup p).getD [p] == [r]) &&
        sameClauses ds (cs.map (clauseImg tbl κ))
    | none =>
      ps.all (fun p => (κ.lookup p).isSome) &&
        G.plain j && (ps.map fun p => (κ.lookup p).getD []).all G.plainTy &&
        G.hasKind .value [j] &&
        (sameClauses (G j) (meetMany (meetOperands G tbl κ ps cs)) ||
          sameClauses (G j) (meetMany (meetOperands G tbl κ ps cs).reverse))

/-- One entry. A parameter row's image is what the context gives it, or itself.
A row the context fixes may be its own image. A clause
row's image is a clause row holding its clauses mapped. A meet row's is
`meetOk`'s. A scheme row's image is
a scheme row with as many binders, distinct parameter rows, whose signatures
are its own mapped with its binders standing for them, provided no free row of
the source, nor any row of a free row's image, is one of those binders. -/
@[nospecialize] def entryOk [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (V : FreeMap ι)
    (e : ι × Ctx ι × List ι) : Bool :=
  if G.params e.1 then
    e.2.2 == (e.2.1.lookup e.1).getD [e.1] && substitutionKind G e.1 e.2.2
  else if e.2.2 == [e.1] && fixedBy G e.2.1 V e.1 then true
  else match G.schemes e.1, e.2.2 with
    | some s, [j] =>
      match G.schemes j with
      | some s2 =>
        !G.params j && decide s2.binders.Nodup && s2.binders.length == s.binders.length &&
          s2.binders.all G.params &&
          (s.binders.zip s2.binders).all (fun (a,b) => G.parameterKinds a == G.parameterKinds b) &&
          (fv V e.1).all (fun p => match e.2.1.lookup p with
            | some U => U.all fun l => (fv V l).all fun q => !s2.binders.contains q
            | none => !s2.binders.contains p) &&
          s.signatures.mapM (sigImg tbl (enter V e.1 e.2.1 s.binders s2.binders)) == some s2.signatures &&
          s.bounds.mapM (boundImg tbl e.2.1 s.binders s2.binders) == some s2.bounds &&
          s.variadic.mapM (restImg tbl (enter V e.1 e.2.1 s.binders s2.binders)) == some s2.variadic && sameShape s s2
      | none => false
    | none, [j] =>
      match G.meets e.1 with
      | some (p, cs) => meetOk G tbl e.2.1 (p :: G.meetParams e.1) cs j
      | none =>
        G.plain e.1 && G.plain j &&
          (G e.1).all (fun c => c.operands.all fun S => (tyImg tbl e.2.1 S).isSome) &&
          sameClauses (G j) ((G e.1).map (clauseImg tbl e.2.1))
    | _, _ => false

/-- The rows a table mentions. -/
@[nospecialize] def tableRows (tbl : InstTable ι) : List ι :=
  tbl.flatMap fun e => e.1 :: e.2.2 ++ e.2.1.flatMap (·.2)

/-- A checked table: its rows lie in a domain with a sound free-variable
certificate, and every entry is one of `entryOk`'s. -/
@[nospecialize] def TableOk [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (D : List ι)
    (V : FreeMap ι) : Bool :=
  FreeOk G D V && (tableRows tbl).all (D.contains ·) && tbl.all (entryOk G tbl V)

/-! ### The compiled table check

`TableOk` looks every image up in the whole table, so checking a table's
entries is quadratic in its size, and the tables of a recursive generic
interface run to a thousand entries and more. An entry's lookups are all under
one context, or under the one context it enters, so the compiled check groups
the entries by context once and looks each image up among its context's
entries only. `TableOk_eq_fast` proves the two equal; `csimp` makes the
compiler run the grouped one. What is checked is unchanged. -/

/-- The entries under context `κ`. -/
@[nospecialize] def ctxEntries [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) : InstTable ι :=
  tbl.filter (·.2.1 == κ)

theorem entryImg_ctxEntries [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) :
    entryImg (ctxEntries tbl κ) κ = entryImg tbl κ := by
  funext l
  unfold entryImg ctxEntries
  rw [List.find?_filter]
  congr 2
  funext e
  cases e.1 == l <;> cases e.2.1 == κ <;> rfl

/-- The contexts the table uses. -/
@[nospecialize] def ctxsOf [DecidableEq ι] (tbl : InstTable ι) : List (Ctx ι) := (tbl.map (·.2.1)).eraseDups

/-- The entries of each context the table uses, grouped once. -/
@[nospecialize] def ctxGroups [DecidableEq ι] (tbl : InstTable ι) : List (Ctx ι × InstTable ι) :=
  (ctxsOf tbl).map fun κ => (κ, ctxEntries tbl κ)

/-- A table's rows lie in `D`: each entry's row and image, and the rows of each
context once, not once per entry under it. -/
theorem tableRows_all [DecidableEq ι] (tbl : InstTable ι) (D : List ι) :
    (tableRows tbl).all (D.contains ·) =
      (tbl.all (fun e => (e.1 :: e.2.2).all (D.contains ·)) &&
        (ctxsOf tbl).all fun κ => (κ.flatMap (·.2)).all (D.contains ·)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [tableRows, ctxsOf, Bool.and_eq_true, List.all_eq_true, List.mem_flatMap,
    List.mem_cons, List.mem_append, List.mem_eraseDups, List.mem_map, List.contains_iff_mem]
  constructor
  · intro h
    exact ⟨fun e he x hx => h x ⟨e, he, Or.inl hx⟩,
      fun κ ⟨e, he, hκ⟩ x ⟨b, hb, hx⟩ => h x ⟨e, he, Or.inr ⟨b, hκ ▸ hb, hx⟩⟩⟩
  · rintro ⟨h1, h2⟩ x ⟨e, he, hx | ⟨b, hb, hx⟩⟩
    · exact h1 e he x hx
    · exact h2 e.2.1 ⟨e, he, rfl⟩ x ⟨b, hb, hx⟩

/-- The entries to look an image under `κ` up in: its group, or the whole table. -/
@[nospecialize] def ctxTable [DecidableEq ι] (groups : List (Ctx ι × InstTable ι)) (tbl : InstTable ι)
    (κ : Ctx ι) : InstTable ι :=
  match groups.find? (·.1 == κ) with
  | some g => g.2
  | none => tbl

theorem entryImg_ctxTable [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) :
    entryImg (ctxTable (ctxGroups tbl) tbl κ) κ = entryImg tbl κ := by
  unfold ctxTable
  split
  · rename_i g hg
    have hm := List.mem_of_find?_eq_some hg
    have hk := List.find?_some hg
    simp only [beq_iff_eq] at hk
    simp only [ctxGroups, List.mem_map] at hm
    obtain ⟨κ', _, rfl⟩ := hm
    simp only at hk ⊢
    subst hk
    exact entryImg_ctxEntries tbl _
  · rfl

section
variable [DecidableEq ι] {t u : InstTable ι} {κ : Ctx ι}

theorem tyImg_congr (h : entryImg t κ = entryImg u κ) : tyImg t κ = tyImg u κ := by
  funext S; simp only [tyImg, h]

theorem sigImg_congr (h : entryImg t κ = entryImg u κ) : sigImg t κ = sigImg u κ := by
  funext p; simp only [sigImg, tyImg_congr h]

theorem restImg_congr (h : entryImg t κ = entryImg u κ) : restImg t κ = restImg u κ := by
  funext p; simp only [restImg, tyImg_congr h]

theorem clauseImg_congr (h : entryImg t κ = entryImg u κ) : clauseImg t κ = clauseImg u κ := by
  funext c; simp only [clauseImg, tyImg_congr h]

theorem boundImg_congr (h : entryImg t κ = entryImg u κ) : boundImg t κ = boundImg u κ := by
  funext src tgt b; simp only [boundImg, tyImg_congr h]

theorem meetOk_congr (G : NormalGraph ι) (h : entryImg t κ = entryImg u κ) :
    meetOk G t κ = meetOk G u κ := by
  funext ps cs j; simp only [meetOk, meetOperands, tyImg_congr h, clauseImg_congr h]
end

/-- `entryOk`, each lookup under context `κ` made in `look κ`. -/
@[nospecialize] def entryOkIn [DecidableEq ι] (G : NormalGraph ι) (look : Ctx ι → InstTable ι) (V : FreeMap ι)
    (e : ι × Ctx ι × List ι) : Bool :=
  if G.params e.1 then
    e.2.2 == (e.2.1.lookup e.1).getD [e.1] && substitutionKind G e.1 e.2.2
  else if e.2.2 == [e.1] && fixedBy G e.2.1 V e.1 then true
  else match G.schemes e.1, e.2.2 with
    | some s, [j] =>
      match G.schemes j with
      | some s2 =>
        !G.params j && decide s2.binders.Nodup && s2.binders.length == s.binders.length &&
          s2.binders.all G.params &&
          (s.binders.zip s2.binders).all (fun (a,b) => G.parameterKinds a == G.parameterKinds b) &&
          (fv V e.1).all (fun p => match e.2.1.lookup p with
            | some U => U.all fun l => (fv V l).all fun q => !s2.binders.contains q
            | none => !s2.binders.contains p) &&
          s.signatures.mapM (sigImg (look (enter V e.1 e.2.1 s.binders s2.binders))
            (enter V e.1 e.2.1 s.binders s2.binders)) == some s2.signatures &&
          s.bounds.mapM (boundImg (look e.2.1) e.2.1 s.binders s2.binders) == some s2.bounds &&
          s.variadic.mapM (restImg (look (enter V e.1 e.2.1 s.binders s2.binders))
            (enter V e.1 e.2.1 s.binders s2.binders)) == some s2.variadic && sameShape s s2
      | none => false
    | none, [j] =>
      match G.meets e.1 with
      | some (p, cs) => meetOk G (look e.2.1) e.2.1 (p :: G.meetParams e.1) cs j
      | none =>
        G.plain e.1 && G.plain j &&
          (G e.1).all (fun c => c.operands.all fun S => (tyImg (look e.2.1) e.2.1 S).isSome) &&
          sameClauses (G j) ((G e.1).map (clauseImg (look e.2.1) e.2.1))
    | _, _ => false

theorem entryOkIn_eq [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι)
    (look : Ctx ι → InstTable ι) (V : FreeMap ι)
    (h : ∀ κ, entryImg (look κ) κ = entryImg tbl κ) (e : ι × Ctx ι × List ι) :
    entryOkIn G look V e = entryOk G tbl V e := by
  simp only [entryOkIn, entryOk, sigImg_congr (h _), restImg_congr (h _), boundImg_congr (h _),
    meetOk_congr G (h _), tyImg_congr (h _), clauseImg_congr (h _)]

/-- `TableOk`, grouped by context: what the compiler runs. -/
@[nospecialize] def TableOkFast [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (D : List ι)
    (V : FreeMap ι) : Bool :=
  let ctxs := ctxsOf tbl
  let groups := ctxs.map fun κ => (κ, ctxEntries tbl κ)
  FreeOk G D V &&
    (tbl.all (fun e => (e.1 :: e.2.2).all (D.contains ·)) &&
      ctxs.all fun κ => (κ.flatMap (·.2)).all (D.contains ·)) &&
    tbl.all (entryOkIn G (ctxTable groups tbl) V)

@[csimp] theorem TableOk_eq_fast : @TableOk = @TableOkFast := by
  funext ι _ G tbl D V
  simp only [TableOk, TableOkFast, ← tableRows_all,
    show entryOkIn G (ctxTable ((ctxsOf tbl).map fun κ => (κ, ctxEntries tbl κ)) tbl) V =
      entryOk G tbl V from
      funext (entryOkIn_eq G tbl _ V (entryImg_ctxTable tbl))]

/-- A context relates the component a binder actually observes to its image.
The two-component image retains list bounds; the selected parameter side does
not constrain an unused component of a mixed assignment. -/
@[nospecialize] def RelKWith [DecidableEq ι] (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (κ : Ctx ι) (S : List ι) (ηL ηR : ParameterAssignment k ι) : Prop :=
  ∀ p ∈ S, match κ.lookup p with
    | some U => I.parameter p (ηL.1 p) =
        I.bound ηR (setSem fun i => qDenoteWithArgs G I (ηR, i)) U
    | none => I.parameter p (ηL.1 p) = I.parameter p (ηR.1 p)

/-- A mapped pack or value parameter obeys its table relation at both semantic
components. This does not reinterpret a list as a runtime value. -/
theorem mixed_parameter_image [DecidableEq ι] (G : NormalGraph ι) (κ : Ctx ι)
    (η θ : MixedAssignment ι) (p : ι) (kind : ParameterKind) (U : List ι)
    (hp : G.parameterKinds p = some kind) (hU : κ.lookup p = some U)
    (h : RelKWith G (mixedParameters G) κ [p] η θ) :
    mixedMeaning G η [p] = mixedMeaning G θ U := by
  rw [mixedMeaning_parameter G η p kind hp]
  have he := h p (by simp)
  rw [hU] at he
  change selectParameter (G.parameterKinds p) (η.1 p) = mixedMeaning G θ U at he
  rw [hp] at he
  exact he

theorem entryImg_mem [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι} {l : ι} {T : List ι}
    (h : entryImg tbl κ l = some T) : (l, κ, T) ∈ tbl := by
  unfold entryImg at h
  cases hf : tbl.find? (fun e => e.1 == l && e.2.1 == κ) with
  | none => simp [hf] at h
  | some e =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨a, b, c⟩ := e
    simp only at hp h
    rw [← hp.1, ← hp.2, ← h]
    exact hm

/-- A union maps to the union of its rows' images. -/
theorem tyImg_iff [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι} {P Q : ι → Prop} :
    ∀ {S S' : List ι}, tyImg tbl κ S = some S' →
      (∀ l ∈ S, ∀ T, entryImg tbl κ l = some T → (P l ↔ ∃ l' ∈ T, Q l')) →
      ((∃ l ∈ S, P l) ↔ ∃ l' ∈ S', Q l')
  | [], S', h, _ => by
    have : S' = [] := by simpa [tyImg] using h.symm
    subst this; simp
  | l :: S, S', h, hper => by
    unfold tyImg at h
    cases hl : entryImg tbl κ l with
    | none => simp [List.mapM_cons, hl] at h
    | some T =>
      cases hs : S.mapM (entryImg tbl κ) with
      | none => simp [List.mapM_cons, hl, hs] at h
      | some Ts =>
        have hS' : S' = T ++ Ts.flatten := by
          simp [List.mapM_cons, hl, hs] at h; exact h.symm
        subst hS'
        have ih := tyImg_iff (S := S) (S' := Ts.flatten) (by simp [tyImg, hs])
          (fun l' hl' T' hT' => hper l' (List.mem_cons_of_mem _ hl') T' hT')
        have hh := hper l List.mem_cons_self T hl
        simp only [List.mem_cons, List.mem_append, exists_eq_or_imp] at ih ⊢
        constructor
        · rintro (h1 | h2)
          · obtain ⟨l', hl', q⟩ := hh.mp h1; exact ⟨l', .inl hl', q⟩
          · obtain ⟨l', hl', q⟩ := ih.mp h2; exact ⟨l', .inr hl', q⟩
        · rintro ⟨l', hl' | hl', q⟩
          · exact .inl (hh.mpr ⟨l', hl', q⟩)
          · exact .inr (ih.mpr ⟨l', hl', q⟩)

theorem mem_of_lookup [DecidableEq ι] {κ : List (ι × β)} {p : ι} {U : β}
    (h : κ.lookup p = some U) : (p, U) ∈ κ := by
  induction κ with
  | nil => simp at h
  | cons e κ ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.lookup_cons] at h
    by_cases ha : p = a
    · subst ha; simp at h; subst h; exact List.mem_cons_self
    · rw [beq_false_of_ne ha] at h; exact List.mem_cons_of_mem _ (ih h)

theorem lookup_append_none [DecidableEq ι] {xs ys : List (ι × β)} {p : ι}
    (h : xs.lookup p = none) : (xs ++ ys).lookup p = ys.lookup p := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.lookup_cons] at h
    by_cases ha : p = a
    · subst ha; simp at h
    · rw [beq_false_of_ne ha] at h
      simp only [List.cons_append, List.lookup_cons]
      rw [beq_false_of_ne ha]; exact ih h

theorem keep_cons [DecidableEq ι] (κ : Ctx ι) (src : List ι) (q : ι) (ps : List ι) :
    keep κ src (q :: ps) = if q ∈ src then keep κ src ps else
      match κ.lookup q with
      | none => keep κ src ps
      | some U => (q, U) :: keep κ src ps := by
  by_cases hq : q ∈ src
  · simp [keep, hq]
  · cases hk : κ.lookup q <;> simp [keep, hq, hk]

theorem lookup_keep [DecidableEq ι] (κ : Ctx ι) {src : List ι} {p : ι} (hp : p ∉ src) :
    ∀ ps : List ι, (keep κ src ps).lookup p = if p ∈ ps then κ.lookup p else none
  | [] => by simp [keep]
  | q :: ps => by
    rw [keep_cons]
    by_cases hq : q ∈ src
    · have hpq : p ≠ q := fun e => hp (e ▸ hq)
      rw [if_pos hq, lookup_keep κ hp ps]
      simp [hpq]
    · rw [if_neg hq]
      by_cases hpq : p = q
      · subst hpq
        cases hk : κ.lookup p with
        | none => simp only; rw [lookup_keep κ hp ps]; simp [hk]
        | some U => simp
      · cases hk : κ.lookup q with
        | none => simp only; rw [lookup_keep κ hp ps]; simp [hpq]
        | some U =>
          simp only [List.lookup_cons, beq_false_of_ne hpq]
          rw [lookup_keep κ hp ps]; simp [hpq]

/-- Outside the binders, entering changes nothing a free row of the scheme
reads. -/
theorem enter_nmem [DecidableEq ι] (V : FreeMap ι) (i : ι) (κ : Ctx ι) {src tgt : List ι} {p : ι}
    (hp : p ∉ src) (hi : p ∈ fv V i) :
    (enter V i κ src tgt).lookup p = κ.lookup p := by
  unfold enter
  rw [lookup_append_none (lookup_zip_none hp), lookup_keep κ hp, if_pos hi]

/-- A binder entered stands for the binder at its position, and both sides are
given the same family there. -/
theorem enter_binder [DecidableEq ι] (ηL ηR : ParameterAssignment k ι) :
    ∀ {src tgt : List ι} {As : List (ParameterFamily k)} {p : ι} {U : List ι},
      tgt.Nodup → src.length = As.length → tgt.length = As.length →
      (src.zip (tgt.map ([·]))).lookup p = some U →
      ∃ q, U = [q] ∧ (assign ηL src As).1 p = (assign ηR tgt As).1 q
  | [], _, _, _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | b :: src, c :: tgt, [], _, _, _, h1, _, _ => by simp at h1
  | b :: src, c :: tgt, A :: As, p, U, hnd, h1, h2, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons] at h
    by_cases hb : p = b
    · subst hb
      simp only [beq_self_eq_true, Option.some.injEq] at h
      refine ⟨c, h.symm, ?_⟩
      rw [assign_cons_head, assign_cons_head]
    · rw [beq_false_of_ne hb] at h
      obtain ⟨q, hq, he⟩ := enter_binder ηL ηR (List.nodup_cons.mp hnd).2
        (by simpa using h1) (by simpa using h2) h
      refine ⟨q, hq, ?_⟩
      have hqt : q ∈ tgt := by
        have hm := (List.of_mem_zip (mem_of_lookup h)).2
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
        rw [hq] at hxe
        cases hxe; exact hx
      have hqc : q ≠ c := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hqt)
      have e1 := assign_cons_ne ηL src A As hb
      have e2 := assign_cons_ne ηR tgt A As hqc
      rw [e1, e2, he]

theorem mapM_some {f : α → Option α} :
    ∀ {xs ys : List α}, xs.mapM f = some ys → ys = xs.map (fun x => (f x).getD x) ∧
      ∀ x ∈ xs, (f x).isSome
  | [], ys, h => by simp at h; subst h; simp
  | x :: xs, ys, h => by
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some zs =>
        have hys : ys = y :: zs := by simp [List.mapM_cons, hx, hxs] at h; exact h.symm
        subst hys
        obtain ⟨h1, h2⟩ := mapM_some hxs
        refine ⟨by simp [hx, h1], ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · simp [hx]
        · exact h2 z hz

theorem lookup_zip_isSome [DecidableEq ι] {src : List ι} {ys : List β} {p : ι}
    (h : p ∈ src) (hl : src.length = ys.length) : ∃ U, (src.zip ys).lookup p = some U := by
  induction src generalizing ys with
  | nil => cases h
  | cons b src ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.zip_cons_cons, List.lookup_cons]
      by_cases hb : p = b
      · subst hb; simp
      · rw [beq_false_of_ne hb]
        exact ih ((List.mem_cons.mp h).resolve_left hb) (by simpa using hl)

theorem lookup_append_some [DecidableEq ι] {xs ys : List (ι × β)} {p : ι} {U : β}
    (h : xs.lookup p = some U) : (xs ++ ys).lookup p = some U := by
  induction xs with
  | nil => simp at h
  | cons e xs ih =>
    obtain ⟨a, b⟩ := e
    by_cases ha : p = a
    · subst ha; simp only [List.cons_append, List.lookup_cons, beq_self_eq_true] at h ⊢; exact h
    · simp only [List.lookup_cons, beq_false_of_ne ha] at h
      simp only [List.cons_append, List.lookup_cons, beq_false_of_ne ha]; exact ih h

/-- Renaming a bound parameter assigns the same family to both binders, but
the correspondence compares only their common kind. Arbitrary unused
components remain unrestricted, including under nested universal schemes. -/
theorem mixed_enter_binder [DecidableEq ι] (G : NormalGraph ι) (V : FreeMap ι) (i : ι) (κ : Ctx ι)
    (η θ : MixedAssignment ι) {src tgt : List ι} {As : List MixedFamily} {p : ι}
    (hp : p ∈ src) (hnd : tgt.Nodup) (hs : src.length = As.length) (ht : tgt.length = As.length)
    (hk : ∀ p q, (src.zip (tgt.map ([·]))).lookup p = some [q] →
      ∃ kind, G.parameterKinds p = some kind ∧ G.parameterKinds q = some kind) :
    ∃ q ∈ tgt, (enter V i κ src tgt).lookup p = some [q] ∧
      (mixedParameters G).parameter p ((assign η src As).1 p) =
        mixedMeaning G (assign θ tgt As) [q] := by
  obtain ⟨U, hU⟩ := lookup_zip_isSome (ys := tgt.map ([·])) hp (by simp [hs, ht])
  obtain ⟨q, rfl, he⟩ := enter_binder η θ hnd hs ht hU
  obtain ⟨kind, hpk, hqk⟩ := hk p q hU
  have hq : q ∈ tgt := by
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp (List.of_mem_zip (mem_of_lookup hU)).2
    cases hxe; exact hx
  refine ⟨q, hq, ?_, ?_⟩
  · unfold enter
    exact lookup_append_some hU
  · rw [mixedMeaning_parameter G _ q kind hqk]
    change selectParameter (G.parameterKinds p) _ = _
    rw [hpk, he]

theorem sameLabels_exists [DecidableEq ι] {a b : List ι} (h : sameLabels a b = true)
    (P : ι → Prop) : (∃ i ∈ a, P i) ↔ (∃ i ∈ b, P i) := by
  simp only [sameLabels, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  constructor
  · rintro ⟨i, hi, hp⟩; exact ⟨i, h.1 i hi, hp⟩
  · rintro ⟨i, hi, hp⟩; exact ⟨i, h.2 i hi, hp⟩

theorem sameLabels_values [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {a b : List ι} (h : sameLabels a b = true) : mixedValues G η a = mixedValues G η b := by
  funext n W v
  exact propext (sameLabels_exists h _)

theorem sameLabels_arguments [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {X : List ι → Fam} {a b : List ι} (h : sameLabels a b = true) :
    graphArguments G η X a = graphArguments G η X b := by
  funext n W vs
  exact propext (sameLabels_exists h _)

theorem sameLabelLists_values [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι} :
    ∀ {as bs : List (List ι)}, sameLabelLists as bs = true →
      as.map (mixedValues G η) = bs.map (mixedValues G η)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [sameLabelLists] at h
  | _ :: _, [], h => by simp [sameLabelLists] at h
  | a :: as, b :: bs, h => by
    simp only [sameLabelLists, List.length_cons, List.zip_cons_cons, List.all_cons,
      Bool.and_eq_true, beq_iff_eq, Nat.add_right_cancel_iff] at h
    have ht : sameLabelLists as bs = true := by
      simp only [sameLabelLists, Bool.and_eq_true, beq_iff_eq]; exact ⟨h.1, h.2.2⟩
    simp only [List.map_cons, sameLabels_values h.2.1, sameLabelLists_values ht]

theorem sigMatch_some [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι}
    {p q : Arrow (List ι)} (h : sigMatch tbl κ p q = true) :
    ∃ q', sigImg tbl κ p = some q' ∧ sameLabels q'.receiver q.receiver = true ∧
      sameLabelLists q'.arguments q.arguments = true ∧ sameLabels q'.result q.result = true ∧ q'.effect = q.effect := by
  unfold sigMatch at h
  split at h
  · rename_i q' hq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨q', hq, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · cases h

theorem restMatch_some [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι}
    {p q : RestArrow (List ι)} (h : restMatch tbl κ p q = true) :
    ∃ q', restImg tbl κ p = some q' ∧ sameLabels q'.receiver q.receiver = true ∧
      sameLabelLists q'.arguments.1 q.arguments.1 = true ∧ sameLabels q'.arguments.2 q.arguments.2 = true ∧
      sameLabels q'.result q.result = true ∧ q'.effect = q.effect := by
  unfold restMatch at h
  split at h
  · rename_i q' hq
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨q', hq, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · cases h

theorem sigBodyMatch_some [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι}
    {p q : Arrow (List ι)} (h : sigBodyMatch tbl κ p q = true) :
    ∃ ps r, p.arguments.mapM (tyImg tbl κ) = some ps ∧ tyImg tbl κ p.result = some r ∧
      sameLabelLists ps q.arguments = true ∧ sameLabels r q.result = true ∧ p.effect = q.effect := by
  unfold sigBodyMatch at h
  split at h
  · rename_i ps r h1 h2
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨ps, r, h1, h2, h.1.1, h.1.2, h.2⟩
  · cases h

theorem restBodyMatch_some [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι}
    {p q : RestArrow (List ι)} (h : restBodyMatch tbl κ p q = true) :
    ∃ ps e r, p.arguments.1.mapM (tyImg tbl κ) = some ps ∧ tyImg tbl κ p.arguments.2 = some e ∧
      tyImg tbl κ p.result = some r ∧ sameLabelLists ps q.arguments.1 = true ∧
      sameLabels e q.arguments.2 = true ∧ sameLabels r q.result = true ∧ p.effect = q.effect := by
  unfold restBodyMatch at h
  split at h
  · rename_i ps e r h1 h2 h3
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨ps, e, r, h1, h2, h3, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · cases h

/-- A type whose one clause is `top` holds every closed value. -/
theorem top_row_mixed {G : NormalGraph ι} {η : MixedAssignment ι} {S : List ι}
    (h : expand G S = [.top]) {n W v} (hv : isVal v = true ∧ Scoped 0 v) :
    mixedValues G η S n W v :=
  mixed_of_expand h ⟨hv, builtinInvariant_of_withoutInvariant rfl n W v⟩

/-- A type holding the built-ins' `unknown`: one of its labels is a clause row
with a `source` clause. -/
@[nospecialize] def unknownTy (G : NormalGraph ι) (T : List ι) : Bool :=
  T.any fun t => (G t).any fun c => match c with | .source => true | _ => false

/-- A value of the built-ins' `unknown` is a member of a type holding it. -/
theorem unknownTy_sound {G : NormalGraph ι} {η : MixedAssignment ι} {T : List ι}
    (h : unknownTy G T = true) {n W v} (hv : excOf G n W v) : mixedValues G η T n W v := by
  obtain ⟨t, ht, hp⟩ := List.any_eq_true.mp h
  obtain ⟨c, hc, hs⟩ := List.any_eq_true.mp hp
  cases c <;> simp only [Bool.false_eq_true] at hs
  exact mixed_expand_mpr ⟨.source, List.mem_flatMap.mpr ⟨t, ht, hc⟩, hv⟩

/-- A type of the built-ins' `unknown` alone: each label a clause row of `source`
clauses only. -/
@[nospecialize] def exactUnknown (G : NormalGraph ι) (U : List ι) : Bool :=
  U.all fun u => G.plain u && (G u).all fun c => match c with | .source => true | _ => false

/-- A member of a type of the built-ins' `unknown` alone is of the exception family. -/
theorem exactUnknown_sound {G : NormalGraph ι} {η : MixedAssignment ι} {U : List ι}
    (h : exactUnknown G U = true) {n W v} (hv : mixedValues G η U n W v) : excOf G n W v := by
  obtain ⟨u, hu, hv⟩ := hv
  have hp := List.all_eq_true.mp h u hu
  simp only [Bool.and_eq_true, List.all_eq_true] at hp
  obtain ⟨c, hc, hrow⟩ := (mixed_unfold_plain η hp.1 n W v).mp hv
  have hs := hp.2 c hc
  cases c <;> simp only [Bool.false_eq_true] at hs
  exact hrow

theorem sigImg_some [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι}
    {p q : Arrow (List ι)} (h : sigImg tbl κ p = some q) :
    tyImg tbl κ p.receiver = some q.receiver ∧ p.arguments.mapM (tyImg tbl κ) = some q.arguments ∧
      tyImg tbl κ p.result = some q.result ∧ p.effect = q.effect := by
  unfold sigImg at h
  cases h1 : tyImg tbl κ p.receiver with
  | none => simp [h1] at h
  | some a =>
    cases h2 : p.arguments.mapM (tyImg tbl κ) with
    | none => simp [h1, h2] at h
    | some b =>
      cases h3 : tyImg tbl κ p.result with
      | none => simp [h1, h2, h3] at h
      | some c =>
        simp [h1, h2, h3] at h
        subst h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem restImg_some [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι}
    {p q : RestArrow (List ι)} (h : restImg tbl κ p = some q) :
    tyImg tbl κ p.receiver = some q.receiver ∧ p.arguments.1.mapM (tyImg tbl κ) = some q.arguments.1 ∧
      tyImg tbl κ p.arguments.2 = some q.arguments.2 ∧ tyImg tbl κ p.result = some q.result ∧ p.effect = q.effect := by
  unfold restImg at h
  cases h1 : tyImg tbl κ p.receiver with
  | none => simp [h1] at h
  | some a =>
    cases h2 : p.arguments.1.mapM (tyImg tbl κ) with
    | none => simp [h1, h2] at h
    | some b =>
      cases h3 : tyImg tbl κ p.arguments.2 with
      | none => simp [h1, h2, h3] at h
      | some c =>
        cases h4 : tyImg tbl κ p.result with
        | none => simp [h1, h2, h3, h4] at h
        | some d =>
          simp [h1, h2, h3, h4] at h
          subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A context fixing a row relates the two assignments on its free rows as
equal parameters. -/
theorem fixedBy_rel [DecidableEq ι] {G : NormalGraph ι} {κ : Ctx ι} {V : FreeMap ι} {i : ι}
    {ηL ηR : MixedAssignment ι} (hfix : fixedBy G κ V i = true)
    (hrel : RelKWith G (mixedParameters G) κ (fv V i) ηL ηR) :
    ∀ p ∈ fv V i, (mixedParameters G).parameter p (ηL.1 p) =
      (mixedParameters G).parameter p (ηR.1 p) := by
  intro p hp
  have hr := hrel p hp
  have hf := List.all_eq_true.mp hfix p hp
  cases hk : κ.lookup p with
  | none => rw [hk] at hr; exact hr
  | some U =>
    rw [hk] at hr hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨rfl, hpar⟩ := hf
    obtain ⟨kind, hkind⟩ : ∃ kind, G.parameterKinds p = some kind := by
      simpa [NormalGraph.params, Option.isSome_iff_exists] using hpar
    change selectParameter (G.parameterKinds p) (ηL.1 p) = mixedMeaning G ηR [p] at hr
    rw [mixedMeaning_parameter G ηR p kind hkind] at hr
    change selectParameter (G.parameterKinds p) (ηL.1 p) = selectParameter (G.parameterKinds p) (ηR.1 p)
    rw [hkind]; rw [hkind] at hr; exact hr

/-- A meet row, as a parameter row, has no argument lists. -/
theorem meet_noArguments {G : NormalGraph ι} {σ : MixedAssignment ι} {l : ι}
    {pc : ι × List (Clause (List ι))} (hl : G.params l = false) (hm : G.meets l = some pc)
    {n : Nat} {W : WorldT n} {vs : List Val} : ¬ mixedMeaning G σ [l] n W (.inr vs) := by
  have hk : G.parameterKinds l = none := by simpa [NormalGraph.params] using hl
  simp [mixedMeaning, mixedParameters, graphArguments, hk, NormalGraph.clauses,
    NormalGraph.plain, hm, NormalGraph.listParam]

/-- A meet row's image has no argument lists either. -/
theorem meetOk_noArguments [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι}
    {κ : Ctx ι} {ps : List ι} {cs : List (Clause (List ι))} {j : ι}
    (hok : meetOk G tbl κ ps cs j = true)
    (σ : MixedAssignment ι) {n : Nat} (W : WorldT n) (vs : List Val) :
    ¬ mixedMeaning G σ [j] n W (.inr vs) := by
  unfold meetOk at hok
  cases hmj : G.meets j with
  | some qd =>
    simp only [hmj, Bool.and_eq_true, Bool.not_eq_true'] at hok
    exact meet_noArguments hok.2.1.1.1.1.1 hmj
  | none =>
    simp only [hmj, Bool.and_eq_true] at hok
    exact mixedMeaning_noArguments G σ [j] hok.2.1.2 n W vs

/-- A meet of several clause lists holds what each of them holds. -/
theorem meetMany_row (G : NormalGraph ι) (Z X : List ι → Fam) (P : List ι → ArgFam)
    (Ls : List (List (Clause (List ι)))) (hne : Ls ≠ []) (n W v) :
    setSem (rowSem G Z X P) (meetMany Ls) n W v ↔
      ∀ L ∈ Ls, setSem (rowSem G Z X P) L n W v := by
  cases Ls with
  | nil => contradiction
  | cons A rest =>
    induction rest generalizing A with
    | nil => simp [meetMany]
    | cons B rest ih =>
      have h := ih (meetLists A B) (List.cons_ne_nil _ _)
      simp only [meetMany, List.foldl_cons] at h ⊢
      rw [h]
      simp only [List.mem_cons, forall_eq_or_imp, meetLists_row]
      constructor
      · rintro ⟨⟨ha, hb⟩, hr⟩; exact ⟨ha, hb, hr⟩
      · rintro ⟨ha, hb, hr⟩; exact ⟨⟨ha, hb⟩, hr⟩

/-- A meet row's parameter, read at the image its context gives it: itself
where the context gives it nothing. -/
theorem meet_param_image [DecidableEq ι] {G : NormalGraph ι} {κ : Ctx ι} {p : ι}
    {ηL ηR : MixedAssignment ι} {n : Nat} {W : WorldT n} {v : Val}
    (hpk : G.parameterKinds p = some .value)
    (hr : RelKWith G (mixedParameters G) κ [p] ηL ηR) :
    ηL.1 p n W (.inl v) ↔ mixedValues G ηR ((κ.lookup p).getD [p]) n W v := by
  have hsel : ∀ A : WorldFamily ParameterSpace.mixed.Carrier,
      (mixedParameters G).parameter p A n W (.inl v) ↔ A n W (.inl v) := by
    intro A; simp [mixedParameters, selectParameter, hpk]
  have h := hr p (List.mem_singleton_self p)
  cases hU : κ.lookup p with
  | none =>
    rw [hU] at h
    simp only [Option.getD_none]
    rw [← hsel (ηL.1 p), h, hsel]
    change _ ↔ mixedMeaning G ηR [p] n W (.inl v)
    rw [mixedMeaning_parameter G ηR p .value hpk]
    simp [selectParameter]
  | some U =>
    rw [hU] at h
    simp only [Option.getD_some]
    rw [← hsel (ηL.1 p), h]; rfl

/-- **A meet row means its image.** Under a context relating the meet row's
parameters, and with its clauses' images, `ps ⊓ cs` means the meet row of the
parameters' images, or, when the context gives each of `ps` a type of clause
rows, the clause row holding the meet of those types' clauses with the
clauses' images: the value is in each and in the clauses, which
`meetLists_row` makes one clause list. -/
theorem meet_row_value [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι} {κ : Ctx ι}
    {i j p : ι} {cs : List (Clause (List ι))} {ηL ηR : MixedAssignment ι} {n : Nat}
    {W : WorldT n} {v : Val}
    (hpar : G.params i = false) (hsch : G.schemes i = none) (hm : G.meets i = some (p, cs))
    (hok : meetOk G tbl κ (p :: G.meetParams i) cs j = true)
    (hrel : RelKWith G (mixedParameters G) κ (p :: G.meetParams i) ηL ηR)
    (hcl : ∀ c ∈ cs, mixedSem G ηL c n W v ↔ mixedSem G ηR (clauseImg tbl κ c) n W v) :
    qDenoteWithArgs G (mixedParameters G) (ηL, i) n W v ↔ mixedValues G ηR [j] n W v := by
  unfold meetOk at hok
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨hpk, _⟩, hok⟩ := hok
  -- The meet row: each parameter's image, within the clauses' images.
  have hval : ∀ q ∈ p :: G.meetParams i,
      (partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) ηL q n W v ↔
      mixedValues G ηR ((κ.lookup q).getD [q]) n W v) := by
    intro q hq
    rw [partSemWithArgs_param (by simp [NormalGraph.params, hpk q hq])]
    simp [mixedParameters, hpk q hq, selectParameter]
    exact meet_param_image (hpk q hq) (fun r hr => by
      cases List.mem_singleton.mp hr; exact hrel q hq)
  have hL : qDenoteWithArgs G (mixedParameters G) (ηL, i) n W v ↔
      (∀ q ∈ p :: G.meetParams i, mixedValues G ηR ((κ.lookup q).getD [q]) n W v) ∧
        setSem (mixedSem G ηR) (cs.map (clauseImg tbl κ)) n W v := by
    rw [qDenoteWithArgs_unfold]
    simp only [qLayerWithArgs, hpar, hsch, hm, Bool.false_eq_true, ite_false]
    refine and_congr ?_ ⟨?_, ?_⟩
    · rw [List.forall_mem_cons]
      exact and_congr (hval p List.mem_cons_self)
        (forall₂_congr fun q hq => hval q (List.mem_cons_of_mem _ hq))
    · rintro ⟨c, hc, h⟩
      exact ⟨_, List.mem_map_of_mem hc, (hcl c hc).mp h⟩
    · rintro ⟨_, hc', h⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
      exact ⟨c, hc, (hcl c hc).mpr h⟩
  have hsingle : mixedValues G ηR [j] n W v ↔ qDenoteWithArgs G (mixedParameters G) (ηR, j) n W v :=
    ⟨fun ⟨_, hm, h⟩ => by cases List.mem_singleton.mp hm; exact h,
     fun h => ⟨j, List.mem_singleton_self j, h⟩⟩
  have members : ∀ {Cs Ds : List (Clause (List ι))}, sameClauses Cs Ds = true →
      (setSem (mixedSem G ηR) Cs n W v ↔ setSem (mixedSem G ηR) Ds n W v) := fun h =>
    sameClauses_iff h (fun d => mixedSem G ηR d n W v) (fun c f hf hn => by
      simp only [rowSem, semWithArgs_members (fun S T h => sameLabels_values h)
        (fun S T h => sameLabels_arguments h) hf hn, builtinInvariant_map])
  rw [hL, hsingle]
  cases hmj : G.meets j with
  | some qd =>
    -- A meet row of the parameters' images.
    obtain ⟨q, ds⟩ := qd
    simp only [hmj, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_true,
      beq_iff_eq, Option.isNone_iff_eq_none] at hok
    obtain ⟨⟨⟨⟨⟨hjp, hjs⟩, hrk⟩, hfwd⟩, hbwd⟩, hds⟩ := hok
    rw [qDenoteWithArgs_unfold]
    simp only [qLayerWithArgs, hjp, hjs, hmj, Bool.false_eq_true, ite_false]
    refine and_congr ?_ (members hds).symm
    have hrv : ∀ r ∈ q :: G.meetParams j,
        (mixedValues G ηR [r] n W v ↔ (mixedParameters G).value r (ηR.1 r) n W v) := by
      intro r hr
      simp [mixedParameters, hrk r hr, selectParameter]
      change mixedMeaning G ηR [r] n W (.inl v) ↔ _
      rw [mixedMeaning_parameter G ηR r .value (hrk r hr)]
      simp [selectParameter]
    have hrv : ∀ r ∈ q :: G.meetParams j,
        (mixedValues G ηR [r] n W v ↔
          partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) ηR r n W v) := by
      intro r hr
      rw [partSemWithArgs_param (by simp [NormalGraph.params, hrk r hr])]
      exact hrv r hr
    have hR : (partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) ηR q n W v ∧
        ∀ r ∈ G.meetParams j,
          partSemWithArgs G (mixedParameters G) (qDenoteWithArgs G (mixedParameters G)) ηR r n W v) ↔
        ∀ r ∈ q :: G.meetParams j, mixedValues G ηR [r] n W v := by
      rw [List.forall_mem_cons]
      exact and_congr (hrv q List.mem_cons_self).symm
        (forall₂_congr fun r hr => (hrv r (List.mem_cons_of_mem _ hr)).symm)
    rw [hR]
    constructor
    · intro h r hr
      obtain ⟨p', hp', he⟩ := hbwd r hr
      rw [← he]; exact h p' hp'
    · intro h p' hp'
      obtain ⟨r, hr, he⟩ := hfwd p' hp'
      rw [he]; exact h r hr
  | none =>
    -- A clause row holding the meet of the parameters' images with the clauses.
    simp only [hmj, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at hok
    obtain ⟨⟨⟨⟨hsome, hjplain⟩, hUplain⟩, _⟩, horder⟩ := hok
    have hparts : ∀ q ∈ p :: G.meetParams i,
        (mixedValues G ηR ((κ.lookup q).getD [q]) n W v ↔
          setSem (mixedSem G ηR) (clausesOf G ((κ.lookup q).getD [])) n W v) := by
      intro q hq
      obtain ⟨U, hU⟩ := Option.isSome_iff_exists.mp (hsome q hq)
      have hpl : G.plainTy U = true := by
        have := hUplain _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
        simpa [hU] using this
      simp only [hU, Option.getD_some]
      rw [mixed_expand ηR hpl n W v, expand_of_plain hpl]
    have hops : (∀ L ∈ meetOperands G tbl κ (p :: G.meetParams i) cs,
        setSem (mixedSem G ηR) L n W v) ↔
        ((∀ q ∈ p :: G.meetParams i, mixedValues G ηR ((κ.lookup q).getD [q]) n W v) ∧
          setSem (mixedSem G ηR) (cs.map (clauseImg tbl κ)) n W v) := by
      simp only [meetOperands, List.mem_append, List.mem_map, List.mem_singleton]
      constructor
      · intro h
        exact ⟨fun q hq => (hparts q hq).mpr (h _ (.inl ⟨q, hq, rfl⟩)), h _ (.inr rfl)⟩
      · rintro ⟨h1, h2⟩ L (⟨q, hq, rfl⟩ | rfl)
        · exact (hparts q hq).mp (h1 q hq)
        · exact h2
    have hne : meetOperands G tbl κ (p :: G.meetParams i) cs ≠ [] := by simp [meetOperands]
    rw [mixed_unfold_plain ηR hjplain n W v]
    rcases horder with h | h
    · rw [members h, meetMany_row G _ _ _ _ hne]
      exact hops.symm
    · rw [members h, meetMany_row G _ _ _ _ (by simpa using hne)]
      simp only [List.mem_reverse]
      exact hops.symm

/-- The argument half of table transport uses the value half at exactly the
same level. It covers every checked entry, including parameters, unchanged
rows and schemes; it does not assume the table contains only tuple rows. -/
theorem table_row_arguments [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι}
    {D : List ι} {V : FreeMap ι} (hok : TableOk G tbl D V = true) (n : Nat)
    (hv : ∀ η θ : MixedAssignment ι, ∀ e ∈ tbl,
      RelKWith G (mixedParameters G) e.2.1 (fv V e.1) η θ →
      ∀ (W : WorldT n) v, qDenoteWithArgs G (mixedParameters G) (η, e.1) n W v ↔
        mixedMeaning G θ e.2.2 n W (.inl v)) :
    ∀ η θ : MixedAssignment ι, ∀ e ∈ tbl,
      RelKWith G (mixedParameters G) e.2.1 (fv V e.1) η θ →
      ∀ (W : WorldT n) vs, mixedMeaning G η [e.1] n W (.inr vs) ↔
        mixedMeaning G θ e.2.2 n W (.inr vs) := by
  simp only [TableOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hF, hrows⟩, hents⟩ := hok
  rintro η θ ⟨i, κ, T⟩ he hrel W vs
  have hiD : i ∈ D := by
    have := hrows i (List.mem_flatMap.mpr ⟨(i, κ, T), he, List.mem_cons_self⟩)
    simpa using this
  have ⟨hself, hreads, _⟩ := freeOk_row hF hiD
  have hrow := hents _ he
  simp only [entryOk] at hrow
  cases hp : G.params i
  · simp only [hp, Bool.false_eq_true, if_false] at hrow
    by_cases hrig : (T == [i] && fixedBy G κ V i) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at hrig
      obtain ⟨rfl, hfix⟩ := hrig
      have h := graphArguments_free hF _
        (agree_freeWith hF (mixedParameters G) (mixed_respectsFree hF)) η θ [i]
        (fun l hl => by cases List.mem_singleton.mp hl; exact hiD)
        (fun l hl p hp' => by
          cases List.mem_singleton.mp hl
          exact fixedBy_rel hfix hrel p hp')
      exact iff_of_eq (congrFun (congrFun (congrFun h n) W) vs)
    · have hrigF : (T == [i] && fixedBy G κ V i) = false := by
        simpa using hrig
      simp only [hrigF, Bool.false_eq_true, if_false] at hrow
      cases hs : G.schemes i with
      | some s =>
        cases T with
        | nil => simp [hs] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hs] at hrow
          | nil =>
            cases ht : G.schemes j with
            | none => simp [hs, ht] at hrow
            | some t =>
              have hj : G.params j = false := by
                simp only [hs, ht, Bool.and_eq_true, Bool.not_eq_true'] at hrow
                exact hrow.1.1.1.1.1.1.1.1.1
              have noArgs : ∀ (σ : MixedAssignment ι) l,
                  G.params l = false → G.schemes l ≠ none →
                  ¬ mixedMeaning G σ [l] n W (.inr vs) := by
                intro σ l hl hsch
                have hk : G.parameterKinds l = none := by simpa [NormalGraph.params] using hl
                simp [mixedMeaning, mixedParameters, graphArguments, hk,
                  NormalGraph.clauses, NormalGraph.plain, hsch, NormalGraph.listParam]
              -- A scheme contributes values only, regardless of its binders.
              exact iff_of_false (noArgs η i hp (by simp [hs]))
                (noArgs θ j hj (by simp [ht]))
      | none =>
        cases T with
        | nil => simp [hs] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hs] at hrow
          | nil =>
            cases hm : G.meets i with
            | some pc =>
              simp only [hs, hm] at hrow
              exact iff_of_false (meet_noArguments hp hm) (meetOk_noArguments hrow θ W vs)
            | none =>
            simp only [hs, hm, Bool.and_eq_true, List.all_eq_true] at hrow
            obtain ⟨⟨⟨hip, hjp⟩, hops⟩, hG⟩ := hrow
            apply graphArguments_image G tbl κ η θ _ _ i j hip hjp hG
              (fun S T h => sameLabels_values h) n W vs
            · intro c hc S hS
              obtain ⟨U, hU⟩ := Option.isSome_iff_exists.mp (hops c hc S hS)
              refine ⟨U, hU, fun v => tyImg_iff hU fun l hl T hT => ?_⟩
              apply hv η θ (l, κ, T) (entryImg_mem hT) _ W v
              intro p hp'
              have hlr : l ∈ reads G i := by
                simp only [reads, hs]
                exact List.mem_flatMap.mpr ⟨c, List.mem_append_left _ hc, List.mem_flatten.mpr ⟨S, hS, hl⟩⟩
              rcases (hreads l hlr).2 p hp' with h | ⟨s', hs', _⟩
              · exact hrel p h
              · rw [hs] at hs'; cases hs'
            · intro v; simp [setSem, mixedValues]
  · simp only [hp, if_true, Bool.and_eq_true, beq_iff_eq] at hrow
    obtain ⟨rfl, _⟩ := hrow
    have hr := hrel i (hself hp)
    obtain ⟨kind, hk⟩ : ∃ kind, G.parameterKinds i = some kind := by
      simpa [NormalGraph.params, Option.isSome_iff_exists] using hp
    rw [mixedMeaning_parameter G η i kind hk]
    cases hκ : κ.lookup i with
    | none =>
      rw [hκ] at hr
      simp only [Option.getD_none]
      rw [mixedMeaning_parameter G θ i kind hk]
      change selectParameter (G.parameterKinds i) _ = selectParameter (G.parameterKinds i) _ at hr
      rw [hk] at hr
      rw [hr]
    | some U =>
      rw [hκ] at hr
      simp only [Option.getD_some]
      change selectParameter (G.parameterKinds i) _ = mixedMeaning G θ U at hr
      rw [hk] at hr
      rw [hr]

/-- Closing one level of a mixed table proof needs only its value images:
the argument images follow at that same level. In the recursive proof the
value step may use both components at strictly smaller levels. -/
theorem table_row_mixed_of_values [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι}
    {D : List ι} {V : FreeMap ι} (hok : TableOk G tbl D V = true) (n : Nat)
    (hv : ∀ η θ : MixedAssignment ι, ∀ e ∈ tbl,
      RelKWith G (mixedParameters G) e.2.1 (fv V e.1) η θ →
      ∀ (W : WorldT n) v, qDenoteWithArgs G (mixedParameters G) (η, e.1) n W v ↔
        mixedMeaning G θ e.2.2 n W (.inl v)) :
    ∀ η θ : MixedAssignment ι, ∀ e ∈ tbl,
      RelKWith G (mixedParameters G) e.2.1 (fv V e.1) η θ →
      ∀ (W : WorldT n) x, mixedMeaning G η [e.1] n W x ↔
        mixedMeaning G θ e.2.2 n W x := by
  intro η θ e he hrel W x
  cases x with
  | inl v =>
    change (∃ i ∈ [e.1], qDenoteWithArgs G (mixedParameters G) (η, i) n W v) ↔ _
    simpa only [List.mem_singleton, exists_eq_left] using hv η θ e he hrel W v
  | inr vs => exact table_row_arguments hok n hv η θ e he hrel W vs

private theorem tyImg_mixed_iff [DecidableEq ι] {G : NormalGraph ι}
    {tbl : InstTable ι} {κ : Ctx ι} {S T : List ι} (h : tyImg tbl κ S = some T)
    {η : MixedAssignment ι} {n : Nat} {W : WorldT n} {x : Val ⊕ List Val}
    {P : ι → Prop}
    (hr : ∀ i ∈ S, ∀ U, entryImg tbl κ i = some U →
      (P i ↔ mixedMeaning G η U n W x)) :
    (∃ i ∈ S, P i) ↔ mixedMeaning G η T n W x := by
  rw [mixedMeaning_union]
  exact tyImg_iff h (fun i hi U hU => (hr i hi U hU).trans (mixedMeaning_union G η U n W x))

/-- **Instance tables.** Under its context, an entry's row means its image. -/
theorem table_row_mixed [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι} {D : List ι}
    {V : FreeMap ι} (hok : TableOk G tbl D V = true) :
    ∀ n, ∀ ηL ηR : MixedAssignment ι, ∀ e ∈ tbl, RelKWith G (mixedParameters G) e.2.1 (fv V e.1) ηL ηR →
      ∀ (W : WorldT n) x, mixedMeaning G ηL [e.1] n W x ↔ mixedMeaning G ηR e.2.2 n W x := by
  have checked := hok
  simp only [TableOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hF, hrowsD⟩, hents⟩ := hok
  have inD : ∀ e ∈ tbl, e.1 ∈ D ∧ (∀ l ∈ e.2.2, l ∈ D) ∧
      ∀ p U, e.2.1.lookup p = some U → ∀ l ∈ U, l ∈ D := by
    intro e he
    have h := fun l hl => by simpa using hrowsD l hl
    refine ⟨h _ (List.mem_flatMap.mpr ⟨e, he, List.mem_cons_self⟩),
      fun l hl => h _ (List.mem_flatMap.mpr ⟨e, he, List.mem_cons_of_mem _ (List.mem_append_left _ hl)⟩),
      fun p U hU l hl => h _ (List.mem_flatMap.mpr ⟨e, he, List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(p, U), mem_of_lookup hU, hl⟩))⟩)⟩
  have singleton : ∀ (η : MixedAssignment ι) (j : ι) m (U : WorldT m) u,
      mixedValues G η [j] m U u ↔ qDenoteWithArgs G (mixedParameters G) (η, j) m U u := fun η j m U u =>
    ⟨fun ⟨_, hm, h⟩ => by cases List.mem_singleton.mp hm; exact h,
     fun h => ⟨j, List.mem_singleton_self j, h⟩⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  apply table_row_mixed_of_values checked n
  rintro ηL ηR ⟨i, κ, T⟩ he hrel W v
  change qDenoteWithArgs G (mixedParameters G) (ηL,i) n W v ↔ mixedValues G ηR T n W v
  have hrow := hents _ he
  obtain ⟨hiD, _, hκD⟩ := inD _ he
  have ⟨hself, hreads, hbounds⟩ := freeOk_row hF hiD
  simp only at hrel hiD hκD
  -- A type whose rows have entries under a context, related on their free
  -- rows, means its image below the budget.
  have hty : ∀ (ηL' ηR' : MixedAssignment ι) (κ' : Ctx ι) (S S' : List ι),
      tyImg tbl κ' S = some S' →
      (∀ l ∈ S, RelKWith G (mixedParameters G) κ' (fv V l) ηL' ηR') →
      Agree (setSem (fun l => qDenoteWithArgs G (mixedParameters G) (ηL', l)) S) (mixedValues G ηR' S') n := by
    intro ηL' ηR' κ' S S' hS hrl m hm U u
    exact tyImg_iff hS fun l hl T hT => by
      have h := ih m hm ηL' ηR' (l, κ', T) (entryImg_mem hT) (hrl l hl) U (.inl u)
      simpa [mixedMeaning, mixedParameters, setSem] using h
  have hmix : ∀ (ηL' ηR' : MixedAssignment ι) (κ' : Ctx ι) (S S' : List ι),
      tyImg tbl κ' S = some S' →
      (∀ l ∈ S, RelKWith G (mixedParameters G) κ' (fv V l) ηL' ηR') →
      Agree (mixedMeaning G ηL' S) (mixedMeaning G ηR' S') n := by
    intro ηL' ηR' κ' S S' hS hrl m hm U x
    rw [mixedMeaning_union]
    exact tyImg_mixed_iff hS fun l hl T hT =>
      ih m hm ηL' ηR' (l, κ', T) (entryImg_mem hT) (hrl l hl) U x
  have hpack : ∀ (ηL' ηR' : MixedAssignment ι) (κ' : Ctx ι) (S S' : List ι),
      tyImg tbl κ' S = some S' →
      (∀ l ∈ S, RelKWith G (mixedParameters G) κ' (fv V l) ηL' ηR') →
      Agree (graphArguments G ηL' (mixedValues G ηL') S)
        (graphArguments G ηR' (mixedValues G ηR') S') n := by
    intro ηL' ηR' κ' S S' hS hrl m hm U vs
    exact hmix ηL' ηR' κ' S S' hS hrl m hm U (.inr vs)
  simp only [entryOk] at hrow
  cases hpar : G.params i
  · simp only [hpar, Bool.false_eq_true, if_false] at hrow
    by_cases hrig : (T == [i] && fixedBy G κ V i) = true
    · -- its own image, the context fixing its free rows
      simp only [Bool.and_eq_true, beq_iff_eq] at hrig
      obtain ⟨rfl, hfix⟩ := hrig
      rw [singleton]
      rw [agree_freeWith hF (mixedParameters G) (mixed_respectsFree hF) ηL ηR i hiD
        (fixedBy_rel hfix hrel)]
    · have hrigF : (T == [i] && fixedBy G κ V i) = false := by
        simpa using hrig
      simp only [hrigF, Bool.false_eq_true, if_false] at hrow
      cases hsch : G.schemes i with
      | some s =>
        cases hT : T with
        | nil => simp [hsch, hT] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hsch, hT] at hrow
          | nil =>
            simp only [hsch, hT] at hrow
            cases hs2 : G.schemes j with
            | none => simp [hs2] at hrow
            | some s2 =>
            simp only [hs2, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq,
              List.all_eq_true] at hrow
            obtain ⟨hrow, hord⟩ := hrow
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨hjp, hnd⟩, hlen⟩, hpars⟩, hkinds⟩, hcap⟩, hsigs⟩, hbnds⟩, hrests⟩ := hrow
            rw [singleton, qDenoteWithArgs_unfold, qDenoteWithArgs_unfold]
            simp only [qLayerWithArgs, hpar, hjp, hsch, hs2, Bool.false_eq_true, if_false]
            change boundedSem _ ηL s _ G.domain n W v ↔ boundedSem _ ηR s2 _ G.domain n W v
            refine and_congr (by rw [sameShape_construct hord]) ?_
            rw [hlen]
            refine forall_congr' fun qlevel => forall_congr' fun hlevel => forall_congr' fun As => forall_congr' fun hlA =>
              imp_congr (sameShape_allowed G.domain hord As) (imp_congr ?_ ?_)
            · -- Each bound maps to the target's: the same family on the binders,
              -- and the bound types related at the outer assignments.
              obtain ⟨hbmap, hbsome⟩ := mapM_some hbnds
              unfold Bounded
              rw [hbmap]
              simp only [List.forall_mem_map]
              refine forall_congr' fun b => forall_congr' fun hb => ?_
              obtain ⟨⟨q, B'⟩, hbi⟩ := Option.isSome_iff_exists.mp (hbsome b hb)
              simp only [hbi, Option.getD_some]
              unfold boundImg at hbi
              split at hbi
              · rename_i q' hU
                obtain ⟨B'', hB'', hqB⟩ := Option.map_eq_some_iff.mp hbi
                cases hqB
                obtain ⟨q'', hq'', he⟩ := enter_binder ηL ηR hnd hlA.symm (hlen.trans hlA.symm) hU
                cases hq''
                have hb1 : b.1 ∈ s.binders := (List.of_mem_zip (mem_of_lookup hU)).1
                have hq2 : q ∈ s2.binders := by
                  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp (List.of_mem_zip (mem_of_lookup hU)).2
                  cases hxe; exact hx
                refine imp_congr (iff_of_true hb1 hq2) (forall_congr' fun j => forall_congr' fun hj =>
                  forall_congr' fun U => forall_congr' fun u => imp_congr (by rw [he]) ?_)
                have hbr : ∀ l ∈ b.2, l ∈ reads G i ∧ l ∈ boundReads G i := by
                  intro l hl'
                  refine ⟨?_, ?_⟩
                  · simp only [reads, hsch]
                    exact List.mem_append_left _
                      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, hl'⟩))
                  · simp only [boundReads, hsch]
                    exact List.mem_flatMap.mpr ⟨b, hb, hl'⟩
                exact hmix ηL ηR κ b.2 _ hB''
                  (fun l hl p hp => hrel p (hbounds l (hbr l hl).2 p hp)) j (by omega) U u
              · simp at hbi
            have hty := fun a b c d e f g => Agree.mono (hty a b c d e f g) hlevel
            have hpack := fun a b c d e f g => Agree.mono (hpack a b c d e f g) hlevel
            let W := trunc qlevel hlevel W
            let n := qlevel
            -- Inside, the relation holds on each signature row's free rows.
            have hrel' : ∀ l ∈ reads G i, RelKWith G (mixedParameters G) (enter V i κ s.binders s2.binders) (fv V l)
                (assign ηL s.binders As) (assign ηR s2.binders As) := by
              intro l hl p hp
              by_cases hb : p ∈ s.binders
              · have hkindRel : ∀ p q, (s.binders.zip (s2.binders.map ([·]))).lookup p = some [q] →
                    ∃ kind, G.parameterKinds p = some kind ∧ G.parameterKinds q = some kind := by
                  intro p q hlookup
                  have hmem : (p,q) ∈ s.binders.zip s2.binders := by
                    have hmem := mem_of_lookup hlookup
                    rw [List.zip_map_right] at hmem
                    obtain ⟨⟨a,b⟩, hab, heq⟩ := List.mem_map.mp hmem
                    cases heq
                    exact hab
                  have heq := hkinds (p,q) hmem
                  have hqp := hpars q (List.of_mem_zip hmem).2
                  obtain ⟨kind, hkind⟩ : ∃ kind, G.parameterKinds q = some kind := by
                    simpa [NormalGraph.params, Option.isSome_iff_exists] using hqp
                  exact ⟨kind, heq.trans hkind, hkind⟩
                obtain ⟨q, hq, hk, he⟩ := mixed_enter_binder G V i κ ηL ηR hb hnd hlA.symm
                  (hlen.trans hlA.symm) hkindRel
                rw [hk]; exact he
              · have hpi : p ∈ fv V i := by
                  rcases (hreads l hl).2 p hp with h1 | ⟨s', hs', h2⟩
                  · exact h1
                  · rw [hsch] at hs'; cases hs'; exact absurd h2 hb
                rw [enter_nmem V i κ hb hpi, assign_nmem ηL s.binders As hb]
                have hr := hrel p hpi
                have hc := hcap p hpi
                cases hk : κ.lookup p with
                | none =>
                  rw [hk] at hr hc
                  have : p ∉ s2.binders := by simpa using hc
                  rw [assign_nmem ηR s2.binders As this]; exact hr
                | some U =>
                  rw [hk] at hr
                  simp only [hk, List.all_eq_true, Bool.not_eq_true'] at hc
                  rw [hr]
                  exact (mixed_respectsFree hF).bound _
                    (agree_freeWith hF (mixedParameters G) (mixed_respectsFree hF))
                    ηR (assign ηR s2.binders As) U (hκD p U hk)
                    (fun l hl q hq => by
                      rw [assign_nmem ηR s2.binders As (by simpa using (hc l hl) q hq)])
            simp only [instanceTWithArgs]
            rw [← sameShape_construct hord]
            obtain ⟨hmap, _⟩ := mapM_some hsigs
            obtain ⟨hmap', _⟩ := mapM_some hrests
            unfold instanceSigs instanceRestsWithArgs
            dsimp only [mixedParameters]
            rw [hmap, hmap']
            simp only [List.map_map]
            refine sigsT_congr s.construct s.signatures _ _ s.variadic _ _ (fun _ _ _ _ => Iff.rfl) (by
              intro p hps
              obtain ⟨_, hsome⟩ := mapM_some hsigs
              obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hsome p hps)
              simpa [Function.comp, hq, Arrow.map, Contract.map] using (sigImg_some hq).2.2.2) (fun p hps => ?_) (by
              intro p hps
              obtain ⟨_, hsome⟩ := mapM_some hrests
              obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hsome p hps)
              simpa [Function.comp, hq, RestArrow.mapWith, Contract.map] using (restImg_some hq).2.2.2.2) (fun p hps => ?_) W v
            · have hin : ∀ l ∈ p.receiver ++ p.arguments.flatten ++ p.result, l ∈ reads G i := fun l hl => by
                simp only [reads, hsch]
                exact List.mem_append_left _
                  (List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hps, by simpa [Arrow.operands, RestArrow.operands, List.append_assoc] using hl⟩))
              obtain ⟨q, hq⟩ : ∃ q, sigImg tbl (enter V i κ s.binders s2.binders) p = some q := by
                obtain ⟨_, hsome⟩ := mapM_some hsigs
                exact Option.isSome_iff_exists.mp (hsome p hps)
              obtain ⟨h1, h2, h3, heff⟩ := sigImg_some hq
              simp only [Function.comp, hq, Option.getD_some]
              refine ⟨hty _ _ _ _ _ h1 fun l hl => hrel' l (hin l (by simp [hl])), ?_,
                hty _ _ _ _ _ h3 fun l hl => hrel' l (hin l (by simp [hl]))⟩
              have hargs : ∀ (Ss Ts : List (List ι)), Ss.mapM (tyImg tbl (enter V i κ s.binders s2.binders)) = some Ts →
                  (∀ S ∈ Ss, ∀ l ∈ S, l ∈ reads G i) →
                  ArgsAgree n (Ss.map (setSem fun l => qDenoteWithArgs G (mixedParameters G) (assign ηL s.binders As, l)))
                    (Ts.map (mixedValues G (assign ηR s2.binders As))) := by
                intro Ss
                induction Ss with
                | nil => intro Ts h _; simp at h; subst h; exact .nil
                | cons S Ss ihs =>
                  intro Ts h hSs
                  cases hS : tyImg tbl (enter V i κ s.binders s2.binders) S with
                  | none => simp [List.mapM_cons, hS] at h
                  | some S' =>
                    cases hr : Ss.mapM (tyImg tbl (enter V i κ s.binders s2.binders)) with
                    | none => simp [List.mapM_cons, hS, hr] at h
                    | some Ts' =>
                      have : Ts = S' :: Ts' := by simp [List.mapM_cons, hS, hr] at h; exact h.symm
                      subst this
                      exact .cons (hty _ _ _ _ _ hS fun l hl => hrel' l (hSs S List.mem_cons_self l hl))
                        (ihs Ts' hr fun T hT => hSs T (List.mem_cons_of_mem _ hT))
              exact hargs _ _ h2 fun S hS l hl => hin l (by
                simp only [List.mem_append, List.mem_flatten]
                exact .inl (.inr ⟨S, hS, hl⟩))
            · have hin : ∀ l ∈ p.receiver ++ p.arguments.1.flatten ++ p.arguments.2 ++ p.result, l ∈ reads G i :=
                fun l hl => by
                  simp only [reads, hsch]
                  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hps, by simpa [Arrow.operands, RestArrow.operands, List.append_assoc] using hl⟩)
              obtain ⟨q, hq⟩ : ∃ q, restImg tbl (enter V i κ s.binders s2.binders) p = some q := by
                obtain ⟨_, hsome⟩ := mapM_some hrests
                exact Option.isSome_iff_exists.mp (hsome p hps)
              obtain ⟨h1, h2, h3, h4, heff⟩ := restImg_some hq
              simp only [Function.comp, hq, Option.getD_some]
              refine ⟨hty _ _ _ _ _ h1 fun l hl => hrel' l (hin l (by simp [hl])), ?_,
                hpack _ _ _ _ _ h3 fun l hl => hrel' l (hin l (by simp [hl])),
                hty _ _ _ _ _ h4 fun l hl => hrel' l (hin l (by simp [hl]))⟩
              have hargs : ∀ (Ss Ts : List (List ι)), Ss.mapM (tyImg tbl (enter V i κ s.binders s2.binders)) = some Ts →
                  (∀ S ∈ Ss, ∀ l ∈ S, l ∈ reads G i) →
                  ArgsAgree n (Ss.map (setSem fun l => qDenoteWithArgs G (mixedParameters G) (assign ηL s.binders As, l)))
                    (Ts.map (mixedValues G (assign ηR s2.binders As))) := by
                intro Ss
                induction Ss with
                | nil => intro Ts h _; simp at h; subst h; exact .nil
                | cons S Ss ihs =>
                  intro Ts h hSs
                  cases hS : tyImg tbl (enter V i κ s.binders s2.binders) S with
                  | none => simp [List.mapM_cons, hS] at h
                  | some S' =>
                    cases hr : Ss.mapM (tyImg tbl (enter V i κ s.binders s2.binders)) with
                    | none => simp [List.mapM_cons, hS, hr] at h
                    | some Ts' =>
                      have : Ts = S' :: Ts' := by simp [List.mapM_cons, hS, hr] at h; exact h.symm
                      subst this
                      exact .cons (hty _ _ _ _ _ hS fun l hl => hrel' l (hSs S List.mem_cons_self l hl))
                        (ihs Ts' hr fun T hT => hSs T (List.mem_cons_of_mem _ hT))
              exact hargs _ _ h2 fun S hS l hl => hin l (by
                simp only [List.mem_append, List.mem_flatten]
                exact .inl (.inl (.inr ⟨S, hS, hl⟩)))
      | none =>
        cases hT : T with
        | nil => simp [hsch, hT] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hsch, hT] at hrow
          | nil =>
            cases hm : G.meets i with
            | some pc =>
              -- A meet row: its parameters' images within its clauses' images.
              obtain ⟨p, cs⟩ := pc
              simp only [hsch, hT, hm] at hrow
              have hops := hrow
              unfold meetOk at hops
              simp only [Bool.and_eq_true, List.all_eq_true] at hops
              have hkinds := hops.1.1
              have hops := hops.1.2
              apply meet_row_value hpar hsch hm hrow
                (fun q hq => hrel q ((freeOk_meet hF hiD (by rw [meetParts_of hm]; exact hq)).1
                  (by simp [NormalGraph.params, beq_iff_eq.mp (hkinds q hq)])))
              intro c hc
              apply clauseImg_row tbl κ c _ _ _ _ _ n W v
              · intro S hS
                obtain ⟨S', hS'⟩ := Option.isSome_iff_exists.mp (hops c hc S hS)
                have hrelS : ∀ l ∈ S, RelKWith G (mixedParameters G) κ (fv V l) ηL ηR := by
                  intro l hl q hq
                  apply hrel q
                  have hlr : l ∈ reads G i := by
                    simp only [reads, hsch]
                    exact List.mem_flatMap.mpr ⟨c, List.mem_append_right _ (by simp [meetClauses, hm, hc]),
                      List.mem_flatten.mpr ⟨S, hS, hl⟩⟩
                  rcases (hreads l hlr).2 q hq with h1 | ⟨s', hs', _⟩
                  · exact h1
                  · rw [hsch] at hs'; cases hs'
                exact ⟨S', hS', hty _ _ _ _ _ hS' hrelS, hpack _ _ _ _ _ hS' hrelS⟩
              · intro m _ U u; simp [mixedValues, setSem]
              · intro m _ U vs; simp [graphArguments]
            | none =>
            simp only [hsch, hT, hm, Bool.and_eq_true, List.all_eq_true] at hrow
            obtain ⟨⟨⟨hip, hjp⟩, hops⟩, hG⟩ := hrow
            rw [singleton, qDenoteWithArgs_unfold, qDenoteWithArgs_unfold]
            have hi := hip
            have hj := hjp
            simp only [NormalGraph.plain, Bool.and_eq_true, Bool.not_eq_true',
              Option.isNone_iff_eq_none] at hi hj
            simp only [qLayerWithArgs, hi.1, hj.1, hi.2, hj.2, Bool.false_eq_true, ite_false]
            have key := sameClauses_iff hG (fun d => rowSem G (builtinValues G) (mixedValues G ηR)
                (graphArguments G ηR (mixedValues G ηR)) d n W v)
              (fun c f hf hn => by
                simp only [rowSem, semWithArgs_members (fun S T h => sameLabels_values h)
                  (fun S T h => sameLabels_arguments h) hf hn, builtinInvariant_map])
            simp only [setSem]
            refine Iff.trans ?_ key.symm
            simp only [List.mem_map]
            have clause : ∀ c ∈ G i,
                rowSem G (builtinValues G) (mixedValues G ηL) (graphArguments G ηL (mixedValues G ηL)) c n W v ↔
                  rowSem G (builtinValues G) (mixedValues G ηR) (graphArguments G ηR (mixedValues G ηR))
                    (clauseImg tbl κ c) n W v := by
              intro c hc
              apply clauseImg_row tbl κ c _ _ _ _ _ n W v
              · intro S hS
                obtain ⟨S', hS'⟩ := Option.isSome_iff_exists.mp (by simpa using hops c hc S hS)
                have hrelS : ∀ l ∈ S, RelKWith G (mixedParameters G) κ (fv V l) ηL ηR := by
                  intro l hl p hp
                  apply hrel p
                  have hlr : l ∈ reads G i := by
                    simp only [reads, hsch]
                    exact List.mem_flatMap.mpr ⟨c, List.mem_append_left _ hc, List.mem_flatten.mpr ⟨S, hS, hl⟩⟩
                  rcases (hreads l hlr).2 p hp with h1 | ⟨s', hs', _⟩
                  · exact h1
                  · rw [hsch] at hs'; cases hs'
                exact ⟨S', hS', hty _ _ _ _ _ hS' hrelS, hpack _ _ _ _ _ hS' hrelS⟩
              · intro m _ U u; simp [mixedValues, setSem]
              · intro m _ U vs; simp [graphArguments]
            constructor
            · rintro ⟨c, hc, h⟩
              exact ⟨_, ⟨c, hc, rfl⟩, (clause c hc).mp h⟩
            · rintro ⟨_, ⟨c, hc, rfl⟩, h⟩
              exact ⟨c, hc, (clause c hc).mpr h⟩
  · -- A parameter uses only its declared component on either side.
    simp only [hpar, ite_true, Bool.and_eq_true, beq_iff_eq] at hrow
    obtain ⟨rfl, _⟩ := hrow
    have hr := hrel i (hself hpar)
    obtain ⟨kind, hk⟩ : ∃ kind, G.parameterKinds i = some kind := by
      simpa [NormalGraph.params, Option.isSome_iff_exists] using hpar
    have hsource : qDenoteWithArgs G (mixedParameters G) (ηL,i) n W v ↔
        selectParameter (some kind) (ηL.1 i) n W (.inl v) := by
      rw [qDenoteWithArgs_unfold]
      simp [qLayerWithArgs, hpar, mixedParameters, selectParameter, hk]
    rw [hsource]
    cases hκ : κ.lookup i with
    | none =>
      rw [hκ] at hr
      simp only [Option.getD_none]
      have he := mixedMeaning_parameter G ηR i kind hk
      change selectParameter (G.parameterKinds i) _ = selectParameter (G.parameterKinds i) _ at hr
      rw [hk] at hr
      rw [hr]
      exact (iff_of_eq (congrFun (congrFun (congrFun he n) W) (.inl v))).symm
    | some U =>
      rw [hκ] at hr
      simp only [Option.getD_some]
      change selectParameter (G.parameterKinds i) _ = mixedMeaning G ηR U at hr
      rw [hk] at hr
      rw [hr]
      rfl

theorem assign_zip_map [DecidableEq ι] {k : ParameterSpace} (η : ParameterAssignment k ι) (F : List ι → ParameterFamily k) :
    ∀ {bs : List ι} {θs : List (List ι)} {b : ι} {U : List ι},
      (bs.zip θs).lookup b = some U → (assign η bs (θs.map F)).1 b = (F U).1
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | c :: bs, θ :: θs, b, U, h => by
    simp only [List.zip_cons_cons, List.lookup_cons] at h
    by_cases hb : b = c
    · subst hb
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      simp only [List.map_cons]
      exact assign_cons_head η b bs (F θ) (θs.map F)
    · rw [beq_false_of_ne hb] at h
      simp only [List.map_cons]
      rw [assign_cons_ne η bs (F θ) (θs.map F) hb]
      exact assign_zip_map η F h

/-- Checked substitution meets every binder bound, independently of whether
its arguments denote values or lists. The interpretation is supplied once and
used for both assignment and the bound check. -/
theorem bounded_substitution [DecidableEq ι] {k : ParameterSpace}
    (η : ParameterAssignment k ι) (F : List ι → ParameterFamily k)
    (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier)
    (s : SchemeRow ι) (θs : List (List ι))
    (hlen : θs.length = s.binders.length)
    (hbnd : ∀ b ∈ s.bounds, ∀ U, (s.binders.zip θs).lookup b.1 = some U →
      FamLe (F U).1 (D η b.2)) (n : Nat) :
    Bounded D η s (θs.map F) n := by
  intro b hb hbin j _ W u hu
  obtain ⟨θ, hθ⟩ := lookup_zip_isSome (ys := θs) hbin (by omega)
  rw [assign_zip_map η F hθ] at hu
  exact hbnd b hb θ hθ j W u hu

/-- Eliminate a universal callable with one checked substitution. This is the
shared semantic boundary for value and pack instantiation certificates. -/
theorem bounded_substitution_elim [DecidableEq ι] {k : ParameterSpace}
    (η : ParameterAssignment k ι) (F : List ι → ParameterFamily k)
    (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier)
    (s : SchemeRow ι) (θs : List (List ι))
    (body : List (ParameterFamily k) → Fam) (domain : SchemeDomain ι k)
    (hlen : θs.length = s.binders.length)
    (hal : domain.allowed s (θs.map F))
    (hbnd : ∀ b ∈ s.bounds, ∀ U, (s.binders.zip θs).lookup b.1 = some U →
      FamLe (F U).1 (D η b.2)) :
    FamLe (boundedSem D η s body domain) (body (θs.map F)) := by
  intro n W v h
  simpa only [trunc_id] using h.2 n (Nat.le_refl n) _ (by simp [hlen]) hal (bounded_substitution η F D s θs hlen hbnd n)

/-- Substituting a complete binder list changes exactly its bound names. -/
theorem assignment_substitution [DecidableEq ι] {k : ParameterSpace}
    (η : ParameterAssignment k ι) (F : List ι → ParameterFamily k)
    (bs : List ι) (θs : List (List ι)) (hlen : θs.length = bs.length) (b : ι) :
    (assign η bs (θs.map F)).1 b =
      match (bs.zip θs).lookup b with
      | some U => (F U).1
      | none => η.1 b := by
  cases hk : (bs.zip θs).lookup b with
  | none =>
    apply assign_nmem
    intro hb
    obtain ⟨U, hU⟩ := lookup_zip_isSome (ys := θs) hb (by omega)
    rw [hU] at hk
    cases hk
  | some U => exact assign_zip_map η F hk

/-- The existing executable kind check makes a mixed substitution satisfy the
selected table relation. Both assigned families come from the graph's single
two-component meaning; no pack contract is reconstructed from a value type. -/
theorem mixed_assignment_substitution [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)
    (bs : List ι) (θs : List (List ι)) (hlen : θs.length = bs.length)
    (hk : instKinds G bs θs = true) (S : List ι) :
    RelKWith G (mixedParameters G) (bs.zip θs) S
      (assign η bs (θs.map fun U => ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩)) η := by
  intro b _
  have he := assignment_substitution η
    (fun U => ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩) bs θs hlen b
  cases hU : (bs.zip θs).lookup b with
  | none =>
    rw [hU] at he
    dsimp only
    rw [he]
  | some U =>
    have hkind := List.all_eq_true.mp hk (b, U) (mem_of_lookup hU)
    cases hp : G.parameterKinds b with
    | none => simp [substitutionKind, hp] at hkind
    | some kind =>
      change selectParameter (G.parameterKinds b) _ = mixedMeaning G η U
      rw [hp, he, hU]
      exact mixedMeaning_selected G η U kind (by simpa [substitutionKind, hp] using hkind)

/-- The semantic obligation of an instantiation witness: its named type
images mean substitution, for values and argument packs together. Only images
used by the signatures must be named. How their equality is established is
separate: a finite closed table is one implementation, while recursive
equations require a proof covering their application families. -/
@[nospecialize] def InstanceImages [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)
    (bs : List ι) (θs : List (List ι)) (tbl : InstTable ι) : Prop :=
  ∀ S S', tyImg tbl (bs.zip θs) S = some S' →
    mixedMeaning G (assign η bs (θs.map fun U =>
      ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩)) S = mixedMeaning G η S'

/-- The current finite-table checker discharges the shared image obligation.
The table's closure and free-variable checks remain necessary here; separating
this theorem does not bypass them or accept a finite truncation. -/
theorem table_instanceImages [DecidableEq ι] {G : NormalGraph ι} (η : MixedAssignment ι)
    {bs : List ι} {θs : List (List ι)} {tbl : InstTable ι} {D : List ι} {V : FreeMap ι}
    (hlen : θs.length = bs.length) (hkinds : instKinds G bs θs = true)
    (hok : TableOk G tbl D V = true) : InstanceImages G η bs θs tbl := by
  let As : List MixedFamily := θs.map fun U =>
    ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩
  have hrel : ∀ l, RelKWith G (mixedParameters G) (bs.zip θs) (fv V l)
      (assign η bs As) η := fun l =>
    mixed_assignment_substitution G η bs θs hlen hkinds (fv V l)
  intro S S' hS
  funext m W x
  apply propext
  rw [mixedMeaning_union]
  exact tyImg_mixed_iff hS fun l _ T hT =>
    table_row_mixed hok m _ η (l, _, T) (entryImg_mem hT) (hrel l) W x

/-- Universal callable elimination depends on meaning-preserving images, not
on enumerating all rows a recursive type can reach. This is the same rule for
fixed and variadic signatures; their bounds, effects and receiver contracts
are retained by the existing signature-image check. -/
theorem inst_images_sound [DecidableEq ι] {G : NormalGraph ι} (η : MixedAssignment ι) {i : ι} {s : SchemeRow ι}
    {tbl : InstTable ι} {θs : List (List ι)} {L : Ops ι}
    {M : List (RestArrow (List ι))}
    (hp : G.params i = false) (hq : G.schemes i = some s) (hcon : s.construct = false)
    (hlen : θs.length = s.binders.length)
    (hal : G.domain.allowed s (θs.map fun U =>
      ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩))
    (hbnd : ∀ b ∈ s.bounds, ∀ U, (s.binders.zip θs).lookup b.1 = some U →
      FamLe (mixedMeaning G η U) (mixedMeaning G η b.2))
    (himages : InstanceImages G η s.binders θs tbl)
    (hL : ∀ q ∈ L, ∃ p ∈ s.signatures, instSig G tbl (s.binders.zip θs) p q = true)
    (hM : ∀ q ∈ M, ∃ p ∈ s.variadic, instRest G tbl (s.binders.zip θs) p q = true)
    : FamLe (mixedValues G η [i])
      (semWithArgs (excOf G) (mixedValues G η) (graphArguments G η (mixedValues G η)) (.arrs L M)) := by
  intro n W v hv
  obtain ⟨_, hm, hv⟩ := hv
  cases List.mem_singleton.mp hm
  have hs := (qDenoteWithArgs_unfold G (mixedParameters G) (η, i) n W v).mp hv
  simp only [qLayerWithArgs, hp, hq, Bool.false_eq_true, if_false] at hs
  have hinv : Invocable v := by simpa only [Callee, hcon, Bool.false_eq_true, if_false] using hs.1
  let F : List ι → MixedFamily := fun U => ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩
  let As : List MixedFamily := θs.map F
  have hc := bounded_substitution_elim η F
    (fun η' S => mixedMeaning G η' S) s θs
    (fun As => instanceTWithArgs (excOf G)
      (fun η' S => setSem (fun l => qDenoteWithArgs G (mixedParameters G) (η', l)) S) η s As (graphArguments G)) G.domain
    hlen hal hbnd n W v hs
  change instanceTWithArgs (excOf G)
    (fun η' S => setSem (fun l => qDenoteWithArgs G (mixedParameters G) (η', l)) S) η s As (graphArguments G) n W v at hc
  simp only [instanceTWithArgs, sigsT, hcon, Bool.false_eq_true, if_false] at hc
  have himg : ∀ S S', tyImg tbl (s.binders.zip θs) S = some S' →
      mixedMeaning G (assign η s.binders As) S = mixedMeaning G η S' := himages
  have hfam : ∀ S S', tyImg tbl (s.binders.zip θs) S = some S' →
      mixedValues G (assign η s.binders As) S = mixedValues G η S' := by
    intro S S' hS
    funext m W' v
    exact congrFun (congrFun (congrFun (himg S S' hS) m) W') (.inl v)
  have hpack : ∀ S S', tyImg tbl (s.binders.zip θs) S = some S' →
      graphArguments G (assign η s.binders As) (mixedValues G (assign η s.binders As)) S =
        graphArguments G η (mixedValues G η) S' := by
    intro S S' hS
    funext m W' vs
    exact congrFun (congrFun (congrFun (himg S S' hS) m) W') (.inr vs)
  have hargs : ∀ (Ss Ts : List (List ι)), Ss.mapM (tyImg tbl (s.binders.zip θs)) = some Ts →
      Ss.map (mixedValues G (assign η s.binders As)) = Ts.map (mixedValues G η) := by
    intro Ss
    induction Ss with
    | nil => intro Ts h; simp at h; subst h; rfl
    | cons S Ss ihs =>
      intro Ts h
      cases hS : tyImg tbl (s.binders.zip θs) S with
      | none => simp [List.mapM_cons, hS] at h
      | some S' =>
        cases hr : Ss.mapM (tyImg tbl (s.binders.zip θs)) with
        | none => simp [List.mapM_cons, hS, hr] at h
        | some Ts' =>
          have : Ts = S' :: Ts' := by simp [List.mapM_cons, hS, hr] at h; exact h.symm
          subst this
          simp only [List.map_cons, hfam S S' hS, ihs Ts' hr]
  -- A receiver the instance states within a scheme receiver admitting every
  -- value: every receiver is a closed value.
  have anyRecv : ∀ (P Q : List ι), receiverUniverse G P Q = true → ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U → ∀ r, mixedValues G η Q j U r →
        mixedValues G (assign η s.binders As) P j U r := by
    intro P Q hP j hj U _ r hr
    simp only [receiverUniverse, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hP
    rcases hP with hP | ⟨hP, hQ⟩
    · obtain ⟨l, _, hl⟩ := hr
      exact top_row_mixed hP (mixedDenote_value G η l hl)
    · exact mixed_of_expand hP (sourceTy_exc hQ η j U r hr)
  refine ⟨⟨hinv, fun q' hq' => ?_⟩, ⟨hinv, fun r' hr' => ?_⟩⟩
  · obtain ⟨q, hqL, rfl⟩ := List.mem_map.mp hq'
    obtain ⟨p, hps, hsig⟩ := hL q hqL
    have hpr := hc.1.2 _ (List.mem_map_of_mem hps)
    change PromiseWith (excOf G) p.effect (ArgsShort (p.arguments.map (mixedValues G (assign η s.binders As))))
      (mixedValues G (assign η s.binders As) p.receiver)
      (mixedValues G (assign η s.binders As) p.result) n W v at hpr
    obtain ⟨hsig, heffect⟩ := Bool.and_eq_true_iff.mp hsig
    rcases Bool.or_eq_true_iff.mp hsig with hsig | hbody
    · obtain ⟨q', hq', s1, s2, s3, se⟩ := sigMatch_some hsig
      obtain ⟨h1, h2, h3, he⟩ := sigImg_some hq'
      have e1 := (hfam _ _ h1).trans (sameLabels_values s1)
      have e3 := (hfam _ _ h3).trans (sameLabels_values s3)
      have e2 := (hargs _ _ h2).trans (sameLabelLists_values s2)
      simp only [e1, e2, e3] at hpr
      exact hpr.weaken (Effect.covers_sound heffect) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
    · simp only [Bool.and_eq_true] at hbody
      obtain ⟨ps, r, h2, h3, s2, s3, he⟩ := sigBodyMatch_some hbody.2
      have e3 := (hfam _ _ h3).trans (sameLabels_values s3)
      have e2 := (hargs _ _ h2).trans (sameLabelLists_values s2)
      simp only [e2, e3] at hpr
      exact (hpr.weaken_recv (anyRecv p.receiver q.receiver hbody.1)).weaken
        (Effect.covers_sound heffect) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
  · obtain ⟨q, hqM, rfl⟩ := List.mem_map.mp hr'
    obtain ⟨p, hps, hsig⟩ := hM q hqM
    have hpr := hc.2.2 _ (List.mem_map_of_mem hps)
    change PromiseWith (excOf G) p.effect (ArgsRest _ (graphArguments G (assign η s.binders As)
      (mixedValues G (assign η s.binders As)) p.arguments.2)) _ _ n W v at hpr
    change PromiseWith (excOf G) p.effect (ArgsRest (p.arguments.1.map (mixedValues G (assign η s.binders As)))
      (graphArguments G (assign η s.binders As) (mixedValues G (assign η s.binders As)) p.arguments.2))
      (mixedValues G (assign η s.binders As) p.receiver) (mixedValues G (assign η s.binders As) p.result) n W v at hpr
    obtain ⟨hsig, heffect⟩ := Bool.and_eq_true_iff.mp hsig
    rcases Bool.or_eq_true_iff.mp hsig with hsig | hbody
    · obtain ⟨q', hq', s1, s2, s3, s4, se⟩ := restMatch_some hsig
      obtain ⟨h1, h2, h3, h4, he⟩ := restImg_some hq'
      have e1 := (hfam _ _ h1).trans (sameLabels_values s1)
      have e3 := (hpack _ _ h3).trans (sameLabels_arguments s3)
      have e4 := (hfam _ _ h4).trans (sameLabels_values s4)
      have e2 := (hargs _ _ h2).trans (sameLabelLists_values s2)
      simp only [e1, e2, e3, e4] at hpr
      exact hpr.weaken (Effect.covers_sound heffect) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
    · simp only [Bool.and_eq_true] at hbody
      obtain ⟨ps, e, r, h2, h3, h4, s2, s3, s4, he⟩ := restBodyMatch_some hbody.2
      have e3 := (hpack _ _ h3).trans (sameLabels_arguments s3)
      have e4 := (hfam _ _ h4).trans (sameLabels_values s4)
      have e2 := (hargs _ _ h2).trans (sameLabelLists_values s2)
      simp only [e2, e3, e4] at hpr
      exact (hpr.weaken_recv (anyRecv p.receiver q.receiver hbody.1)).weaken
        (Effect.covers_sound heffect) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)

/-! ## Families of pairs

A family entry
(RECURSIVE-EQUATIONS §7) holds its pairs where its hypotheses hold: its
variables are parameter rows, and one entry stands for every pair that is
an instance of it. One level induction justifies both (`pairs_sound`),
parameterized by the relation premises are read through: an ordinary table
is the case without hypotheses, a family the case whose
premises may be instances of its entries (`family_sound`). -/

/-- Both components of one type within another's, at one level. -/
@[nospecialize] def MixedLe (G : NormalGraph ι) (η : MixedAssignment ι) (A B : List ι) (n : Nat) : Prop :=
  ∀ (W : WorldT n) x, mixedMeaning G η A n W x → mixedMeaning G η B n W x

theorem MixedLe.values {G : NormalGraph ι} {η : MixedAssignment ι} {A B : List ι} {n : Nat}
    (h : MixedLe G η A B n) : FamLeAt G η A B n := fun W v hv => h W (.inl v) hv

/-- Hypotheses hold at every level up to `n`, in both components. -/
@[nospecialize] def HypsHold (G : NormalGraph ι) (η : MixedAssignment ι) (hyps : List (ι × ι)) (n : Nat) : Prop :=
  ∀ h ∈ hyps, ∀ j, j ≤ n → MixedLe G η [h.1] [h.2] j

/-- Hypotheses hold below `n`, and for values at `n`: what proving values at
`n` reads. -/
@[nospecialize] def HypsHoldValues (G : NormalGraph ι) (η : MixedAssignment ι) (hyps : List (ι × ι))
    (n : Nat) : Prop :=
  (∀ h ∈ hyps, ∀ j, j < n → MixedLe G η [h.1] [h.2] j) ∧ ∀ h ∈ hyps, FamLeAt G η [h.1] [h.2] n

theorem HypsHold.values {G : NormalGraph ι} {η : MixedAssignment ι} {hyps : List (ι × ι)}
    {n : Nat} (h : HypsHold G η hyps n) : HypsHoldValues G η hyps n :=
  ⟨fun p hp j hj => h p hp j (Nat.le_of_lt hj), fun p hp => (h p hp n (Nat.le_refl n)).values⟩

/-- **Quantified-α** (RECURSIVE-EQUATIONS §6). A scheme row's quantified
signatures cover another's up to renaming the target's binders to the
source's: as many binders, distinct on each side, of pairwise equal kinds;
each source bound on a binder matched by the target's bound on the renamed
binder, which is within it (read outside both schemes); no source binder free
in the target's signatures unless it is also a target binder; and the
source's signatures cover the target's renamed. The renaming is the
checker's own substitution, never a certificate's. -/
@[nospecialize] def SchemeRenames [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G))
    (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop) (i j : ι) : Prop :=
  match sub, G.schemes i, G.schemes j with
  | some r, some s, some s' =>
    G.params i = false ∧ G.params j = false ∧
    s.binders.length = s'.binders.length ∧ s.binders.Nodup ∧ s'.binders.Nodup ∧
    (∀ pq ∈ s.binders.zip s'.binders, G.parameterKinds pq.1 = G.parameterKinds pq.2) ∧
    (∀ b ∈ s.bounds, ∃ b' ∈ s'.bounds,
      (s.binders.zip s'.binders).lookup b.1 = some b'.1 ∧ R b'.2 b.2) ∧
    (∀ A ∈ s'.body.operands, ∀ x ∈ r.free A,
      x ∈ s.binders → x ∈ s'.binders) ∧ sameShape s s' = true ∧
    CoversWith G none R known arrows [] s.body
      (s'.body.map (r.substitute (s'.binders.zip (s.binders.map fun p => [p]))))
  | _, _, _ => False

/-- The quantified rule: the same binders (`SchemeCoversWith`), of which
renaming is the general case. -/
@[nospecialize] def SchemeCoversAlpha [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G))
    (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop) (i j : ι) : Prop :=
  SchemeCoversWith G R known arrows i j ∨ SchemeRenames G sub R known arrows i j

/-- A meet part of a family pair below another (RECURSIVE-EQUATIONS §3.3,
§7.3): a scheme whose signatures cover the other's up to renaming, or a
variable below the other by a hypothesis. Without hypotheses it is
quantified coverage alone. -/
@[nospecialize] def PartCovers [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G))
    (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop)
    (hyps : List (ι × ι)) (a b : ι) : Prop :=
  SchemeCoversAlpha G sub R known arrows a b ∨ (a, b) ∈ hyps

/-- Opaque rows of a family pair: as for a pair without hypotheses, and a
row may also be below a target row by a hypothesis, and a scheme row below
one whose signatures its own cover up to renaming. A meet reads its parts
the same way (`PartCovers`): a target meet's variable part is covered by a
source part, or the source row, below it by a hypothesis. -/
@[nospecialize] def OpaqueFamily [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G))
    (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop)
    (hyps : List (ι × ι)) (S T : List ι) : Prop :=
  ∀ i ∈ S, G.plain i = true ∨ i ∈ T ∨ OpaqueUniverse G T i ∨
    MeetOpaque G (PartCovers G sub R known arrows hyps)
      (fun a => ∃ b ∈ clausesOf G T, CoversWith G sub R known arrows S a b) T i ∨
    (∃ y ∈ T, (i, y) ∈ hyps) ∨ ∃ j ∈ T, SchemeCoversAlpha G sub R known arrows i j

theorem SchemeCoversAlpha.mono [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} {known : Known ι}
    {arrows arrows' : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    (ha : ∀ L S M, arrows L S M → arrows' L S M) {i j : ι}
    (h : SchemeCoversAlpha G sub R known arrows i j) : SchemeCoversAlpha G sub R known arrows' i j := by
  rcases h with h | h
  · left
    unfold SchemeCoversWith at h ⊢
    split at h
    · exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        CoversWith.mono ha h.2.2.2.2.2⟩
    · exact h.elim
  · right
    unfold SchemeRenames at h ⊢
    split at h
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hord, h9⟩ := h
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, hord, CoversWith.mono ha h9⟩
    · exact h.elim

theorem OpaqueFamily.mono [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} {known : Known ι}
    {arrows arrows' : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    (ha : ∀ L S M, arrows L S M → arrows' L S M) {hyps : List (ι × ι)} {S T : List ι}
    (h : OpaqueFamily G sub R known arrows hyps S T) : OpaqueFamily G sub R known arrows' hyps S T := by
  intro i hi
  rcases h i hi with h | h | h | h | h | ⟨j, hj, hc⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl (h.mono (fun _ _ => Or.imp_left (SchemeCoversAlpha.mono ha))
      fun a ⟨b, hb, hc⟩ => ⟨b, hb, CoversWith.mono ha hc⟩))))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨j, hj, SchemeCoversAlpha.mono ha hc⟩))))

/-- The three core conditions for one pair (POSITIVE-TYPES "Core tables",
RECURSIVE-EQUATIONS §7.3), premises read through `R`. -/
@[nospecialize] def PairOk [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (known : Known ι)
    (R : List ι → List ι → Prop) (hyps : List (ι × ι)) (A B : List ι) : Prop :=
  SameKind G A B = true ∧
    OpaqueFamily G sub R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) hyps A B ∧
    ∀ a ∈ sourceClauses G A ++ meetSources G A B hyps, ∃ b ∈ clausesOf G B, Covers G sub R known A a b

/-- **Quantified-α, soundly.** At every instance the target admits, the
source admits it too at its own binders (each bound is matched); there the
source's signatures give the target's renamed ones, whose meaning at the
source's instance is the target's at its own (`renamed_meaning`). -/
theorem renames_sound [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {sub : Option (Renaming G)} {R : List ι → List ι → Prop} {known : Known ι} {i j : ι}
    (hc : SchemeRenames G sub R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) i j) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n) (W : WorldT n) (v : Val)
    (hv : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    qDenoteWithArgs G (mixedParameters G) (η, j) n W v := by
  unfold SchemeRenames at hc
  split at hc
  · rename_i r s s' hs hs'
    obtain ⟨hpi, hpj, hlen, hnp, hnq, hkinds, hbnd, hfresh, hord, hcov⟩ := hc
    rw [qDenoteWithArgs_unfold] at hv ⊢
    simp only [qLayerWithArgs, hpi, hpj, hs, hs', Bool.false_eq_true, if_false] at hv ⊢
    refine ⟨sameShape_construct hord ▸ hv.1, fun q hq As hl _hal hb => ?_⟩
    have hall := hv.2 q hq
    have hre : ReassignSound G η R q := fun i s As hs =>
      ⟨fun k hk => (hre i s As hs).1 k (by omega),
       fun k hk => (hre i s As hs).2 k (by omega)⟩
    have hr := fun k (hk : k < q) => hr k (by omega)
    have hpa := fun k (hk : k < q) => hpa k (by omega)
    let W := trunc q hq W
    let n := q
    have hal := (sameShape_allowed G.domain hord As).mpr _hal
    have hb' : Bounded (fun θ S => (mixedParameters G).bound θ
        (setSem (fun l => qDenoteWithArgs G (mixedParameters G) (θ, l))) S) η s As n := by
      intro b hbm hbin k hk U u hu
      obtain ⟨b', hb'm, hlk, hR⟩ := hbnd b hbm
      obtain ⟨m, hm1, hm2, hpb', hqb'⟩ := lookup_zip_index hlk
      have heq : (assign η s.binders As).1 b.1 = (assign η s'.binders As).1 b'.1 := by
        rw [← hpb', ← hqb', assign_getElem η hnp (by omega) m hm1,
          assign_getElem η hnq (by omega) m hm2]
      have hin : b'.1 ∈ s'.binders := hqb' ▸ List.getElem_mem hm2
      have hu' := hb b' hb'm hin k hk U u (heq ▸ hu)
      cases u with
      | inl w => exact hr k hk _ _ hR U w hu'
      | inr ws => exact hpa k hk _ _ hR U ws hu'
    have hi : semWithArgs (excOf G) (mixedValues G (assign η s.binders As)) (mixedArgs G (assign η s.binders As))
        s.body n W v := (instance_body G η s As) ▸ hall As (by rw [hlen]; exact hl) hal hb'
    have hcovered := covers_body_sound hcov (by
      unfold SchemeRow.body; rw [sameShape_construct hord]
      cases s'.construct <;> simp [Clause.map, mapFields]) n (hre i s As hs).1 (hre i s As hs).2 W v hi
    show instanceTWithArgs _ _ η s' As _ n W v
    rw [instance_body]
    rw [← semWithArgs_map_meaning (η := assign η s.binders As)
      (f := r.substitute (s'.binders.zip (s.binders.map fun p => [p]))) fun S hS => ?_]
    · exact hcovered
    · apply renamed_meaning r η hlen hnp hnq hkinds (by omega) S
      rcases hS with hS | rfl
      · exact .inr (hfresh S hS)
      · exact .inl rfl
  · exact hc.elim

/-- **Quantified signatures, soundly.** A member of a scheme row is a member of
one its quantified signatures cover: at each instance the target admits, the
source admits it too, and there the arrow coverage holds, its premises read
at that instance's assignment. -/
theorem scheme_covers_sound [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι} {R known i j}
    (hc : SchemeCoversWith G R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) i j) (n : Nat)
    (hre : ReassignSound G η R n)
    (W : WorldT n) (v : Val)
    (hv : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    qDenoteWithArgs G (mixedParameters G) (η, j) n W v := by
  unfold SchemeCoversWith at hc
  split at hc
  · rename_i s s' hs hs'
    obtain ⟨hpi, hpj, hbs, hbnd, hord, hcov⟩ := hc
    rw [qDenoteWithArgs_unfold] at hv ⊢
    simp only [qLayerWithArgs, hpi, hpj, hs, hs', Bool.false_eq_true, if_false] at hv ⊢
    refine ⟨sameShape_construct hord ▸ hv.1, fun q hq As hl _hal hb => ?_⟩
    have hall := hv.2 q hq
    have hre : ReassignSound G η R q := fun i s As hs =>
      ⟨fun k hk => (hre i s As hs).1 k (by omega),
       fun k hk => (hre i s As hs).2 k (by omega)⟩
    let W := trunc q hq W
    let n := q
    have hal := (sameShape_allowed G.domain hord As).mpr _hal
    have hb' : Bounded (fun θ S => (mixedParameters G).bound θ
        (setSem (fun l => qDenoteWithArgs G (mixedParameters G) (θ, l))) S) η s As n := by
      intro b hbm hbin j hj U u hu
      rw [hbs] at hbin hu
      exact hb b (hbnd b hbm) hbin j hj U u hu
    have hi : semWithArgs (excOf G) (mixedValues G (assign η s.binders As)) (mixedArgs G (assign η s.binders As))
        s.body n W v := (instance_body G η s As) ▸ hall As (by rw [hbs]; exact hl) hal hb'
    show instanceTWithArgs _ _ η s' As _ n W v
    rw [instance_body, ← hbs]
    exact covers_body_sound hcov (by
      unfold SchemeRow.body; rw [sameShape_construct hord]
      cases s'.construct <;> simp) n (hre i s As hs).1 (hre i s As hs).2 W v hi
  · exact hc.elim

theorem alpha_sound [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι}
    {sub : Option (Renaming G)} {R : List ι → List ι → Prop} {known : Known ι} {i j : ι}
    (hc : SchemeCoversAlpha G sub R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) i j) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n) (W : WorldT n) (v : Val)
    (hv : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    qDenoteWithArgs G (mixedParameters G) (η, j) n W v := by
  rcases hc with hc | hc
  · exact scheme_covers_sound hc n hre W v hv
  · exact renames_sound hc n hr hpa hre W v hv

/-- A scheme row is no parameter row. -/
theorem SchemeCoversAlpha.not_param [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop} {i j : ι}
    (h : SchemeCoversAlpha G sub R known arrows i j) : G.params i = false := by
  rcases h with h | h
  · unfold SchemeCoversWith at h
    split at h
    · exact h.1
    · exact h.elim
  · unfold SchemeRenames at h
    split at h
    · exact h.1
    · exact h.elim

/-- **Values of a pair, at a level.** Each split source clause is covered,
its premises read below the level; each opaque row is in the target, below
`top`, a meet row covered through its clauses or below a target row by its
parameters, below a target row by a hypothesis, or a scheme row whose
signatures cover a target scheme's, renaming binders. -/
theorem pair_values_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {R : List ι → List ι → Prop} {hyps : List (ι × ι)} {A B : List ι}
    {η : MixedAssignment ι} {n : Nat} (hc : PairOk G sub known R hyps A B)
    (hknown : ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G η S T j) (hpa : ArgsLeBelow G η R n)
    (hre : ReassignSound G η R n) (hhyp : ∀ h ∈ hyps, FamLeAt G η [h.1] [h.2] n) :
    FamLeAt G η A B n := by
  intro W v hv
  have hself : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      mixedValues G η A j U v := fun j hj U hU =>
    (setSem_adm (fun i => qDenoteWithArgs_adm G (mixedParameters G) (η, i)) A).transfer
      hv j (Nat.le_of_lt hj) U hU
  -- A meet part below another holds the value: by quantified coverage, or by
  -- a hypothesis, which holds at `n` for values.
  have hpart : ∀ a b, PartCovers G sub R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) hyps a b →
      qDenoteWithArgs G (mixedParameters G) (η, a) n W v →
      qDenoteWithArgs G (mixedParameters G) (η, b) n W v := by
    intro a b h hv
    rcases h with h | h
    · exact alpha_sound h n hr hpa hre W v hv
    · obtain ⟨b', hb', hv'⟩ := hhyp (a, b) h W v ⟨a, List.mem_singleton_self a, hv⟩
      cases List.mem_singleton.mp hb'
      exact hv'
  rcases mixed_cases hv with ⟨c, hcm, hv⟩ | ⟨i, hi, hp, hv⟩
  · obtain ⟨a, ha, hv⟩ := (splitClause_row G _ _ _ c n W v).mpr hv
    obtain ⟨b, hb, hcover⟩ :=
      hc.2.2 a (List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, hcm, ha⟩))
    exact mixed_expand_mpr ⟨b, hb, Covers.sound hcover hknown n hr hpa hre W v hself hv⟩
  · rcases (hc.2.1 i hi).resolve_left (by simp [hp]) with
      hB | htop | hmeet | ⟨y, hy, hh⟩ | ⟨j, hj, hsc⟩
    · exact ⟨i, hB, hv⟩
    · rcases htop with htop | ⟨hsource, hparam, hscheme⟩
      · exact mixed_expand_mpr ⟨.top, htop, mixedDenote_value G η i hv,
          builtinInvariant_of_withoutInvariant rfl n W v⟩
      · obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hscheme
        rw [qDenoteWithArgs_unfold] at hv
        simp only [qLayerWithArgs, hparam, hs, Bool.false_eq_true, ite_false] at hv
        have hn := hv.1.not_plain
        obtain ⟨fs, code, oid, rfl, hscoped⟩ := hv.1.obj
        exact mixed_expand_mpr ⟨.source, hsource, ⟨rfl, hscoped⟩,
          builtinInvariant_of_not_plain hn⟩
    · rcases hmeet with ⟨hmeet, hsm | hsrc⟩ | ⟨j, hj, hjm, hparts, hcl⟩
      · by_cases hB : i ∈ B
        · exact ⟨i, hB, hv⟩
        · by_cases hbelow : B.any (meetBelow G i · hyps) = true
          · obtain ⟨j, hj, hij⟩ := List.any_eq_true.mp hbelow
            exact ⟨j, hj, meetBelow_sound hmeet hij hhyp hv⟩
          obtain ⟨c, hcm, hv⟩ := meet_clause_of hmeet hv
          obtain ⟨a, ha, hv⟩ := (splitClause_row G _ _ _ c n W v).mpr hv
          have hmem : a ∈ meetSources G A B hyps := List.mem_flatMap.mpr ⟨c,
            List.mem_flatMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hmeet, hB, hbelow, hsm]⟩,
              hcm⟩, ha⟩
          obtain ⟨b, hb, hcover⟩ := hc.2.2 a (List.mem_append_right _ hmem)
          exact mixed_expand_mpr ⟨b, hb, Covers.sound hcover hknown n hr hpa hre W v hself hv⟩
      · rcases hsrc with hbelow | ⟨q, hq, hqp, j, hj, hsc⟩ | hcov
        · obtain ⟨j, hj, hij⟩ := List.any_eq_true.mp hbelow
          exact ⟨j, hj, meetBelow_sound hmeet hij (by simp) hv⟩
        · exact ⟨j, hj, hpart _ _ hsc (meet_part_value hmeet hq hqp hv)⟩
        · obtain ⟨c, hcm, hv⟩ := meet_clause_of hmeet hv
          obtain ⟨a, ha, hv⟩ := (splitClause_row G _ _ _ c n W v).mpr hv
          obtain ⟨b, hb, hcover⟩ := hcov a (List.mem_flatMap.mpr ⟨c, hcm, ha⟩)
          exact mixed_expand_mpr ⟨b, hb, Covers.sound hcover hknown n hr hpa hre W v hself hv⟩
      · exact ⟨j, hj, meet_target_value hjm hpart hparts hcl hv⟩
    · obtain ⟨y', hy', hv'⟩ := hhyp (i, y) hh W v ⟨i, List.mem_singleton_self i, hv⟩
      cases List.mem_singleton.mp hy'
      exact ⟨y, hy, hv'⟩
    · exact ⟨j, hj, alpha_sound hsc n hr hpa hre W v hv⟩

/-- **Argument lists of a pair, at a level,** from value premises at the same
level. This uses the executable kind condition, so value top cannot discharge
a list edge. A pack parameter of the source is in the target or below a
target row by a hypothesis. -/
theorem pair_arguments_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {R : List ι → List ι → Prop} {hyps : List (ι × ι)} {A B : List ι}
    {η : MixedAssignment ι} {n : Nat} (hc : PairOk G sub known R hyps A B)
    (hv : ∀ S T, R S T → FamLeAt G η S T n)
    (hhyp : ∀ h ∈ hyps, ∀ (W : WorldT n) vs,
      mixedMeaning G η [h.1] n W (.inr vs) → mixedMeaning G η [h.2] n W (.inr vs)) :
    ∀ (W : WorldT n) vs, mixedMeaning G η A n W (.inr vs) → mixedMeaning G η B n W (.inr vs) := by
  intro W vs ha
  have ⟨hsort, hopaque, hcover⟩ := hc
  simp only [SameKind, Bool.or_eq_true, Bool.and_eq_true] at hsort
  rcases hsort with ⟨hav, _⟩ | ⟨haa, hba⟩
  · exact False.elim (mixedMeaning_noArguments G η A hav n W vs ha)
  have noTop : .top ∉ clausesOf G B := by
    intro h
    obtain ⟨a, bs, he⟩ := argument_clause hba h
    cases he
  change graphArguments G η (mixedValues G η) A n W vs at ha
  change graphArguments G η (mixedValues G η) B n W vs
  obtain ⟨i, hi, ha⟩ := ha
  by_cases hp : G.parameterKinds i = some .arguments
  · have hn : G.plain i = false := by simp [NormalGraph.plain, NormalGraph.params, hp]
    rcases hopaque i hi with h | h | h | h | ⟨y, hy, hh⟩ | ⟨j, -, h⟩
    · simp [hn] at h
    · exact ⟨i, h, by simpa [hp, NormalGraph.listParam] using ha⟩
    · rcases h with h | ⟨_, hparam, _⟩
      · exact False.elim (noTop h)
      · simp [NormalGraph.params, hp] at hparam
    · rcases h with ⟨h, -⟩ | ⟨j, hj, hjm, -, -⟩
      · simp [NormalGraph.meetRow, NormalGraph.params, hp] at h
      · -- A meet row is a value row, which a list-sorted target has none of.
        have hk := List.all_eq_true.mp hba j hj
        simp only [NormalGraph.meetRow, NormalGraph.params, Bool.and_eq_true, Bool.not_eq_true',
          Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hjm
        obtain ⟨⟨hjp, _⟩, hjs⟩ := hjm
        cases hq : G.parameterKinds j <;> simp_all
    · obtain ⟨y', hy', h2⟩ := hhyp (i, y) hh W vs ⟨i, List.mem_singleton_self i, ha⟩
      cases List.mem_singleton.mp hy'
      exact ⟨y, hy, h2⟩
    · have := h.not_param
      simp [NormalGraph.params, hp] at this
  · have hlp : G.listParam i = false := by
      have hk := List.all_eq_true.mp haa i hi
      cases hq : G.parameterKinds i with
      | none => simp [NormalGraph.listParam, hq]
      | some k => cases k <;> simp_all [NormalGraph.listParam]
    simp only [hlp, Bool.false_eq_true, ite_false] at ha
    obtain ⟨c, hci, hca⟩ := ha
    cases c <;> try contradiction
    case pack a bs =>
      have hsrc : .pack a bs ∈ sourceClauses G A :=
        List.mem_flatMap.mpr ⟨.pack a bs, List.mem_flatMap.mpr ⟨i, hi, hci⟩, by simp [splitClause]⟩
      obtain ⟨b, hb, hcov⟩ := hcover _ (List.mem_append_left _ hsrc)
      obtain ⟨d, ds, rfl⟩ := argument_clause hba hb
      obtain ⟨j, hj, hbj⟩ := List.mem_flatMap.mp hb
      have hjplain := NormalGraph.plain_of_clauses hbj
      have hjkind : G.parameterKinds j ≠ some .arguments := by
        intro h
        simp [NormalGraph.plain, NormalGraph.params, h] at hjplain
      refine ⟨j, hj, ?_⟩
      simp only [NormalGraph.listParam_of_plain hjplain, Bool.false_eq_true, ite_false]
      refine ⟨.pack d ds, hbj, ?_⟩
      change ∀ q ∈ d :: ds, ArgumentContracts.Fits (tupleFams (mixedValues G η) q) n W vs
      intro q hq
      obtain ⟨p, hp, hpq⟩ := hcov q hq
      exact covers_arguments hpq (mixedValues G η) (fun A v => A n W v)
        (fun S T h v hv' => hv S T h W v hv') vs (hca p hp)

/-- **Pairs by level induction.** Families of pairs indexed by `E`, each with
the relation its premises are read through and its hypotheses, whose pairs
all meet the core conditions, hold at every level where their hypotheses
do, provided premises are sound given the pairs below the level
(`below`), and, for the values an argument list's contracts read, at the
level once all values there are (`same`). Entering a scheme must keep the
hypotheses (`fixed`). Values at a level come first, from premises below it;
argument lists at the level then from values at it. -/
theorem pairs_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {E : Type} (R : E → List ι → List ι → Prop) (hyps : E → List (ι × ι))
    (pairs : E → List (List ι × List ι))
    (hvalid : ∀ e, ∀ p ∈ pairs e, PairOk G sub known (R e) (hyps e) p.1 p.2)
    (hk : ∀ η : MixedAssignment ι,
      ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    (fixed : ∀ e (η : MixedAssignment ι) n i s As, G.schemes i = some s →
      HypsHoldValues G η (hyps e) n → HypsHoldValues G (assign η s.binders As) (hyps e) n)
    (below : ∀ n, (∀ j, j < n → ∀ e η, HypsHold G η (hyps e) j → ∀ p ∈ pairs e, MixedLe G η p.1 p.2 j) →
      ∀ e η, HypsHoldValues G η (hyps e) n → ∀ S T, R e S T → ∀ j, j < n → MixedLe G η S T j)
    (same : ∀ n, (∀ j, j < n → ∀ e η, HypsHold G η (hyps e) j → ∀ p ∈ pairs e, MixedLe G η p.1 p.2 j) →
      (∀ e η, HypsHoldValues G η (hyps e) n → ∀ p ∈ pairs e, FamLeAt G η p.1 p.2 n) →
      ∀ e η, HypsHold G η (hyps e) n → ∀ S T, R e S T → FamLeAt G η S T n) :
    ∀ n, (∀ e η, HypsHoldValues G η (hyps e) n → ∀ p ∈ pairs e, FamLeAt G η p.1 p.2 n) ∧
      ∀ e η, HypsHold G η (hyps e) n → ∀ p ∈ pairs e, MixedLe G η p.1 p.2 n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have lower : ∀ j, j < n → ∀ e η, HypsHold G η (hyps e) j → ∀ p ∈ pairs e, MixedLe G η p.1 p.2 j :=
      fun j hj => (ih j hj).2
    have prem := below n lower
    have values : ∀ e η, HypsHoldValues G η (hyps e) n → ∀ p ∈ pairs e, FamLeAt G η p.1 p.2 n := by
      intro e η hη p hp
      exact pair_values_sound (hvalid e p hp) (hk η)
        (fun j hj S T h => (prem e η hη S T h j hj).values)
        (fun j hj S T h W vs hvs => prem e η hη S T h j hj W (.inr vs) hvs)
        (fun i s As hs => ⟨fun j hj S T h => (prem e _ (fixed e η n i s As hs hη) S T h j hj).values,
          fun j hj S T h W vs hvs => prem e _ (fixed e η n i s As hs hη) S T h j hj W (.inr vs) hvs⟩)
        hη.2
    refine ⟨values, fun e η hη p hp W x hx => ?_⟩
    cases x with
    | inl v => exact values e η hη.values p hp W v hx
    | inr vs =>
      exact pair_arguments_sound (hvalid e p hp) (same n lower values e η hη)
        (fun h hh W vs hvs => hη h hh n (Nat.le_refl n) W (.inr vs) hvs) W vs hx

/-! ### Family entries

An entry is an assumption of RECURSIVE-EQUATIONS §4.2: a goal pair with
variables, hypotheses between them and a table. Its premises are the rules
`Tab`, `TabRen` and `Union` (`Prem`) and `Mem`, `Hyp`, `MeetHyp` and `Inst`
(`PremLabel`); `Inst` discharges an instance's hypotheses by further
premises, on strictly smaller types. `family_sound` is Theorem 1. -/

theorem MixedLe.of_labels {G : NormalGraph ι} {η : MixedAssignment ι} {A B : List ι} {m : Nat}
    (h : ∀ l ∈ A, MixedLe G η [l] B m) : MixedLe G η A B m := by
  intro W x hx
  obtain ⟨l, hl, hx⟩ := (mixedMeaning_union G η A m W x).mp hx
  exact h l hl W x hx

theorem FamLeAt.of_labels {G : NormalGraph ι} {η : MixedAssignment ι} {A B : List ι} {m : Nat}
    (h : ∀ l ∈ A, FamLeAt G η [l] B m) : FamLeAt G η A B m := by
  intro W v hv
  obtain ⟨l, hl, hx⟩ := (mixedMeaning_union G η A m W (.inl v)).mp hv
  exact h l hl W v hx

theorem MixedLe.of_mem {G : NormalGraph ι} {η : MixedAssignment ι} {l : ι} {B : List ι} {m : Nat}
    (h : l ∈ B) : MixedLe G η [l] B m :=
  fun W x hx => mixed_subset (fun i hi => by rw [List.mem_singleton.mp hi]; exact h) m W x hx

theorem MixedLe.congr {G : NormalGraph ι} {η θ : MixedAssignment ι} {A A' B B' : List ι} {m : Nat}
    (ha : mixedMeaning G η A = mixedMeaning G θ A') (hb : mixedMeaning G η B = mixedMeaning G θ B')
    (h : MixedLe G θ A' B' m) : MixedLe G η A B m := by
  intro W x hx
  rw [ha] at hx
  rw [hb]
  exact h W x hx

theorem FamLeAt.congr {G : NormalGraph ι} {η θ : MixedAssignment ι} {A A' B B' : List ι} {m : Nat}
    (ha : mixedMeaning G η A = mixedMeaning G θ A') (hb : mixedMeaning G η B = mixedMeaning G θ B')
    (h : FamLeAt G θ A' B' m) : FamLeAt G η A B m := by
  intro W v hv
  have hv' : mixedMeaning G η A m W (.inl v) := hv
  rw [ha] at hv'
  show mixedMeaning G η B m W (.inl v)
  rw [hb]
  exact h W v hv'

/-- Instantiating parameters at types of their kinds: each parameter row
means its replacement. -/
theorem assignment_images [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)
    (bs : List ι) (θs : List (List ι)) (hlen : θs.length = bs.length)
    (kinds : instKinds G bs θs = true) (p : ι) (hp : G.params p = true) :
    mixedMeaning G (assign η bs (θs.map fun U => ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩)) [p] =
      mixedMeaning G η (replace (bs.zip θs) p) := by
  obtain ⟨kind, hk⟩ : ∃ kind, G.parameterKinds p = some kind := by
    simpa [NormalGraph.params, Option.isSome_iff_exists] using hp
  have hr := mixed_assignment_substitution G η bs θs hlen kinds [p]
  cases lookup : (bs.zip θs).lookup p with
  | some U =>
    simpa only [replace, lookup, Option.getD_some] using
      mixed_parameter_image G (bs.zip θs) _ η p kind U hk lookup hr
  | none =>
    rw [mixedMeaning_parameter _ _ _ _ hk]
    simp only [replace, lookup, Option.getD_none]
    rw [mixedMeaning_parameter _ _ _ _ hk]
    have he := hr p (by simp)
    rw [lookup] at he
    change selectParameter (G.parameterKinds p) _ =
      selectParameter (G.parameterKinds p) _ at he
    simpa only [hk] using he

/-- A family entry, an assumption (RECURSIVE-EQUATIONS §4.2): its goal
`source ≤ target`, its variables, hypotheses between them, its table
`T_a`, and the instances its premises use, each an entry's index and the
types its variables are instantiated at, in order. -/
structure Entry (ι : Type) where
  source : List ι
  target : List ι
  variables : List ι := []
  hypotheses : List (ι × ι) := []
  table : Table ι := []
  instances : List (Nat × List (List ι)) := []
  deriving DecidableEq, Repr

/-- The goal, then the table. -/
@[nospecialize] def Entry.pairs (e : Entry ι) : List (List ι × List ι) := (e.source, e.target) :: e.table

/-- A type at an instance: its variables replaced, when a renaming exists. -/
@[nospecialize] def image [DecidableEq ι] {G : NormalGraph ι} (sub : Option (Renaming G))
    (σ : List (ι × List ι)) (A : List ι) : List ι :=
  match sub with
  | some r => r.substitute σ A
  | none => A

/-- The entries an instance may cite, by index (the set `𝒜` of §4.2). -/
abbrev Lookup (ι : Type) := Nat → Option (Entry ι)

/-- An entry's hypotheses relate parameter rows. -/
@[nospecialize] def HypParams (G : NormalGraph ι) (e : Entry ι) : Prop :=
  ∀ h ∈ e.hypotheses, G.params h.1 = true ∧ G.params h.2 = true

/-- The instance of entry `e` at the types `xs` relates the label `l` to
`B`: `xs` of `e`'s variables' kinds, `e`'s substituted source holding `l`,
its substituted target within `B`. -/
@[nospecialize] def InstanceAt [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (e : Entry ι)
    (l : ι) (B : List ι) (xs : List (List ι)) : Prop :=
  xs.length = e.variables.length ∧ instKinds G e.variables xs = true ∧
    (sub.isNone = true → e.variables = []) ∧
    l ∈ image sub (e.variables.zip xs) e.source ∧
    ∀ b ∈ image sub (e.variables.zip xs) e.target, b ∈ B

/-- A label's size, by which `Inst`'s premises decrease: the renaming's, and
nothing without one (no instance then has a hypothesis). -/
@[nospecialize] def labelSize [DecidableEq ι] {G : NormalGraph ι} (sub : Option (Renaming G)) (l : ι) : Nat :=
  match sub with
  | some r => r.size l
  | none => 0

/-- A union's size: its labels'. -/
@[nospecialize] def typeSize [DecidableEq ι] {G : NormalGraph ι} (sub : Option (Renaming G)) (A : List ι) : Nat :=
  (A.map (labelSize sub)).sum

/-- A renaming of bound rows (`TabRen`): each renamed row a parameter row
and no family variable, given one such row of its kind. Hypotheses relate
family variables only, so a renaming leaves them in place. -/
@[nospecialize] def boundRow [DecidableEq ι] {G : NormalGraph ι} (r : Renaming G) (x : ι) : Bool :=
  G.params x && !r.familyVar x

@[nospecialize] def RenamesBound [DecidableEq ι] (G : NormalGraph ι) (r : Renaming G) (σ : List (ι × List ι)) : Prop :=
  instKinds G σ.unzip.1 σ.unzip.2 = true ∧
    ∀ q ∈ σ, boundRow r q.1 = true ∧ q.2.length = 1 ∧ ∀ y ∈ q.2, boundRow r y = true

instance [DecidableEq ι] (G : NormalGraph ι) (r : Renaming G) (σ : List (ι × List ι)) :
    Decidable (RenamesBound G r σ) := by
  unfold RenamesBound; infer_instance

mutual
/-- **Premises** (RECURSIVE-EQUATIONS §4.2), `Π;T ⊢ A ⊑ B` in the entry
`f`, whose hypotheses are `Π` and table `T`: a table pair (`tab`), a table
pair at renamed bound rows (`tabRen`, the renaming the representation's own
matcher proposes), or each label of `A` below `B` (`union`). -/
inductive Prem [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (look : Lookup ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (f : Entry ι) : List ι → List ι → Prop where
  | tab {A B : List ι} : (A, B) ∈ f.table → Prem G sub look gen f A B
  | tabRen {A B : List ι} (r : Renaming G) (p : List ι × List ι) : sub = some r → p ∈ f.table →
      RenamesBound G r (r.rename p A B) →
      (∀ l ∈ A, l ∈ r.substitute (r.rename p A B) p.1) →
      (∀ b ∈ r.substitute (r.rename p A B) p.2, b ∈ B) → Prem G sub look gen f A B
  | union {A B : List ι} : (∀ l ∈ A, PremLabel G sub look gen f l B) → Prem G sub look gen f A B
/-- A label below a union: a member (`mem`), below a member by a hypothesis
(`hyp`), a meet below a member by its parts and the hypotheses (`meetHyp`),
or by an instance of a cited entry (`inst`), its hypotheses discharged by
premises on strictly smaller types. The instances are the entry's own
(`f.instances`) and those `gen` proposes, verified code (`Var` proposes
same-head instances); what it proposes is checked like any other. -/
inductive PremLabel [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (look : Lookup ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (f : Entry ι) : ι → List ι → Prop where
  | mem {l : ι} {B : List ι} : l ∈ B → PremLabel G sub look gen f l B
  | hyp {l y : ι} {B : List ι} : (l, y) ∈ f.hypotheses → y ∈ B → PremLabel G sub look gen f l B
  | meetHyp {l y : ι} {B : List ι} : G.meetRow l = true → y ∈ B → meetBelow G l y f.hypotheses = true →
      PremLabel G sub look gen f l B
  | inst {l : ι} {B : List ι} (w : Nat × List (List ι)) (e : Entry ι) :
      w ∈ f.instances ++ gen l B → look w.1 = some e → InstanceAt G sub e l B w.2 →
      (∀ h ∈ e.hypotheses, typeSize sub (replace (e.variables.zip w.2) h.1) +
        typeSize sub (replace (e.variables.zip w.2) h.2) < labelSize sub l + typeSize sub B) →
      (∀ h ∈ e.hypotheses,
        Prem G sub look gen f (replace (e.variables.zip w.2) h.1) (replace (e.variables.zip w.2) h.2)) →
      PremLabel G sub look gen f l B
end

/-- A meet label below a target label by its parts holds where the
hypotheses do, for values; it admits no argument list. -/
theorem meetBelow_mixed [DecidableEq ι] {G : NormalGraph ι} {η : MixedAssignment ι} {l : ι}
    {B : List ι} {hyps : List (ι × ι)} {m : Nat} (hl : G.meetRow l = true)
    (hb : ∃ y ∈ B, meetBelow G l y hyps = true) (hh : ∀ h ∈ hyps, FamLeAt G η [h.1] [h.2] m) :
    MixedLe G η [l] B m := by
  obtain ⟨y, hy, hly⟩ := hb
  intro W x hx
  cases x with
  | inl v =>
    obtain ⟨i, hi, hv⟩ := hx
    cases List.mem_singleton.mp hi
    exact ⟨y, hy, meetBelow_sound hl hly hh hv⟩
  | inr vs =>
    refine (mixedMeaning_noArguments G η [l] ?_ m W vs hx).elim
    simp only [NormalGraph.meetRow, Bool.and_eq_true, Bool.not_eq_true'] at hl
    simp [NormalGraph.hasKind, NormalGraph.params, Option.isNone_iff_eq_none] at hl ⊢
    obtain ⟨⟨hp, _⟩, hm⟩ := hl
    simp [hp, hm]

/-- **Valid entries** (`Valid`, §4.2): every pair of every entry of `F`
meets the core conditions, its premises read in its entry, instances citing
the entries `look` names. -/
@[nospecialize] def FamilyValid [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (known : Known ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (look : Lookup ι) (F : List (Entry ι)) : Prop :=
  ∀ f ∈ F, ∀ p ∈ f.pairs, PairOk G sub known (Prem G sub look gen f) f.hypotheses p.1 p.2

/-- The variable discipline: hypotheses relate an entry's own variables, and
variables are rows the representation reserves for them, parameter rows no
scheme binds (none without a renaming). -/
@[nospecialize] def VariablesOk [DecidableEq ι] {G : NormalGraph ι} (sub : Option (Renaming G))
    (F : List (Entry ι)) : Prop :=
  (∀ f ∈ F, ∀ h ∈ f.hypotheses, h.1 ∈ f.variables ∧ h.2 ∈ f.variables) ∧
    ∀ f ∈ F, ∀ x ∈ f.variables, match sub with
      | some r => r.familyVar x = true
      | none => False

/-- An entry's goal holds wherever its hypotheses do. -/
@[nospecialize] def EntrySound (G : NormalGraph ι) (e : Entry ι) : Prop :=
  (∀ n η, HypsHold G η e.hypotheses n → MixedLe G η e.source e.target n) ∧
    ∀ n η, HypsHoldValues G η e.hypotheses n → FamLeAt G η e.source e.target n

/-- A hypothesis names a family variable: a parameter row no scheme binds. -/
theorem VariablesOk.hyp [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {F : List (Entry ι)} (hv : VariablesOk sub F) {f : Entry ι} (hf : f ∈ F) {h : ι × ι}
    (hh : h ∈ f.hypotheses) :
    ∀ x, x = h.1 ∨ x = h.2 → G.params x = true ∧ (∀ i s, G.schemes i = some s → x ∉ s.binders) ∧
      ∀ r, sub = some r → r.familyVar x = true := by
  intro x hx
  have hmem : x ∈ f.variables := by
    rcases hx with rfl | rfl
    · exact (hv.1 f hf h hh).1
    · exact (hv.1 f hf h hh).2
  have hvar := hv.2 f hf x hmem
  cases sub with
  | none => exact hvar.elim
  | some r =>
    exact ⟨r.familyVar_param x hvar, fun i s hs => r.familyVar_unbound i s x hs hvar,
      fun r' hr => by cases hr; exact hvar⟩

theorem VariablesOk.params [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {F : List (Entry ι)} (hv : VariablesOk sub F) {f : Entry ι} (hf : f ∈ F) : HypParams G f :=
  fun h hh => ⟨(hv.hyp hf hh h.1 (.inl rfl)).1, (hv.hyp hf hh h.2 (.inr rfl)).1⟩

theorem zip_unzip_eq (σ : List (α × β)) : σ.unzip.1.zip σ.unzip.2 = σ := List.zip_unzip σ

/-- An instance moves the entry's goal to the use: at the assignment giving
its variables their types' meanings, each hypothesis means its instance, the
source holds the label and the target is within `B`. -/
theorem InstanceAt.transport [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {e : Entry ι} {l : ι} {B : List ι} {xs : List (List ι)}
    (hi : InstanceAt G sub e l B xs) (hpar : sub.isSome = true → HypParams G e)
    (η : MixedAssignment ι) :
    ∃ η' : MixedAssignment ι,
      (∀ h ∈ e.hypotheses,
        mixedMeaning G η' [h.1] = mixedMeaning G η (replace (e.variables.zip xs) h.1) ∧
        mixedMeaning G η' [h.2] = mixedMeaning G η (replace (e.variables.zip xs) h.2)) ∧
      FamLe (mixedMeaning G η [l]) (mixedMeaning G η' e.source) ∧
      FamLe (mixedMeaning G η' e.target) (mixedMeaning G η B) := by
  obtain ⟨hlen, hkinds, hnone, hl, hB⟩ := hi
  cases sub with
  | none =>
    have hv : e.variables = [] := hnone rfl
    refine ⟨η, fun h _ => ?_, ?_, ?_⟩
    · simp [hv, replace]
    · exact mixed_subset fun i hi => by
        rw [List.mem_singleton.mp hi]; simpa [image] using hl
    · exact mixed_subset fun b hb => hB b (by simpa [image] using hb)
  | some r =>
    have images := assignment_images G η e.variables xs hlen hkinds
    have hp := hpar rfl
    refine ⟨_, fun h hh => ⟨images _ (hp h hh).1, images _ (hp h hh).2⟩, ?_, ?_⟩
    · rw [r.substitute_meaning _ η _ images e.source]
      exact mixed_subset fun i hi => by
        rw [List.mem_singleton.mp hi]; simpa [image] using hl
    · rw [r.substitute_meaning _ η _ images e.target]
      exact mixed_subset fun b hb => hB b (by simpa [image] using hb)

/-- `TabRen` moves a table pair to its renaming: at the assignment giving the
renamed rows their images' meanings, the hypotheses keep theirs, and the
renamed pair means the pair there. -/
theorem RenamesBound.transport [DecidableEq ι] {G : NormalGraph ι} {r : Renaming G}
    {σ : List (ι × List ι)} (hren : RenamesBound G r σ) {hyps : List (ι × ι)}
    (hfv : ∀ h ∈ hyps, r.familyVar h.1 = true ∧ r.familyVar h.2 = true)
    (hfp : ∀ h ∈ hyps, G.params h.1 = true ∧ G.params h.2 = true) (η : MixedAssignment ι) :
    ∃ η' : MixedAssignment ι,
      (∀ h ∈ hyps, mixedMeaning G η' [h.1] = mixedMeaning G η [h.1] ∧
        mixedMeaning G η' [h.2] = mixedMeaning G η [h.2]) ∧
      ∀ A, mixedMeaning G η' A = mixedMeaning G η (r.substitute σ A) := by
  have hlen : σ.unzip.2.length = σ.unzip.1.length := by simp
  have images := assignment_images G η σ.unzip.1 σ.unzip.2 hlen hren.1
  rw [zip_unzip_eq] at images
  refine ⟨_, fun h hh => ?_, r.substitute_meaning _ η σ images⟩
  have keep : ∀ x, G.params x = true → r.familyVar x = true →
      mixedMeaning G (assign η σ.unzip.1 (σ.unzip.2.map fun U =>
        ⟨mixedMeaning G η U, mixedMeaning_valid G η U⟩)) [x] = mixedMeaning G η [x] := by
    intro x hx hvar
    apply mixedMeaning_param_eq rfl hx
    apply assign_nmem
    intro hmem
    obtain ⟨q, hq, rfl⟩ : ∃ q ∈ σ, q.1 = x := by
      simp only [List.unzip_fst, List.mem_map] at hmem
      exact hmem
    have := (hren.2 q hq).1
    simp [boundRow, hvar] at this
  exact ⟨keep _ (hfp h hh).1 (hfv h hh).1, keep _ (hfp h hh).2 (hfv h hh).2⟩

/-- **Premises below the level** (the inner induction of Theorem 1, §4.2).
Read at `η` below `n`, a premise holds where the entry's table pairs hold at
every assignment meeting its hypotheses, its hypotheses hold at `η`, and every
cited entry's goal holds where its hypotheses do. -/
theorem prem_mixed [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {look : Lookup ι}
    {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} {η : MixedAssignment ι} {n : Nat}
    (hfv : ∀ r, sub = some r → ∀ h ∈ f.hypotheses, r.familyVar h.1 = true ∧ r.familyVar h.2 = true)
    (hfp : HypParams G f)
    (hpar : ∀ k e, look k = some e → sub.isSome = true → HypParams G e)
    (htab : ∀ j, j < n → ∀ η', HypsHold G η' f.hypotheses j → ∀ p ∈ f.table, MixedLe G η' p.1 p.2 j)
    (hhyp : ∀ h ∈ f.hypotheses, ∀ j, j < n → MixedLe G η [h.1] [h.2] j)
    (hent : ∀ j, j < n → ∀ k e η', look k = some e → HypsHold G η' e.hypotheses j →
      MixedLe G η' e.source e.target j) :
    (∀ {A B}, Prem G sub look gen f A B → ∀ j, j < n → MixedLe G η A B j) ∧
      ∀ {l B}, PremLabel G sub look gen f l B → ∀ j, j < n → MixedLe G η [l] B j := by
  have tabRen : ∀ (r : Renaming G) (p : List ι × List ι) (A B : List ι), sub = some r →
      p ∈ f.table → RenamesBound G r (r.rename p A B) →
      (∀ l ∈ A, l ∈ r.substitute (r.rename p A B) p.1) →
      (∀ b ∈ r.substitute (r.rename p A B) p.2, b ∈ B) → ∀ j, j < n → MixedLe G η A B j := by
    intro r p A B hs hp hren hA hB j hj
    obtain ⟨η', hkeep, hsub⟩ := hren.transport (hfv r hs) hfp η
    have hyps' : HypsHold G η' f.hypotheses j := fun h hh k hk =>
      MixedLe.congr (hkeep h hh).1 (hkeep h hh).2 (hhyp h hh k (by omega))
    have hpair := MixedLe.congr (hsub _).symm (hsub _).symm (htab j hj η' hyps' p hp)
    intro W x hx
    exact mixed_subset hB j W x (hpair W x (mixed_subset hA j W x hx))
  let motive_1 := fun (A B : List ι) (_ : Prem G sub look gen f A B) =>
    ∀ j, j < n → MixedLe G η A B j
  let motive_2 := fun (l : ι) (B : List ι) (_ : PremLabel G sub look gen f l B) =>
    ∀ j, j < n → MixedLe G η [l] B j
  have tab : ∀ {A B} (h : (A, B) ∈ f.table), motive_1 A B (.tab h) := fun h j hj =>
    htab j hj η (fun h' hh k hk => hhyp h' hh k (by omega)) _ h
  have ren : ∀ {A B} r p hs hp hren hA hB, motive_1 A B (.tabRen r p hs hp hren hA hB) :=
    fun r p hs hp hren hA hB => tabRen r p _ _ hs hp hren hA hB
  have union : ∀ {A B} (h : ∀ l ∈ A, PremLabel G sub look gen f l B),
      (∀ l hl, motive_2 l B (h l hl)) → motive_1 A B (.union h) :=
    fun _ ih j hj => MixedLe.of_labels fun l hl => ih l hl j hj
  have mem : ∀ {l B} (h : l ∈ B), motive_2 l B (.mem h) := fun h _ _ => MixedLe.of_mem h
  have hyp : ∀ {l y B} (hh : (l, y) ∈ f.hypotheses) (hy : y ∈ B), motive_2 l B (.hyp hh hy) :=
    fun hh hy j hj W x hx => MixedLe.of_mem hy W x (hhyp _ hh j hj W x hx)
  have meetHyp : ∀ {l y B} (hm : G.meetRow l = true) (hy : y ∈ B) (hb : meetBelow G l y f.hypotheses = true),
      motive_2 l B (.meetHyp hm hy hb) :=
    fun hm hy hb j hj => meetBelow_mixed hm ⟨_, hy, hb⟩ fun h hh => (hhyp h hh j hj).values
  have inst : ∀ {l B} (w : Nat × List (List ι)) (e : Entry ι) hw hl hi hdec
      (hps : ∀ h ∈ e.hypotheses, Prem G sub look gen f (replace (e.variables.zip w.2) h.1)
        (replace (e.variables.zip w.2) h.2)),
      (∀ h hh, motive_1 _ _ (hps h hh)) → motive_2 l B (.inst w e hw hl hi hdec hps) := by
    intro l B w e _ hl hi _ _ ih j hj
    obtain ⟨η', himg, hsrc, htgt⟩ := hi.transport (hpar w.1 e hl) η
    have hyps' : HypsHold G η' e.hypotheses j := fun h hh k hk =>
      MixedLe.congr (himg h hh).1 (himg h hh).2 (ih h hh k (by omega))
    have goal := hent j hj w.1 e η' hl hyps'
    exact fun W x hx => htgt j W x (goal W x (hsrc j W x hx))
  exact ⟨fun h => Prem.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h,
    fun h => PremLabel.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h⟩

/-- **Premises for values at the level.** As `prem_mixed`, at `n` itself
for values: table pairs, hypotheses and cited goals for values at `n`, and
everything below `n`. -/
theorem prem_values [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {look : Lookup ι}
    {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} {η : MixedAssignment ι} {n : Nat}
    (hfv : ∀ r, sub = some r → ∀ h ∈ f.hypotheses, r.familyVar h.1 = true ∧ r.familyVar h.2 = true)
    (hfp : HypParams G f)
    (hpar : ∀ k e, look k = some e → sub.isSome = true → HypParams G e)
    (htab : ∀ j, j < n → ∀ η', HypsHold G η' f.hypotheses j → ∀ p ∈ f.table, MixedLe G η' p.1 p.2 j)
    (htabv : ∀ η', HypsHoldValues G η' f.hypotheses n → ∀ p ∈ f.table, FamLeAt G η' p.1 p.2 n)
    (hη : HypsHoldValues G η f.hypotheses n)
    (hent : ∀ j, j < n → ∀ k e η', look k = some e → HypsHold G η' e.hypotheses j →
      MixedLe G η' e.source e.target j)
    (hentv : ∀ k e η', look k = some e → HypsHoldValues G η' e.hypotheses n →
      FamLeAt G η' e.source e.target n) :
    (∀ {A B}, Prem G sub look gen f A B → FamLeAt G η A B n) ∧
      ∀ {l B}, PremLabel G sub look gen f l B → FamLeAt G η [l] B n := by
  have below := prem_mixed (look := look) (gen := gen) hfv hfp hpar htab hη.1 hent
  let motive_1 := fun (A B : List ι) (_ : Prem G sub look gen f A B) => FamLeAt G η A B n
  let motive_2 := fun (l : ι) (B : List ι) (_ : PremLabel G sub look gen f l B) =>
    FamLeAt G η [l] B n
  have tab : ∀ {A B} (h : (A, B) ∈ f.table), motive_1 A B (.tab h) := fun h => htabv η hη _ h
  have ren : ∀ {A B} r p hs hp hren hA hB, motive_1 A B (.tabRen r p hs hp hren hA hB) := by
    intro A B r p hs hp hren hA hB
    obtain ⟨η', hkeep, hsub⟩ := hren.transport (hfv r hs) hfp η
    have hyps' : HypsHoldValues G η' f.hypotheses n :=
      ⟨fun h hh k hk => MixedLe.congr (hkeep h hh).1 (hkeep h hh).2 (hη.1 h hh k hk),
        fun h hh => FamLeAt.congr (hkeep h hh).1 (hkeep h hh).2 (hη.2 h hh)⟩
    have hpair := htabv η' hyps' p hp
    have hpair' : FamLeAt G η (r.substitute (r.rename p A B) p.1)
        (r.substitute (r.rename p A B) p.2) n :=
      FamLeAt.congr (hsub _).symm (hsub _).symm hpair
    intro W v hv
    exact (mixed_subset hB n W (.inl v) (hpair' W v (mixed_subset hA n W (.inl v) hv)))
  have union : ∀ {A B} (h : ∀ l ∈ A, PremLabel G sub look gen f l B),
      (∀ l hl, motive_2 l B (h l hl)) → motive_1 A B (.union h) :=
    fun _ ih => FamLeAt.of_labels fun l hl => ih l hl
  have mem : ∀ {l B} (h : l ∈ B), motive_2 l B (.mem h) := fun h => (MixedLe.of_mem h).values
  have hyp : ∀ {l y B} (hh : (l, y) ∈ f.hypotheses) (hy : y ∈ B), motive_2 l B (.hyp hh hy) :=
    fun hh hy W v hv => (MixedLe.of_mem hy).values W v (hη.2 _ hh W v hv)
  have meetHyp : ∀ {l y B} (hm : G.meetRow l = true) (hy : y ∈ B) (hb : meetBelow G l y f.hypotheses = true),
      motive_2 l B (.meetHyp hm hy hb) :=
    fun hm hy hb => (meetBelow_mixed hm ⟨_, hy, hb⟩ hη.2).values
  have inst : ∀ {l B} (w : Nat × List (List ι)) (e : Entry ι) hw hl hi hdec
      (hps : ∀ h ∈ e.hypotheses, Prem G sub look gen f (replace (e.variables.zip w.2) h.1)
        (replace (e.variables.zip w.2) h.2)),
      (∀ h hh, motive_1 _ _ (hps h hh)) → motive_2 l B (.inst w e hw hl hi hdec hps) := by
    intro l B w e _ hl hi _ hps ih
    obtain ⟨η', himg, hsrc, htgt⟩ := hi.transport (hpar w.1 e hl) η
    have hyps' : HypsHoldValues G η' e.hypotheses n :=
      ⟨fun h hh k hk => MixedLe.congr (himg h hh).1 (himg h hh).2 (below.1 (hps h hh) k hk),
        fun h hh => FamLeAt.congr (himg h hh).1 (himg h hh).2 (ih h hh)⟩
    have goal := hentv w.1 e η' hl hyps'
    exact fun W v hv => htgt n W (.inl v) (goal W v (hsrc n W (.inl v) hv))
  exact ⟨fun h => Prem.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h,
    fun h => PremLabel.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h⟩

/-- **Theorem 1** (RECURSIVE-EQUATIONS §4.2). Valid entries, whose instances
cite entries of `F` or entries already sound (`look`), hold at every
assignment meeting their hypotheses, at every level, in both components:
by level induction (`pairs_sound`), each premise by the inner induction
on its derivation (`prem_mixed`, `prem_values`). -/
theorem family_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)}
    (hvalid : FamilyValid G sub known gen look F) (hvars : VariablesOk sub F)
    (hlook : ∀ k e, look k = some e → e ∈ F ∨ (EntrySound G e ∧ HypParams G e))
    (hk : ∀ η : MixedAssignment ι,
      ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2))) :
    ∀ f ∈ F, (∀ n η, HypsHold G η f.hypotheses n → ∀ p ∈ f.pairs, MixedLe G η p.1 p.2 n) ∧
      ∀ n η, HypsHoldValues G η f.hypotheses n → ∀ p ∈ f.pairs, FamLeAt G η p.1 p.2 n := by
  let E := {f : Entry ι // f ∈ F}
  have hpar : ∀ k e, look k = some e → sub.isSome = true → HypParams G e := by
    intro k e hl _
    rcases hlook k e hl with he | he
    · exact hvars.params he
    · exact he.2
  have hfv : ∀ e : E, ∀ r, sub = some r → ∀ h ∈ e.1.hypotheses,
      r.familyVar h.1 = true ∧ r.familyVar h.2 = true := fun e r hr h hh =>
    ⟨(hvars.hyp e.2 hh h.1 (.inl rfl)).2.2 r hr, (hvars.hyp e.2 hh h.2 (.inr rfl)).2.2 r hr⟩
  have hs := pairs_sound (G := G) (sub := sub) (known := known) (E := E)
    (fun e => Prem G sub look gen e.1) (fun e => e.1.hypotheses) (fun e => e.1.pairs)
    (fun e p hp => hvalid e.1 e.2 p hp) hk
    (by
      intro e η n i s As hs hη
      have heq : ∀ h ∈ e.1.hypotheses, ∀ x, x = h.1 ∨ x = h.2 →
          mixedMeaning G (assign η s.binders As) [x] = mixedMeaning G η [x] := by
        intro h hh x hx
        have hvx := hvars.hyp e.2 hh x hx
        exact mixedMeaning_param_eq rfl hvx.1 (assign_nmem η s.binders As (hvx.2.1 i s hs))
      exact ⟨fun h hh j hj => MixedLe.congr (heq h hh _ (.inl rfl)) (heq h hh _ (.inr rfl))
          (hη.1 h hh j hj),
        fun h hh => FamLeAt.congr (heq h hh _ (.inl rfl)) (heq h hh _ (.inr rfl)) (hη.2 h hh)⟩)
    (by
      intro n lower e η hη S T h j hj
      refine (prem_mixed (hfv e) (hvars.params e.2) hpar
        (fun j hj η' hh p hp => lower j hj e η' hh p (List.mem_cons_of_mem _ hp)) hη.1
        (fun j hj k e' η' hl hh => ?_)).1 h j hj
      rcases hlook k e' hl with he | he
      · exact lower j hj ⟨e', he⟩ η' hh _ List.mem_cons_self
      · exact he.1.1 j η' hh)
    (by
      intro n lower values e η hη S T h
      refine (prem_values (hfv e) (hvars.params e.2) hpar
        (fun j hj η' hh p hp => lower j hj e η' hh p (List.mem_cons_of_mem _ hp))
        (fun η' hh p hp => values e η' hh p (List.mem_cons_of_mem _ hp)) hη.values
        (fun j hj k e' η' hl hh => ?_) (fun k e' η' hl hh => ?_)).1 h
      · rcases hlook k e' hl with he | he
        · exact lower j hj ⟨e', he⟩ η' hh _ List.mem_cons_self
        · exact he.1.1 j η' hh
      · rcases hlook k e' hl with he | he
        · exact values ⟨e', he⟩ η' hh _ List.mem_cons_self
        · exact he.1.2 n η' hh)
  intro f hf
  exact ⟨fun n η hη => (hs n).2 ⟨f, hf⟩ η hη, fun n η hη => (hs n).1 ⟨f, hf⟩ η hη⟩

/-- Every entry of a valid family is sound. -/
theorem family_entries_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)}
    (hvalid : FamilyValid G sub known gen look F) (hvars : VariablesOk sub F)
    (hlook : ∀ k e, look k = some e → e ∈ F ∨ (EntrySound G e ∧ HypParams G e))
    (hk : ∀ η : MixedAssignment ι,
      ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2))) :
    ∀ e ∈ F, EntrySound G e := by
  intro e he
  have h := family_sound hvalid hvars hlook hk e he
  exact ⟨fun n η hη => h.1 n η hη _ List.mem_cons_self,
    fun n η hη => h.2 n η hη _ List.mem_cons_self⟩

/-- A pair of a variable-free entry holds at every assignment: the claims a
family certificate proves. -/
theorem family_closed_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)}
    (hvalid : FamilyValid G sub known gen look F) (hvars : VariablesOk sub F)
    (hlook : ∀ k e, look k = some e → e ∈ F ∨ (EntrySound G e ∧ HypParams G e))
    (hk : ∀ η : MixedAssignment ι,
      ∀ k ∈ known, FamLe (mixedValues G η k.1) (mixedSem G η (.arrs k.2.1 k.2.2)))
    {f : Entry ι} (hf : f ∈ F) (hclosed : f.hypotheses = []) {S T : List ι} (hp : (S, T) ∈ f.pairs) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  intro η n W x hx
  refine (family_sound hvalid hvars hlook hk f hf).1 n η ?_ (S, T) hp W x hx
  intro h hh
  rw [hclosed] at hh
  cases hh

/-- The graph whose parameter rows mean `η`. No check reads the assignment, so
every derivation over `G` is one over each reassignment. -/
@[nospecialize] def reassign (G : NormalGraph ι) (η : MixedAssignment ι) : NormalGraph ι := { G with env := η }

end Verification.PositiveRules
