import Verification.Types.EquationGraphs
import Verification.Types.PositiveRules

/-! Meet labels mean exactly the intersection of their parts' values
(RECURSIVE-EQUATIONS §3.3). A meet's row is computed from its parts' rows;
its meaning reads its parameter and scheme parts at its own level and its
clause parts through the normalized conjunction (`meetLists_row`). A meet
admits no argument list. Distribution over unions follows. -/
namespace Verification.EquationGraphs
open PositiveGraphs PositiveRules PositiveNormalization Tower

theorem Types.mem_labels : ∀ {ts : Types} {h : ts.scoped sig 0 0 = true} {q : Label sig},
    q ∈ ts.labels h ↔ q.1 ∈ ts.toList
  | .nil, _, _ => by simp [Types.labels]
  | .cons t ts, h, q => by
    simp only [Types.labels, List.mem_cons, Types.toList_cons, Types.mem_labels]
    exact or_congr ⟨fun he => he ▸ rfl, fun he => Subtype.ext he⟩ Iff.rfl

/-- A row a template yields, or a parameter's, is never a meet row. -/
theorem Equations.baseRow_ne_meet (equations : Equations) (q : Label equations.signature)
    (p : Label equations.signature) (cs : List (Clause (List (Label equations.signature))))
    (ps : List (Label equations.signature)) : equations.baseRow q ≠ .meet p cs ps := by
  apply q.cases (P := fun q => equations.baseRow q ≠ .meet p cs ps)
  · intro scope
    have hv := (equations.body scope.head).2
    cases hb : (equations.body scope.head).1 <;>
      simp_all [Equations.baseRow, Template.instantiate, RowTemplate.wellBound, GraphRow.map]
  · intro scope slot
    simp [Equations.baseRow]
  · intro o i k
    simp [Equations.baseRow, Label.view, Label.familyVar]
  · intro ps' valid
    simp [Equations.baseRow, Label.view]

/-- A label that is not a meet has its base row. -/
theorem Equations.row_nonmeet (equations : Equations) (q : Label equations.signature)
    (h : q.1.isMeet = false) : equations.row q = equations.baseRow q := by
  rcases q with ⟨t, valid⟩
  cases t
  case argument => simp [Tree.scoped] at valid
  case «local» => simp [Tree.scoped] at valid
  all_goals simp_all [Equations.row, Label.view, Tree.isMeet]

theorem Equations.partRow_nonmeet (equations : Equations) (q : Label equations.signature)
    (h : q.1.isMeet = false) : equations.graph.partRow q = true := by
  have hn := equations.baseRow_ne_meet q
  simp only [NormalGraph.partRow, Bool.or_eq_true, Option.isNone_iff_eq_none]
  right
  simp only [Equations.graph, NormalGraph.ofRowMap, equations.row_nonmeet q h]
  cases hb : equations.baseRow q with
  | meet p cs ps => exact absurd hb (hn p cs ps)
  | _ => rfl

/-- A label whose row is a clause row means those clauses. -/
theorem Equations.graph_clauses (equations : Equations) {i : Label equations.signature}
    {cs : List (Clause (List (Label equations.signature)))} (h : equations.row i = .clauses cs) :
    equations.graph.plain i = true ∧ equations.graph i = cs := by
  have hp : equations.graph.plain i = true := by
    simp [NormalGraph.plain, NormalGraph.params, Equations.graph, NormalGraph.ofRowMap, h]
  refine ⟨hp, ?_⟩
  show NormalGraph.clauses _ i = cs
  simp only [NormalGraph.clauses, hp, if_true]
  simp [Equations.graph, NormalGraph.ofRowMap, h, GraphRow.union]

/-- A part of a meet means what its base row says, read at the same level: a
clause part its clauses, any other part as the step reads a part. -/
theorem Equations.part_iff (equations : Equations) (η : MixedAssignment (Label equations.signature))
    (q : Label equations.signature) (h : q.1.isMeet = false) {n W v} :
    qDenoteWithArgs equations.graph (mixedParameters equations.graph) (η, q) n W v ↔
      partCase (fun q => partSemWithArgs equations.graph (mixedParameters equations.graph)
          (qDenoteWithArgs equations.graph (mixedParameters equations.graph)) η q n W v)
        (fun cs => setSem (mixedSem equations.graph η) cs n W v) (q, equations.baseRow q) := by
  have hrow := equations.row_nonmeet q h
  cases hb : equations.baseRow q with
  | clauses cs =>
    obtain ⟨hplain, hG⟩ := equations.graph_clauses (hrow.trans hb)
    rw [mixed_unfold_plain η hplain, hG]
    rfl
  | _ => exact part_denote (equations.partRow_nonmeet q h)

/-- The normalized conjunction of clause lists means the intersection, among
values. -/
theorem setSem_meetAll (G : NormalGraph ι) (Z X : List ι → Fam) (P : List ι → ArgFam)
    (Cs : List (List (Clause (List ι)))) (n : Nat) (W : WorldT n) (v : Val) :
    setSem (rowSem G Z X P) (meetAll Cs) n W v ↔
      (isVal v = true ∧ Scoped 0 v) ∧ ∀ C ∈ Cs, setSem (rowSem G Z X P) C n W v := by
  induction Cs with
  | nil =>
    simp only [meetAll, List.not_mem_nil, false_implies, implies_true, and_true]
    constructor
    · rintro ⟨c, hc, hv, _⟩
      cases List.mem_singleton.mp hc
      exact hv
    · intro hv
      exact ⟨.top, List.mem_singleton_self _, hv, builtinInvariant_of_withoutInvariant rfl n W v⟩
  | cons C rest ih =>
    rw [meetAll, meetLists_row, ih, List.forall_mem_cons]
    constructor
    · rintro ⟨hC, hv, hr⟩; exact ⟨hv, hC, hr⟩
    · rintro ⟨hv, hC, hr⟩; exact ⟨hC, hv, hr⟩

/-- Argument-list clauses hold no value: leaving them out keeps a row's
values. -/
theorem setSem_filter_value (G : NormalGraph ι) (Z X : List ι → Fam) (P : List ι → ArgFam)
    (L : List (Clause (List ι))) (n : Nat) (W : WorldT n) (v : Val) :
    setSem (rowSem G Z X P) (L.filter Clause.isValue) n W v ↔ setSem (rowSem G Z X P) L n W v := by
  constructor
  · rintro ⟨c, hc, hv⟩
    exact ⟨c, (List.mem_filter.mp hc).1, hv⟩
  · rintro ⟨c, hc, hv⟩
    refine ⟨c, List.mem_filter.mpr ⟨hc, ?_⟩, hv⟩
    cases c <;> simp_all [Clause.isValue, rowSem, semWithArgs]

private theorem meet_row (equations : Equations) (ps : Types)
    (valid : (Tree.meet ps).scoped equations.signature 0 0 = true) :
    equations.row ⟨.meet ps, valid⟩ =
      meetRowOf ((ps.labels (Bool.and_eq_true_iff.mp valid).1).map
        fun q => (q, equations.baseRow q)) := rfl

private theorem meet_flat (ps : Types) (valid : (Tree.meet ps).scoped sig 0 0 = true)
    (q : Label sig) (hq : q ∈ ps.labels (Bool.and_eq_true_iff.mp valid).1) : q.1.isMeet = false := by
  have h := (Bool.and_eq_true_iff.mp valid).2
  simp only [List.all_eq_true, Bool.not_eq_true'] at h
  exact h q.1 (Types.mem_labels.mp hq)

/-- **A meet label means the intersection of its parts' values**, at every
level and assignment. -/
theorem Equations.meet_denote (equations : Equations)
    (η : MixedAssignment (Label equations.signature)) (ps : Types)
    (valid : (Tree.meet ps).scoped equations.signature 0 0 = true) {n W v} :
    qDenoteWithArgs equations.graph (mixedParameters equations.graph) (η, ⟨.meet ps, valid⟩) n W v ↔
      (isVal v = true ∧ Scoped 0 v) ∧ ∀ q ∈ ps.labels (Bool.and_eq_true_iff.mp valid).1,
        qDenoteWithArgs equations.graph (mixedParameters equations.graph) (η, q) n W v := by
  let parts := ps.labels (Bool.and_eq_true_iff.mp valid).1
  let rows := parts.map fun q => (q, equations.baseRow q)
  have hparts : (∀ q ∈ parts,
      qDenoteWithArgs equations.graph (mixedParameters equations.graph) (η, q) n W v) ↔
      (∀ q ∈ meetRigid rows, partSemWithArgs equations.graph (mixedParameters equations.graph)
          (qDenoteWithArgs equations.graph (mixedParameters equations.graph)) η q n W v) ∧
        ∀ C ∈ meetClauseLists rows, setSem (mixedSem equations.graph η) C n W v := by
    rw [meet_partition]
    simp only [rows, List.forall_mem_map]
    exact forall₂_congr fun q hq => equations.part_iff η q (meet_flat ps valid q hq) (n := n) (W := W) (v := v)
  change _ ↔ _ ∧ ∀ q ∈ parts, _
  rw [hparts]
  have hrow := meet_row equations ps valid
  cases hr : meetRigid rows with
  | nil =>
    have hrow' : equations.row ⟨.meet ps, valid⟩ =
        .clauses ((meetAll ((meetClauseLists rows).eraseDups)).filter Clause.isValue) := by
      rw [hrow]; simp only [meetRowOf]; rw [hr]
    obtain ⟨hplain, hG⟩ := equations.graph_clauses hrow'
    rw [mixed_unfold_plain η hplain, hG, setSem_filter_value, setSem_meetAll]
    simp
  | cons p rs =>
    have hrow' : equations.row ⟨.meet ps, valid⟩ = .meet p (meetAll ((meetClauseLists rows).eraseDups)) rs := by
      rw [hrow]; simp only [meetRowOf]; rw [hr]
    have hm : equations.graph.meetRow ⟨.meet ps, valid⟩ = true := by
      simp [NormalGraph.meetRow, NormalGraph.params, Equations.graph, NormalGraph.ofRowMap, hrow']
    rw [meet_row_iff hm]
    have hparts' : meetParts equations.graph ⟨.meet ps, valid⟩ = p :: rs := by
      simp [meetParts, Equations.graph, NormalGraph.ofRowMap, hrow']
    have hcl : meetClauses equations.graph ⟨.meet ps, valid⟩ = meetAll ((meetClauseLists rows).eraseDups) := by
      simp [meetClauses, Equations.graph, NormalGraph.ofRowMap, hrow']
    rw [hparts', hcl]
    have hs := setSem_meetAll equations.graph (builtinValues equations.graph)
      (mixedValues equations.graph η) (mixedArgs equations.graph η) ((meetClauseLists rows).eraseDups) n W v
    change _ ∧ setSem (mixedSem equations.graph η) _ n W v ↔ _
    rw [hs]
    simp only [List.mem_eraseDups]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
    · rintro ⟨h2, h1, h3⟩; exact ⟨h1, h2, h3⟩

/-- A meet label's row is no scheme and no parameter. -/
theorem Equations.meet_rigid (equations : Equations) (ps : Types)
    (valid : (Tree.meet ps).scoped equations.signature 0 0 = true) :
    equations.graph.schemes ⟨.meet ps, valid⟩ = none ∧
      equations.graph.parameterKinds ⟨.meet ps, valid⟩ = none := by
  have hrow := meet_row equations ps valid
  cases hr : meetRigid ((ps.labels (Bool.and_eq_true_iff.mp valid).1).map
      fun q => (q, equations.baseRow q)) with
  | nil =>
    rw [meetRowOf, hr] at hrow
    simp [Equations.graph, NormalGraph.ofRowMap, hrow]
  | cons p rs =>
    rw [meetRowOf, hr] at hrow
    simp [Equations.graph, NormalGraph.ofRowMap, hrow]

/-- A meet label admits no argument list. -/
theorem Equations.meet_noArguments (equations : Equations)
    (η : MixedAssignment (Label equations.signature)) (ps : Types)
    (valid : (Tree.meet ps).scoped equations.signature 0 0 = true) {n W vs} :
    ¬ mixedMeaning equations.graph η [⟨.meet ps, valid⟩] n W (.inr vs) := by
  let rows := (ps.labels (Bool.and_eq_true_iff.mp valid).1).map fun q => (q, equations.baseRow q)
  have hrow := meet_row equations ps valid
  rintro ⟨i, hi, h⟩
  cases List.mem_singleton.mp hi
  cases hr : meetRigid rows with
  | nil =>
    have hrow' : equations.row ⟨.meet ps, valid⟩ =
        .clauses ((meetAll ((meetClauseLists rows).eraseDups)).filter Clause.isValue) := by
      rw [hrow]; simp only [meetRowOf]; rw [hr]
    simp only [Equations.graph, NormalGraph.ofRowMap, hrow',
      NormalGraph.clauses, NormalGraph.plain, NormalGraph.params, GraphRow.union, NormalGraph.listParam] at h
    obtain ⟨c, hc, h⟩ := h
    simp only [Option.isSome_none, Bool.not_false, Option.isNone_none, Bool.and_self, ite_true,
      List.mem_filter] at hc
    cases c <;> simp_all [Clause.isValue, clauseArguments]
  | cons p rs =>
    have hrow' : equations.row ⟨.meet ps, valid⟩ = .meet p (meetAll ((meetClauseLists rows).eraseDups)) rs := by
      rw [hrow]; simp only [meetRowOf]; rw [hr]
    simp [Equations.graph, NormalGraph.ofRowMap, hrow', NormalGraph.clauses, NormalGraph.plain,
      NormalGraph.params, NormalGraph.listParam] at h

theorem mixedMeaning_single_value (G : NormalGraph ι) (η : MixedAssignment ι) (i : ι)
    {n W v} : mixedMeaning G η [i] n W (.inl v) ↔ qDenoteWithArgs G (mixedParameters G) (η, i) n W v := by
  simp [mixedMeaning, mixedParameters, setSem]

/-- **A canonical meet means the intersection of its operands' values**:
flattening nested meets, sorting and deduplicating keep the intersection. -/
theorem Equations.meetOf_denote (equations : Equations)
    (η : MixedAssignment (Label equations.signature)) (c : List (Label equations.signature)) {n W v} :
    qDenoteWithArgs equations.graph (mixedParameters equations.graph) (η, Label.meetOf c) n W v ↔
      (isVal v = true ∧ Scoped 0 v) ∧ ∀ L ∈ c,
        qDenoteWithArgs equations.graph (mixedParameters equations.graph) (η, L) n W v := by
  let D := fun L => qDenoteWithArgs equations.graph (mixedParameters equations.graph) (η, L) n W v
  refine Iff.trans (equations.meet_denote η _ (Label.meetOf c).2) (and_congr_right fun hv => ?_)
  constructor
  · intro h L hL
    rcases L with ⟨t, vt⟩
    cases t with
    | meet ps' =>
      refine (equations.meet_denote η ps' vt).mpr ⟨hv, fun q hq => h q ?_⟩
      rw [Types.mem_labels, Types.toList_ofList, List.mem_eraseDups, List.mem_mergeSort]
      exact List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨_, hL, rfl⟩, Types.mem_labels.mp hq⟩
    | _ =>
      refine h _ ?_
      rw [Types.mem_labels, Types.toList_ofList, List.mem_eraseDups, List.mem_mergeSort]
      exact List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨_, hL, rfl⟩, by simp [Tree.meetParts]⟩
  · intro h q hq
    rw [Types.mem_labels, Types.toList_ofList, List.mem_eraseDups, List.mem_mergeSort] at hq
    obtain ⟨_, hL, hu⟩ := List.mem_flatMap.mp hq
    obtain ⟨L, hLc, rfl⟩ := List.mem_map.mp hL
    rcases L with ⟨t, vt⟩
    have hD := h _ hLc
    cases t with
    | meet ps' =>
      exact ((equations.meet_denote η ps' vt).mp hD).2 q (Types.mem_labels.mpr hu)
    | _ =>
      simp only [Tree.meetParts, List.mem_singleton] at hu
      have : q = ⟨_, vt⟩ := Subtype.ext hu
      subst this
      exact hD

/-- **Distribution.** The meets of every choice of a label from each union
mean the intersection of the unions' values. -/
theorem Equations.distribute_values (equations : Equations)
    (η : MixedAssignment (Label equations.signature)) (As : List (List (Label equations.signature)))
    {n W v} :
    mixedValues equations.graph η ((choices As).map Label.meetOf) n W v ↔
      (isVal v = true ∧ Scoped 0 v) ∧ ∀ A ∈ As, mixedValues equations.graph η A n W v := by
  simp only [mixedValues, setSem, List.mem_map]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, h⟩
    obtain ⟨hv, h⟩ := (equations.meetOf_denote η c).mp h
    exact ⟨hv, exists_choice.mp ⟨c, hc, h⟩⟩
  · rintro ⟨hv, h⟩
    obtain ⟨c, hc, h⟩ := exists_choice.mpr h
    exact ⟨_, ⟨c, hc, rfl⟩, (equations.meetOf_denote η c).mpr ⟨hv, h⟩⟩

/-- Distributed meets admit no argument list. -/
theorem Equations.distribute_noArguments (equations : Equations)
    (η : MixedAssignment (Label equations.signature)) (As : List (List (Label equations.signature)))
    {n W vs} : ¬ mixedMeaning equations.graph η ((choices As).map Label.meetOf) n W (.inr vs) := by
  intro h
  obtain ⟨i, hi, h⟩ := (mixedMeaning_union _ _ _ n W _).mp h
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hi
  exact equations.meet_noArguments η _ (Label.meetOf c).2 h

/-- Distributed meets mean the intersection of the unions, as a whole: values
in each union, and no argument list. -/
theorem Equations.distribute_meaning (equations : Equations)
    (η θ : MixedAssignment (Label equations.signature))
    (As Bs : List (List (Label equations.signature))) (hlen : As.length = Bs.length) {n : Nat}
    (h : ∀ i (ha : i < As.length) (hb : i < Bs.length) m, m < n → ∀ W v,
      mixedValues equations.graph η As[i] m W v ↔ mixedValues equations.graph θ Bs[i] m W v) :
    Agree (mixedMeaning equations.graph η ((choices As).map Label.meetOf))
      (mixedMeaning equations.graph θ ((choices Bs).map Label.meetOf)) n := by
  intro m hm W x
  cases x with
  | inr vs =>
    exact iff_of_false (equations.distribute_noArguments η As) (equations.distribute_noArguments θ Bs)
  | inl v =>
    change mixedValues _ η _ m W v ↔ mixedValues _ θ _ m W v
    rw [equations.distribute_values, equations.distribute_values]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hA B hB
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
      exact (h i (by omega) hi m hm W v).mp (hA _ (List.getElem_mem (by omega)))
    · intro hB A hA
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
      exact (h i hi (by omega) m hm W v).mpr (hB _ (List.getElem_mem (by omega)))

#print axioms Equations.meet_denote
#print axioms Equations.meet_noArguments
#print axioms Equations.meetOf_denote
#print axioms Equations.distribute_values
#print axioms Equations.distribute_meaning

end Verification.EquationGraphs
