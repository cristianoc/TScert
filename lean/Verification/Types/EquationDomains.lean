import Verification.Types.EquationFamilies
-- QualifiedTemplateEmbedding.lean embeds an ordinary template into a graph with qualified rows; without it domain installation cannot preserve the template's meaning.
import Verification.Types.QualifiedTemplateEmbedding

namespace Verification.EquationGraphs
open PositiveGraphs PositiveNormalization PositiveRules CallEffects QualifiedTemplateEmbedding

mutual
/-- Declaration heads referenced by finite type syntax, including owners of
bound parameters. -/
def Tree.dependencyHeads : Tree → List Nat
  | .app h args | .bound h args _ => h :: args.dependencyHeads
  | .argument _ | .local _ | .var .. => []
  | .meet parts => parts.dependencyHeads
def Types.dependencyHeads : Types → List Nat
  | .nil => []
  | .cons t ts => t.dependencyHeads ++ ts.dependencyHeads
def Args.dependencyHeads : Args → List Nat
  | .nil => []
  | .cons ts args => ts.dependencyHeads ++ args.dependencyHeads
end

@[simp] theorem Types.dependencyHeads_ofList (ts : List Tree) :
    (Types.ofList ts).dependencyHeads = ts.flatMap Tree.dependencyHeads := by
  induction ts <;> simp_all [Types.ofList, Types.dependencyHeads]

@[simp] theorem Args.dependencyHeads_ofList (ts : List Types) :
    (Args.ofList ts).dependencyHeads = ts.flatMap Types.dependencyHeads := by
  induction ts <;> simp_all [Args.ofList, Args.dependencyHeads]

@[simp] theorem Types.dependencyHeads_append (xs ys : Types) :
    (xs.append ys).dependencyHeads = xs.dependencyHeads ++ ys.dependencyHeads := by
  cases xs with
  | nil => rfl
  | cons t ts => simp [Types.append, Types.dependencyHeads, dependencyHeads_append ts ys, List.append_assoc]

theorem Types.dependencyHeads_of_mem : ∀ {ts : Types} {t : Tree},
    t ∈ ts.toList → ∀ h ∈ t.dependencyHeads, h ∈ ts.dependencyHeads
  | .nil, _, hm => by simp at hm
  | .cons t ts, u, hm => by
    intro h hh
    simp only [Types.toList_cons, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact List.mem_append_left _ hh
    · exact List.mem_append_right _ (Types.dependencyHeads_of_mem hm h hh)

theorem Tree.dependencyHeads_canonMeet {ts : List Tree} {h : Nat}
    (hh : h ∈ (canonMeet ts).dependencyHeads) : ∃ t ∈ ts, h ∈ t.dependencyHeads := by
  simp only [canonMeet, Tree.dependencyHeads, Types.dependencyHeads_ofList,
    List.mem_flatMap, List.mem_eraseDups, List.mem_mergeSort] at hh
  obtain ⟨u, ⟨t, ht, hu⟩, hh⟩ := hh
  refine ⟨t, ht, ?_⟩
  cases t with
  | meet ps => exact Types.dependencyHeads_of_mem hu h hh
  | _ =>
    simp only [Tree.meetParts, List.mem_singleton] at hu
    subst hu
    exact hh

theorem Types.labels_heads (ts : Types) (valid : ts.scoped sig 0 0 = true)
    (l : Label sig) (hl : l ∈ ts.labels valid) (h : Nat) (hh : h ∈ l.1.dependencyHeads) :
    h ∈ ts.dependencyHeads := by
  rw [← Types.labels_val ts valid, Types.dependencyHeads_ofList, List.flatMap_map]
  exact List.mem_flatMap.mpr ⟨l,hl,hh⟩

/-- The application's owner and its captured arguments use only these heads. -/
def Scope.within (scope : Scope sig) (H : Nat → Prop) : Prop :=
  H scope.head.val ∧ ∀ h ∈ scope.rawArgs.dependencyHeads, H h

private theorem Scope.argument_heads (scope : Scope sig) (i : Nat)
    (hi : i < scope.arguments.length) (h : Nat)
    (hh : h ∈ (Types.ofList (scope.arguments[i].map Subtype.val)).dependencyHeads) :
    h ∈ scope.rawArgs.dependencyHeads := by
  simp only [Scope.rawArgs, Args.dependencyHeads_ofList, List.flatMap_map]
  exact List.mem_flatMap.mpr ⟨scope.arguments[i], List.getElem_mem hi, hh⟩

mutual
/-- Instantiation introduces only heads in the template or its application. -/
theorem Tree.instantiate_heads (scope : Scope sig) (H : Nat → Prop)
    (hs : scope.within H) (t : Tree)
    (valid : t.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (ht : ∀ h ∈ t.dependencyHeads, H h) (h : Nat)
    (hh : h ∈ (Tree.instantiate scope t valid).1.dependencyHeads) : H h := by
  cases t with
  | app g args =>
    simp only [Tree.instantiate, Types.dependencyHeads, Tree.dependencyHeads, List.append_nil, List.mem_cons] at hh
    rcases hh with rfl | hh
    · exact ht h (by simp [Tree.dependencyHeads])
    · exact Args.instantiate_heads scope H hs args _
        (fun j hj => ht j (List.mem_cons_of_mem _ hj)) h hh
  | bound g args slot =>
    simp only [Tree.instantiate, Types.dependencyHeads, Tree.dependencyHeads, List.append_nil, List.mem_cons] at hh
    rcases hh with rfl | hh
    · exact ht h (by simp [Tree.dependencyHeads])
    · exact Args.instantiate_heads scope H hs args _
        (fun j hj => ht j (List.mem_cons_of_mem _ hj)) h hh
  | argument i => exact hs.2 h (scope.argument_heads i _ h hh)
  | «local» i =>
    simp only [Tree.instantiate, Types.dependencyHeads, Tree.dependencyHeads, Scope.bound,
      List.append_nil, List.mem_cons] at hh
    exact hh.elim (fun e => e ▸ hs.1) (hs.2 h)
  | var o i k => simp [Tree.instantiate, Types.dependencyHeads, Tree.dependencyHeads] at hh
  | meet ps =>
    simp only [Tree.instantiate, Types.dependencyHeads_ofList, List.map_map,
      List.mem_flatMap, List.mem_map, Function.comp_def] at hh
    obtain ⟨_, ⟨c,hc,rfl⟩,hh⟩ := hh
    obtain ⟨u,hu,hhu⟩ := Tree.dependencyHeads_canonMeet hh
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hu
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hl
    have hlen := (mem_choices.mp hc).1
    exact Types.instantiateParts_heads scope H hs ps _ ht _
      (List.getElem_mem (by omega)) _ ((mem_choices.mp hc).2 i hi (by omega)) h hhu

theorem Types.instantiateParts_heads (scope : Scope sig) (H : Nat → Prop)
    (hs : scope.within H) (ts : Types)
    (valid : ts.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (ht : ∀ h ∈ ts.dependencyHeads, H h) (A : List (Label sig))
    (hA : A ∈ Types.instantiateParts scope ts valid) (l : Label sig) (hl : l ∈ A)
    (h : Nat) (hh : h ∈ l.1.dependencyHeads) : H h := by
  cases ts with
  | nil => simp [Types.instantiateParts] at hA
  | cons t ts =>
    simp only [Types.instantiateParts, List.mem_cons] at hA
    rcases hA with rfl | hA
    · exact Tree.instantiate_heads scope H hs t _
        (fun j hj => ht j (List.mem_append_left _ hj)) h (Types.labels_heads _ _ l hl h hh)
    · exact Types.instantiateParts_heads scope H hs ts _
        (fun j hj => ht j (List.mem_append_right _ hj)) A hA l hl h hh

theorem Types.instantiate_heads (scope : Scope sig) (H : Nat → Prop)
    (hs : scope.within H) (ts : Types)
    (valid : ts.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (ht : ∀ h ∈ ts.dependencyHeads, H h) (h : Nat)
    (hh : h ∈ (Types.instantiate scope ts valid).1.dependencyHeads) : H h := by
  cases ts with
  | nil => simp [Types.instantiate, Types.dependencyHeads] at hh
  | cons t ts =>
    simp only [Types.instantiate, Types.dependencyHeads_append, List.mem_append] at hh
    rcases hh with hh | hh
    · exact Tree.instantiate_heads scope H hs t _
        (fun j hj => ht j (List.mem_append_left _ hj)) h hh
    · exact Types.instantiate_heads scope H hs ts _
        (fun j hj => ht j (List.mem_append_right _ hj)) h hh

theorem Args.instantiate_heads (scope : Scope sig) (H : Nat → Prop)
    (hs : scope.within H) (args : Args)
    (valid : args.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (ht : ∀ h ∈ args.dependencyHeads, H h) (h : Nat)
    (hh : h ∈ (Args.instantiate scope args valid).1.dependencyHeads) : H h := by
  cases args with
  | nil => simp [Args.instantiate, Args.dependencyHeads] at hh
  | cons ts args =>
    rcases List.mem_append.mp hh with hh | hh
    · exact Types.instantiate_heads scope H hs ts _
        (fun j hj => ht j (List.mem_append_left _ hj)) h hh
    · exact Args.instantiate_heads scope H hs args _
        (fun j hj => ht j (List.mem_append_right _ hj)) h hh
end

#print axioms Tree.instantiate_heads

/-- A label whose finite syntax names only the selected heads. -/
def Label.withinHeads (H : Nat → Prop) (l : Label sig) : Prop :=
  ∀ h ∈ l.1.dependencyHeads, H h

instance (H : Nat → Prop) [DecidablePred H] (l : Label sig) :
    Decidable (l.withinHeads H) := inferInstanceAs (Decidable (∀ h ∈ l.1.dependencyHeads, H h))

/-- A finite template's dependencies include references and binding positions. -/
def Equations.templateDependencies (E : Equations) (h : Fin E.signature.length) : List Nat :=
  (E.rawBody h).operands.flatten.flatMap Tree.dependencyHeads

/-- Every template reached from the selected heads stays inside the selection. -/
def Equations.ClosedHeads (E : Equations) (H : Nat → Prop) : Prop :=
  ∀ h : Fin E.signature.length, H h.val → ∀ g ∈ E.templateDependencies h, H g

instance (E : Equations) (H : Nat → Prop) [DecidablePred H] :
    Decidable (E.ClosedHeads H) := inferInstanceAs
      (Decidable (∀ h : Fin E.signature.length, H h.val → ∀ g ∈ E.templateDependencies h, H g))

private theorem expressions_within (scope : Scope sig) (H : Nat → Prop)
    (hs : scope.within H) (es : List (Expression sig sig[scope.head]))
    (he : ∀ e ∈ es, ∀ h ∈ e.1.dependencyHeads, H h) :
    ∀ l ∈ es.flatMap (Expression.instantiate scope), l.withinHeads H := by
  intro l hl h hh
  obtain ⟨e,he',hl⟩ := List.mem_flatMap.mp hl
  exact Tree.instantiate_heads scope H hs e.1 e.2.1 (he e he') h
    (Types.labels_heads _ _ l hl h hh)

private theorem reference_within (scope : Scope sig) (H : Nat → Prop)
    (hs : scope.within H) (r : Reference sig sig[scope.head])
    (hr : ∀ h ∈ r.1.1.dependencyHeads, H h) :
    (r.instantiate scope).withinHeads H := by
  apply expressions_within scope H hs [r.1]
    (by intro e he; simpa using List.mem_singleton.mp he ▸ hr)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact List.getElem_mem _

private theorem Template.instantiate_within (E : Equations) (H : Nat → Prop)
    (closed : E.ClosedHeads H) (scope : Scope E.signature) (hs : scope.within H) :
    ∀ S ∈ ((E.body scope.head).instantiate scope).operands,
      ∀ l ∈ S, l.withinHeads H := by
  have deps := closed scope.head hs.1
  unfold Equations.templateDependencies Equations.rawBody at deps
  have raw : ∀ S ∈ ((E.body scope.head).1.map (fun r => r.1.1) (List.map Subtype.val)).operands,
      ∀ t ∈ S, ∀ h ∈ t.dependencyHeads, H h := by
    intro S hS t ht h hh
    exact deps h (List.mem_flatMap.mpr ⟨t,List.mem_flatten.mpr ⟨S,hS,ht⟩,hh⟩)
  cases hb : (E.body scope.head).1 with
  | clauses cs =>
    simp only [Template.instantiate, hb, GraphRow.map, GraphRow.operands,
      List.forall_mem_flatMap, List.forall_mem_map, clause_operands_map] at raw ⊢
    intro c hc S hS
    simpa only [List.forall_mem_flatMap] using expressions_within scope H hs S (raw c hc S hS)
  | scheme bs sigs bounds rests resolution =>
    simp only [Template.instantiate, hb, GraphRow.map, GraphRow.operands,
      List.forall_mem_cons, List.forall_mem_append, List.forall_mem_flatMap,
      List.forall_mem_map] at raw ⊢
    refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
    · intro b hb
      exact reference_within scope H hs b (raw.1.1.1 b hb)
    · intro a ha
      simp only [Arrow.map, Contract.map, Arrow.operands, List.forall_mem_cons,
        List.forall_mem_append, List.forall_mem_map] at raw ⊢
      exact ⟨⟨expressions_within scope H hs _ (raw.1.1.2 a ha).1.1,
        fun S hS => expressions_within scope H hs S ((raw.1.1.2 a ha).1.2 S hS)⟩,
        expressions_within scope H hs _ (raw.1.1.2 a ha).2.1, by simp⟩
    · intro b hb
      refine ⟨reference_within scope H hs b.1 (raw.1.2 b hb).1, ?_⟩
      simpa only [List.forall_mem_flatMap] using expressions_within scope H hs b.2 (raw.1.2 b hb).2
    · intro a ha
      simp only [RestArrow.map, RestArrow.mapWith, Contract.map, RestArrow.operands,
        List.forall_mem_cons, List.forall_mem_append, List.forall_mem_map] at raw ⊢
      exact ⟨⟨expressions_within scope H hs _ (raw.2 a ha).1.1,
        fun S hS => expressions_within scope H hs S ((raw.2 a ha).1.2 S hS)⟩,
        expressions_within scope H hs _ (raw.2 a ha).2.1,
        expressions_within scope H hs _ (raw.2 a ha).2.2.1, by simp⟩
  | param b name kind => simp [Template.instantiate, hb, GraphRow.map, GraphRow.operands]
  | meet b cs bs =>
    have valid := (E.body scope.head).2
    simp [hb, RowTemplate.wellBound] at valid

private theorem Equations.baseRow_within (E : Equations) (H : Nat → Prop)
    (closed : E.ClosedHeads H) (l : Label E.signature) (hl : l.withinHeads H) :
    ∀ S ∈ (E.baseRow l).operands, ∀ q ∈ S, q.withinHeads H := by
  revert hl
  apply l.cases
  · intro scope hl
    have hs : scope.within H := by
      simpa [Label.withinHeads, Scope.label, Tree.dependencyHeads, List.forall_mem_cons,
        Scope.within] using hl
    simpa [Equations.baseRow] using Template.instantiate_within E H closed scope hs
  · intro scope slot _
    simp [Equations.baseRow, GraphRow.operands]
  · intro owner slot kind _
    simp [Equations.baseRow, GraphRow.operands]
  · intro ps valid _
    simp [Equations.baseRow, Label.view, GraphRow.operands]

private theorem meetRowOf_within [DecidableEq ι] (P : ι → Prop) (rows : List (ι × GraphRow ι))
    (hr : ∀ x ∈ rows, P x.1 ∧ ∀ S ∈ x.2.operands, ∀ q ∈ S, P q) :
    ∀ S ∈ (meetRowOf rows).operands, ∀ q ∈ S, P q := by
  have rigid : ∀ q ∈ meetRigid rows, P q := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := mem_meetRigid hq
    exact (hr x hx).1
  have clauses : ∀ c ∈ meetAll ((meetClauseLists rows).eraseDups), ∀ S ∈ c.operands, ∀ q ∈ S, P q := by
    intro c hc S hS q hq
    obtain ⟨C,hC,d,hd,hSd⟩ := meetAll_operands hc hS
    obtain ⟨⟨l,r⟩,hrow,he⟩ := mem_meetClauseLists (List.mem_eraseDups.mp hC)
    have hclosed := (hr (l,r) hrow).2
    rw [he] at hclosed
    exact hclosed S (by simpa [GraphRow.operands] using List.mem_flatMap.mpr ⟨d,hd,hSd⟩) q hq
  unfold meetRowOf
  cases he : meetRigid rows with
  | nil =>
    intro S hS q hq
    obtain ⟨c,hc,hSc⟩ := List.mem_flatMap.mp hS
    exact clauses c (List.mem_filter.mp hc).1 S hSc q hq
  | cons p ps =>
    simp only [GraphRow.operands, List.forall_mem_cons, List.forall_mem_flatMap]
    exact ⟨⟨rigid p (he ▸ List.mem_cons_self),
      fun q hq => rigid q (he ▸ List.mem_cons_of_mem _ hq)⟩, clauses⟩

theorem Equations.row_within (E : Equations) (H : Nat → Prop)
    (closed : E.ClosedHeads H) (l : Label E.signature) (hl : l.withinHeads H) :
    ∀ S ∈ (E.row l).operands, ∀ q ∈ S, q.withinHeads H := by
  revert hl
  apply l.cases
  · intro scope hl
    exact E.baseRow_within H closed scope.label hl
  · intro scope slot hl
    exact E.baseRow_within H closed (scope.bound slot) hl
  · intro owner slot kind hl
    exact E.baseRow_within H closed (Label.familyVar owner slot kind) hl
  · intro ps valid hl
    change ∀ S ∈ (meetRowOf ((ps.labels (Bool.and_eq_true_iff.mp valid).1).map
      fun q => (q,E.baseRow q))).operands, ∀ q ∈ S, q.withinHeads H
    apply meetRowOf_within
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    have hq' : q.withinHeads H := fun h hh =>
      hl h (Types.labels_heads ps _ q hq h hh)
    exact ⟨hq',E.baseRow_within H closed q hq'⟩

theorem Equations.dependencies_within (E : Equations) (H : Nat → Prop)
    (closed : E.ClosedHeads H) (l : Label E.signature) (hl : l.withinHeads H) :
    (∀ q ∈ reads E.graph l, q.withinHeads H) ∧
      (∀ q ∈ meetParts E.graph l, q.withinHeads H) := by
  have hr := E.row_within H closed l hl
  cases hrow : E.row l <;>
    simp [reads, meetParts, Equations.graph, NormalGraph.ofRowMap, NormalGraph.clauses,
      NormalGraph.plain, NormalGraph.params, hrow, GraphRow.union, meetClauses,
      GraphRow.operands, List.mem_flatMap, List.mem_flatten] at hr ⊢ <;> grind

/-- Only templates in the dependency closure must have ordinary quantifiers. -/
def Equations.ordinaryTemplate (E : Equations) (h : Fin E.signature.length) : Bool :=
  match (E.body h).1 with
  | .scheme _ _ _ _ resolution _ => resolution.isEmpty
  | _ => true

theorem Equations.scheme_ordinary (E : Equations) (H : Nat → Prop)
    (ordinary : ∀ h : Fin E.signature.length, H h.val → E.ordinaryTemplate h = true)
    (l : Label E.signature) (hl : l.withinHeads H)
    (s : SchemeRow (Label E.signature)) (hs : E.graph.schemes l = some s) : s.resolution = [] := by
  revert hl hs
  apply l.cases
  · intro scope hl hs
    have ho := ordinary scope.head (hl scope.head.val (by simp [Scope.label, Tree.dependencyHeads]))
    unfold Equations.ordinaryTemplate at ho
    cases hb : (E.body scope.head).1 <;>
      simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow,
        Template.instantiate, hb, GraphRow.map] at hs
    rename_i bs sigs bounds rests resolution
    subst s
    simpa [hb] using ho
  · intro scope slot _ hs
    simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow] at hs
  · intro owner slot kind _ hs
    simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow] at hs
  · intro ps valid _ hs
    simp only [Equations.graph, NormalGraph.ofRowMap, Equations.row, Label.view] at hs
    cases hr : meetRigid ((ps.labels (Bool.and_eq_true_iff.mp valid).1).map
      fun q => (q,E.baseRow q)) <;> simp [meetRowOf, hr] at hs

@[simp] theorem Equations.graph_domain (E : Equations)
    (domain : SchemeDomain (Label E.signature) .mixed) :
    ({ E with domain := domain } : Equations).graph = { E.graph with domain := domain } := by
  have base : ({ E with domain := domain } : Equations).baseRow = E.baseRow := by
    funext l
    unfold Equations.baseRow
    cases l.view <;> rfl
  have rows : ({ E with domain := domain } : Equations).row = E.row := by
    funext l
    unfold Equations.row
    rw [base]
    cases l.view <;> rfl
  simp only [Equations.graph, rows, NormalGraph.ofRowMap]

@[simp] theorem Equations.ordinaryTemplate_domain (E : Equations)
    (domain : SchemeDomain (Label E.signature) .mixed) (h : Fin E.signature.length) :
    ({ E with domain := domain } : Equations).ordinaryTemplate h = E.ordinaryTemplate h := by
  unfold Equations.ordinaryTemplate
  cases (E.body h).1 <;> rfl

/-- A checked finite set of heads, with ordinary quantifiers throughout its
dependency closure and the graph's array prototype included. -/
structure OrdinaryRegion (E : Equations) where
  heads : List Nat
  closed : E.ClosedHeads (· ∈ heads)
  ordinary : ∀ h : Fin E.signature.length, h.val ∈ heads → E.ordinaryTemplate h = true
  builtins : ∀ r ∈ E.builtins.toList, ∀ l ∈ r.proto ++ r.unknown, l.withinHeads (· ∈ heads)

/-- Dependency discovery proposes a finite set. The final checks establish
closure, ordinary quantification, the built-ins, and inclusion of every root. -/
def Equations.checkOrdinaryRegion (E : Equations) (roots : List Nat) :
    Option { R : OrdinaryRegion E // ∀ h ∈ roots, h ∈ R.heads } := Id.run do
  let mut heads := (roots ++ E.builtins.toList.flatMap
    (fun r => (r.proto ++ r.unknown).flatMap fun l => l.1.dependencyHeads)).eraseDups
  for _ in [:E.signature.length + 1] do
    let more := (List.finRange E.signature.length).filter (fun h => heads.contains h.val)
      |>.flatMap E.templateDependencies
    let next := (heads ++ more).eraseDups
    if next.length == heads.length then break
    heads := next
  if checked : E.ClosedHeads (· ∈ heads) ∧
      (∀ h : Fin E.signature.length, h.val ∈ heads → E.ordinaryTemplate h = true) ∧
      (∀ r ∈ E.builtins.toList, ∀ l ∈ r.proto ++ r.unknown, l.withinHeads (· ∈ heads)) ∧
      (∀ h ∈ roots, h ∈ heads) then
    return some ⟨⟨heads,checked.1,checked.2.1,checked.2.2.1⟩,checked.2.2.2⟩
  else return none

/-- Descriptor qualification elsewhere in the graph does not affect this
checked ordinary region. -/
theorem OrdinaryRegion.domainRegion (R : OrdinaryRegion E)
    (domain : SchemeDomain (Label E.signature) .mixed) :
    DomainRegion E.graph domain (Label.withinHeads (· ∈ R.heads)) where
  reads i hi := (E.dependencies_within _ R.closed i hi).1
  parts i hi := (E.dependencies_within _ R.closed i hi).2
  builtins r hr j hj := R.builtins r (by
    have hr' : E.builtins = some r := hr
    simp [hr']) j (List.mem_append_left _ hj)
  unknown r hr j hj := R.builtins r (by
    have hr' : E.builtins = some r := hr
    simp [hr']) j (List.mem_append_right _ hj)
  allowed i hi s hs As :=
    let ordinary := E.scheme_ordinary _ R.ordinary i hi s hs
    iff_of_true (domain.ordinary_allowed s As ordinary)
      (E.graph.domain.ordinary_allowed s As ordinary)

theorem OrdinaryRegion.denote (R : OrdinaryRegion E)
    (domain : SchemeDomain (Label E.signature) .mixed)
    (η : MixedAssignment (Label E.signature)) (l : Label E.signature)
    (hl : l.withinHeads (· ∈ R.heads)) :
    qDenoteWithArgs { E.graph with domain := domain }
      (mixedParameters { E.graph with domain := domain }) (η,l) =
      qDenoteWithArgs E.graph (mixedParameters E.graph) (η,l) :=
  (R.domainRegion domain).denote η l hl

#print axioms OrdinaryRegion.denote

end Verification.EquationGraphs
