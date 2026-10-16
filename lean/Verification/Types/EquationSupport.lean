import Verification.Types.EquationMeets

/-! Free-parameter support for equation graphs. These graphs use the same
recursive semantics and support theorem as checked finite tables. -/
namespace Verification.EquationGraphs
open PositiveGraphs PositiveNormalization CallEffects PositiveRules

mutual
private theorem Tree.free_closed (t : Tree) (valid : t.scoped sig 0 0 = true)
    (p : Tree) (hp : p ∈ t.free) : p.scoped sig 0 0 = true := by
  cases t with
  | app h args => exact Args.free_closed args (Bool.and_eq_true_iff.mp valid).2 p hp
  | bound h args i => simpa [Tree.free] using List.mem_singleton.mp hp ▸ valid
  | var o i k => simpa [Tree.free] using List.mem_singleton.mp hp ▸ valid
  | argument i => simp [Tree.free] at hp
  | «local» i => simp [Tree.free] at hp
  | meet ps => exact Types.free_closed ps (Bool.and_eq_true_iff.mp valid).1 p hp
private theorem Types.free_closed (ts : Types) (valid : ts.scoped sig 0 0 = true)
    (p : Tree) (hp : p ∈ ts.free) : p.scoped sig 0 0 = true := by
  cases ts with
  | nil => simp [Types.free] at hp
  | cons t ts =>
    rcases List.mem_append.mp hp with hp | hp
    · exact Tree.free_closed t (Bool.and_eq_true_iff.mp valid).1 p hp
    · exact Types.free_closed ts (Bool.and_eq_true_iff.mp valid).2 p hp
private theorem Args.free_closed (args : Args) (valid : args.scoped sig 0 0 = true)
    (p : Tree) (hp : p ∈ args.free) : p.scoped sig 0 0 = true := by
  cases args with
  | nil => simp [Args.free] at hp
  | cons ts args =>
    rcases List.mem_append.mp hp with hp | hp
    · exact Types.free_closed ts (Bool.and_eq_true_iff.mp valid).1 p hp
    · exact Args.free_closed args (Bool.and_eq_true_iff.mp valid).2 p hp
end

def Label.free (label : Label sig) : List (Label sig) :=
  label.1.free.attach.map fun p => ⟨p.1, Tree.free_closed label.1 label.2 p.1 p.2⟩

@[simp] theorem Label.mem_free {label p : Label sig} : p ∈ label.free ↔ p.1 ∈ label.1.free := by
  simp only [free, List.mem_map, List.mem_attach, true_and]
  constructor
  · rintro ⟨p', rfl⟩; exact p'.2
  · intro hp; exact ⟨⟨p.1, hp⟩, rfl⟩

@[simp] theorem Types.free_ofList (ts : List Tree) : (ofList ts).free = ts.flatMap Tree.free := by
  induction ts <;> simp_all [ofList, free]

@[simp] theorem Args.free_ofList (ts : List Types) : (ofList ts).free = ts.flatMap Types.free := by
  induction ts <;> simp_all [ofList, free]

@[simp] theorem Types.free_append (xs ys : Types) : (xs.append ys).free = xs.free ++ ys.free := by
  cases xs with
  | nil => rfl
  | cons t ts => simp [append, free, free_append ts ys, List.append_assoc]

/-- Support available inside a template: its captured parameters and, only in
signature positions, the locals that this application will quantify. -/
def Scope.supports (scope : Scope sig) (locals : Bool) (p : Tree) : Prop :=
  p ∈ scope.rawArgs.free ∨ locals = true ∧
    ∃ slot : Fin sig[scope.head].binders.length, p = (scope.bound slot).1

private theorem Scope.argument_support (scope : Scope sig) (i : Nat)
    (hi : i < scope.arguments.length) (p : Tree)
    (hp : p ∈ (Types.ofList (scope.arguments[i].map Subtype.val)).free) :
    p ∈ scope.rawArgs.free := by
  simp only [Scope.rawArgs, Args.free_ofList, List.flatMap_map]
  exact List.mem_flatMap.mpr ⟨scope.arguments[i], List.getElem_mem hi, hp⟩

theorem Types.labels_free (ts : Types) (valid : ts.scoped sig 0 0 = true) (L : Label sig)
    (hL : L ∈ ts.labels valid) (p : Tree) (hp : p ∈ L.1.free) : p ∈ ts.free := by
  rw [← Types.labels_val ts valid, Types.free_ofList, List.flatMap_map]
  exact List.mem_flatMap.mpr ⟨L, hL, hp⟩

theorem Types.free_of_mem : ∀ {ts : Types} {t : Tree}, t ∈ ts.toList → ∀ p ∈ t.free, p ∈ ts.free
  | .nil, _, h => by simp at h
  | .cons u ts, t, h => by
    intro p hp
    simp only [Types.toList_cons, List.mem_cons] at h
    simp only [Types.free, List.mem_append]
    rcases h with rfl | h
    · exact .inl hp
    · exact .inr (Types.free_of_mem h p hp)

/-- A canonical meet's free parameters are its operands'. -/
theorem Tree.free_canonMeet {ts : List Tree} {p : Tree} (hp : p ∈ (canonMeet ts).free) :
    ∃ t ∈ ts, p ∈ t.free := by
  simp only [canonMeet, Tree.free, Types.free_ofList, List.mem_flatMap, List.mem_eraseDups, List.mem_mergeSort] at hp
  obtain ⟨u, ⟨t, ht, hu⟩, hp⟩ := hp
  refine ⟨t, ht, ?_⟩
  cases t with
  | meet ps => exact Types.free_of_mem hu p hp
  | _ =>
    simp only [Tree.meetParts, List.mem_singleton] at hu
    subst hu; exact hp

mutual
/-- Instantiation introduces only the parameters explicitly in scope. -/
theorem Tree.instantiate_support (scope : Scope sig) (t : Tree)
    (valid : t.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (lexical : t.lexical locals = true) (p : Tree)
    (hp : p ∈ (Tree.instantiate scope t valid).1.free) : scope.supports locals p := by
  cases t with
  | app h args =>
    apply Args.instantiate_support scope args (Bool.and_eq_true_iff.mp valid).2 lexical p
    simpa [Tree.instantiate, Types.free, Tree.free, Scope.bound] using hp
  | bound h args i => simp [Tree.lexical] at lexical
  | var o i k => simp [Tree.lexical] at lexical
  | argument i =>
    left
    exact scope.argument_support i _ p hp
  | «local» i =>
    right
    refine ⟨lexical, ⟨⟨i, of_decide_eq_true valid⟩, ?_⟩⟩
    simpa [Tree.instantiate, Types.free, Tree.free, Scope.bound] using hp
  | meet ps =>
    simp only [Tree.instantiate, Types.free_ofList, List.map_map, List.mem_flatMap, List.mem_map,
      Function.comp_def] at hp
    obtain ⟨_, ⟨c, hc, rfl⟩, hp⟩ := hp
    obtain ⟨u, hu, hpu⟩ := Tree.free_canonMeet hp
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hu
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
    have hlen := (mem_choices.mp hc).1
    exact Types.instantiateParts_support scope ps _ lexical _ (List.getElem_mem (by omega))
      _ ((mem_choices.mp hc).2 i hi (by omega)) p hpu
theorem Types.instantiateParts_support (scope : Scope sig) (ts : Types)
    (valid : ts.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (lexical : ts.lexical locals = true) (A : List (Label sig))
    (hA : A ∈ Types.instantiateParts scope ts valid) (L : Label sig) (hL : L ∈ A) (p : Tree)
    (hp : p ∈ L.1.free) : scope.supports locals p := by
  cases ts with
  | nil => simp [Types.instantiateParts] at hA
  | cons t ts =>
    simp only [Types.instantiateParts, List.mem_cons] at hA
    rcases hA with rfl | hA
    · exact Tree.instantiate_support scope t _ (Bool.and_eq_true_iff.mp lexical).1 p
        (Types.labels_free _ _ L hL p hp)
    · exact Types.instantiateParts_support scope ts _ (Bool.and_eq_true_iff.mp lexical).2 A hA L hL p hp
theorem Types.instantiate_support (scope : Scope sig) (ts : Types)
    (valid : ts.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (lexical : ts.lexical locals = true) (p : Tree)
    (hp : p ∈ (Types.instantiate scope ts valid).1.free) : scope.supports locals p := by
  cases ts with
  | nil => simp [Types.instantiate, Types.free] at hp
  | cons t ts =>
    simp only [Types.instantiate, Types.free_append, List.mem_append] at hp
    rcases hp with hp | hp
    · exact Tree.instantiate_support scope t (Bool.and_eq_true_iff.mp valid).1
        (Bool.and_eq_true_iff.mp lexical).1 p hp
    · exact Types.instantiate_support scope ts (Bool.and_eq_true_iff.mp valid).2
        (Bool.and_eq_true_iff.mp lexical).2 p hp
theorem Args.instantiate_support (scope : Scope sig) (args : Args)
    (valid : args.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (lexical : args.lexical locals = true) (p : Tree)
    (hp : p ∈ (Args.instantiate scope args valid).1.free) : scope.supports locals p := by
  cases args with
  | nil => simp [Args.instantiate, Args.free] at hp
  | cons ts args =>
    rcases List.mem_append.mp hp with hp | hp
    · exact Types.instantiate_support scope ts (Bool.and_eq_true_iff.mp valid).1
        (Bool.and_eq_true_iff.mp lexical).1 p hp
    · exact Args.instantiate_support scope args (Bool.and_eq_true_iff.mp valid).2
        (Bool.and_eq_true_iff.mp lexical).2 p hp
end

theorem clause_operands_map (f : α → β) (c : Clause α) :
    (c.map f).operands = c.operands.map f := by
  cases c <;> simp [Clause.map, Clause.operands, Tuple.map, Tuple.operands,
    mapFields, OptionalField.map, MethodMembers.Sig.map, MethodMembers.Sig.operands,
    Arrow.map, Arrow.operands, RestArrow.map, RestArrow.mapWith, RestArrow.operands,
    MethodArrow.map, MethodArrow.operands, MethodRestArrow.map,
    MethodRestArrow.mapWith, MethodRestArrow.operands, Contract.map,
    List.map_flatMap, List.flatMap_map, Function.comp_def, Option.toList_map]

private theorem Types.member_free (ts : Types) (valid : ts.scoped sig 0 0 = true)
    (l p : Label sig) (hl : l ∈ ts.labels valid) (hp : p ∈ l.free) : p.1 ∈ ts.free := by
  rw [← Types.labels_val ts valid, Types.free_ofList, List.flatMap_map]
  exact List.mem_flatMap.mpr ⟨l, hl, Label.mem_free.mp hp⟩

private theorem Expression.support (scope : Scope sig) (e : Expression sig sig[scope.head])
    (lexical : e.1.lexical locals = true) {l p : Label sig}
    (hl : l ∈ e.instantiate scope) (hp : p ∈ l.free) : scope.supports locals p.1 :=
  Tree.instantiate_support scope e.1 e.2.1 lexical p.1
    (Types.member_free _ _ l p hl hp)

private theorem expressions_support (scope : Scope sig) (es : List (Expression sig sig[scope.head]))
    (lexical : ∀ e ∈ es, e.1.lexical locals = true) {l p : Label sig}
    (hl : l ∈ es.flatMap (Expression.instantiate scope)) (hp : p ∈ l.free) :
    scope.supports locals p.1 := by
  obtain ⟨e, he, hl⟩ := List.mem_flatMap.mp hl
  exact e.support scope (lexical e he) hl hp

theorem Reference.instantiate_local (scope : Scope sig) (r : Reference sig sig[scope.head])
    (slot : Fin sig[scope.head].binders.length) (hr : r.1.1 = .local slot.val) :
    r.instantiate scope = scope.bound slot := by
  rcases r with ⟨⟨t, hv⟩, hs⟩
  dsimp only at hr
  subst t
  rfl

/-- The checked source order of local references is exactly the canonical
binder order, not merely a set containing the same names. -/
theorem Scope.instantiate_binders (scope : Scope sig) (bs : List (Reference sig sig[scope.head]))
    (hbs : bs.map (fun b => b.1.1) = (List.range sig[scope.head].binders.length).map Tree.local) :
    bs.map (Reference.instantiate scope) = scope.binders := by
  have hlen : bs.length = sig[scope.head].binders.length := by
    simpa using congrArg List.length hbs
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    have hib : i < bs.length := by simpa using hi
    have hin : i < sig[scope.head].binders.length := by simpa [hlen] using hib
    have hget : (bs[i]).1.1 = Tree.local i := by
      have he := congrArg (fun xs : List Tree => xs[i]?) hbs
      simp only [List.getElem?_map] at he
      rw [List.getElem?_eq_getElem hib, List.getElem?_range hin] at he
      exact Option.some.inj he
    simpa [Scope.binders, List.getElem_map, List.getElem_finRange] using
      (bs[i]).instantiate_local scope ⟨i, hin⟩ hget

private theorem clause_reads_support (scope : Scope sig) (cs : List (Clause (List (Expression sig sig[scope.head]))))
    {l p : Label sig}
    (hl : l ∈ (cs.map (Clause.map (fun es => es.flatMap (Expression.instantiate scope)))).flatMap
      (fun c => c.operands.flatten)) (hp : p ∈ l.free) : scope.supports true p.1 := by
  obtain ⟨c', hc', hl⟩ := List.mem_flatMap.mp hl
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  rw [clause_operands_map] at hl
  obtain ⟨es', hes', hl⟩ := List.mem_flatten.mp hl
  obtain ⟨es, hes, rfl⟩ := List.mem_map.mp hes'
  exact expressions_support scope es (fun e _ => e.2.2) hl hp

/-- A row that is not a meet's reads only its label's support. -/
private theorem Equations.row_support (equations : Equations) (label : Label equations.signature)
    (hm : label.1.isMeet = false) :
    (equations.graph.params label = true → label ∈ label.free) ∧
    (∀ l ∈ reads equations.graph label, True ∧ ∀ p ∈ l.free,
      p ∈ label.free ∨ (∃ s, equations.graph.schemes label = some s ∧ p ∈ s.binders)) ∧
    (∀ l ∈ boundReads equations.graph label, ∀ p ∈ l.free, p ∈ label.free) := by
  revert hm
  apply label.cases (P := fun label => label.1.isMeet = false →
    (equations.graph.params label = true → label ∈ label.free) ∧
    (∀ l ∈ reads equations.graph label, True ∧ ∀ p ∈ l.free,
      p ∈ label.free ∨ (∃ s, equations.graph.schemes label = some s ∧ p ∈ s.binders)) ∧
    (∀ l ∈ boundReads equations.graph label, ∀ p ∈ l.free, p ∈ label.free))
  · intro scope _
    have hv := (equations.body scope.head).2
    cases hb : (equations.body scope.head).1 with
    | param p name kind => simp [hb, RowTemplate.wellBound] at hv
    | meet p cs ps => simp [hb, RowTemplate.wellBound] at hv
    | clauses cs =>
      have hlocals : equations.signature[scope.head].binders = [] := by
        simpa [hb, RowTemplate.wellBound] using hv
      simp only [NormalGraph.params, equations.kind_application, Option.isSome_none,
        Bool.false_eq_true, false_implies, true_and]
      constructor
      · intro l hl
        intro p hp
        have hreads : l ∈ (cs.map (Clause.map (fun es => es.flatMap (Expression.instantiate scope)))).flatMap
            (fun c => c.operands.flatten) := by
          simpa [reads, Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Template.instantiate,
            hb, GraphRow.map, NormalGraph.clauses, NormalGraph.plain, NormalGraph.params,
            GraphRow.union, meetClauses] using hl
        rcases clause_reads_support scope cs hreads hp with h | ⟨_, slot, _⟩
        · left; simpa [Scope.label, Tree.free] using h
        · have hn := slot.isLt
          have hlen := congrArg List.length hlocals
          simp only [List.length_nil] at hlen
          omega
      · simp [boundReads, Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow,
          Template.instantiate, hb, GraphRow.map]
    | scheme bs sigs bounds rests resolution =>
      simp only [hb, RowTemplate.wellBound, Bool.and_eq_true_iff, decide_eq_true_eq] at hv
      simp only [NormalGraph.params, equations.kind_application, Option.isSome_none,
        Bool.false_eq_true, false_implies, true_and]
      constructor
      · intro l hl
        intro p hp
        have hreads : l ∈
            ((sigs.map (Arrow.map (fun es => es.flatMap (Expression.instantiate scope)))).flatMap
              (fun a => a.operands.flatten) ++
            (bounds.map (fun b => (b.1.instantiate scope, b.2.flatMap (Expression.instantiate scope)))).flatMap (·.2)) ++
            (rests.map (RestArrow.map (fun es => es.flatMap (Expression.instantiate scope)))).flatMap
              (fun a => a.operands.flatten) := by
          simpa only [reads, Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow,
            Scope.view_label, Template.instantiate, hb, GraphRow.map] using hl
        have hs : scope.supports true p.1 := by
          rcases List.mem_append.mp hreads with h | h
          · rcases List.mem_append.mp h with h | h
            · apply clause_reads_support scope [.arrs sigs rests] (hp := hp)
              simpa only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
                Clause.map, Clause.operands, List.flatten_append, List.append_nil, List.flatten_eq_flatMap, List.flatMap_append, List.flatMap_assoc] using
                List.mem_append_left _ h
            · obtain ⟨b', hb', h⟩ := List.mem_flatMap.mp h
              obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb'
              exact expressions_support scope b.2 (fun e _ => e.2.2) h hp
          · apply clause_reads_support scope [.arrs sigs rests] (hp := hp)
            simpa only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
              Clause.map, Clause.operands, List.flatten_append, List.append_nil, List.flatten_eq_flatMap, List.flatMap_append, List.flatMap_assoc] using
              List.mem_append_right _ h
        rcases hs with h | ⟨_, slot, he⟩
        · left; simpa [Scope.label, Tree.free] using h
        · right
          simp only [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Scope.view_label,
            Template.instantiate, hb, GraphRow.map]
          refine ⟨_, rfl, ?_⟩
          have hp' : p = scope.bound slot := Subtype.ext he
          rw [hp']
          rw [scope.instantiate_binders bs hv.1]
          exact Scope.mem_binders.mpr ⟨slot, rfl⟩
      · intro l hl p hp
        have hbounds : l ∈ (bounds.map (fun b =>
            (b.1.instantiate scope, b.2.flatMap (Expression.instantiate scope)))).flatMap (·.2) := by
          simpa only [boundReads, Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow,
            Scope.view_label, Template.instantiate, hb, GraphRow.map] using hl
        obtain ⟨b', hb', hl⟩ := List.mem_flatMap.mp hbounds
        obtain ⟨b, hbin, rfl⟩ := List.mem_map.mp hb'
        have hx := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hv.2 b hbin)).2
        have hs := expressions_support scope b.2 (List.all_eq_true.mp hx) hl hp
        rcases hs with h | ⟨h, _⟩
        · simpa [Scope.label, Tree.free] using h
        · cases h
  · intro scope slot _
    simp only [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Scope.view_bound,
      NormalGraph.params, reads, boundReads, meetClauses, NormalGraph.clauses, NormalGraph.plain]
    simp [Scope.bound, Tree.free]
  · intro o i k _
    simp only [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Label.view_familyVar,
      NormalGraph.params, reads, boundReads, meetClauses, NormalGraph.clauses, NormalGraph.plain]
    simp [Label.familyVar, Label.free, Tree.free]
  · intro ps valid h
    simp [Tree.isMeet] at h

theorem Clause.meet_operands {a b c : Clause α} (h : c ∈ PositiveNormalization.meet a b) {S : α}
    (hS : S ∈ c.operands) : S ∈ a.operands ∨ S ∈ b.operands := by
  cases a <;> cases b <;> unfold PositiveNormalization.meet at h <;>
    simp only [List.mem_singleton, List.not_mem_nil] at h <;>
    (try split at h) <;> (try simp only [List.mem_singleton, List.not_mem_nil] at h) <;>
    (try subst h) <;> simp only [Clause.operands, Tuple.operands, List.map_append, List.mem_append,
      List.flatMap_append, List.flatten_append, List.flatMap_cons] at hS ⊢ <;>
    grind (splits := 40)

/-- Normalization never meets two operands: a conjunction's operands are its
clauses'. -/
theorem meetAll_operands {Cs : List (List (Clause α))} {c : Clause α} (hc : c ∈ meetAll Cs)
    {S : α} (hS : S ∈ c.operands) : ∃ C ∈ Cs, ∃ d ∈ C, S ∈ d.operands := by
  induction Cs generalizing c with
  | nil =>
    simp only [meetAll, List.mem_singleton] at hc
    subst hc; simp [Clause.operands] at hS
  | cons C rest ih =>
    simp only [meetAll, meetLists, List.mem_flatMap, List.mem_filter] at hc
    obtain ⟨a, ha, b, hb, hm, -⟩ := hc
    rcases Clause.meet_operands hm hS with h | h
    · exact ⟨C, List.mem_cons_self, a, ha, h⟩
    · obtain ⟨C', hC', d, hd, h⟩ := ih hb h
      exact ⟨C', List.mem_cons_of_mem _ hC', d, hd, h⟩

theorem mem_meetClauseLists {rows : List (ι × GraphRow ι)} {C : List (Clause (List ι))}
    (h : C ∈ meetClauseLists rows) : ∃ x ∈ rows, x.2 = .clauses C := by
  induction rows with
  | nil => simp [meetClauseLists] at h
  | cons x rest ih =>
    obtain ⟨q, r⟩ := x
    cases r <;> simp only [meetClauseLists, List.mem_cons] at h
    all_goals first
      | (rcases h with rfl | h
         · exact ⟨_, List.mem_cons_self, rfl⟩
         · obtain ⟨y, hy, he⟩ := ih h; exact ⟨y, List.mem_cons_of_mem _ hy, he⟩)
      | (obtain ⟨y, hy, he⟩ := ih h; exact ⟨y, List.mem_cons_of_mem _ hy, he⟩)

theorem mem_meetRigid {rows : List (ι × GraphRow ι)} {q : ι}
    (h : q ∈ meetRigid rows) : ∃ x ∈ rows, x.1 = q := by
  induction rows with
  | nil => simp [meetRigid] at h
  | cons x rest ih =>
    obtain ⟨p, r⟩ := x
    cases r <;> simp only [meetRigid, List.mem_cons] at h
    all_goals first
      | (rcases h with rfl | h
         · exact ⟨_, List.mem_cons_self, rfl⟩
         · obtain ⟨y, hy, he⟩ := ih h; exact ⟨y, List.mem_cons_of_mem _ hy, he⟩)
      | (obtain ⟨y, hy, he⟩ := ih h; exact ⟨y, List.mem_cons_of_mem _ hy, he⟩)

/-- Computed syntax support satisfies the local closure conditions used by
both finite-table and equation-graph semantics. A meet reads its clause
parts' operands, and its parameter and scheme parts' support is its own. -/
theorem Equations.free_support (equations : Equations) :
    FreeSupport equations.graph (fun _ => True) Label.free := by
  -- A meet's parts, their rows, and its row.
  have meetData : ∀ (ps : Types) (valid : (Tree.meet ps).scoped equations.signature 0 0 = true),
      let parts := ps.labels (Bool.and_eq_true_iff.mp valid).1
      let rows := parts.map fun q => (q, equations.baseRow q)
      (∀ q ∈ parts, q.1.isMeet = false ∧
        ∀ r ∈ q.free, r ∈ Label.free (sig := equations.signature) ⟨.meet ps, valid⟩) ∧
      equations.row ⟨.meet ps, valid⟩ = meetRowOf rows := by
    intro ps valid parts rows
    refine ⟨fun q hq => ⟨?_, fun r hr => ?_⟩, rfl⟩
    · have h := (Bool.and_eq_true_iff.mp valid).2
      simp only [List.all_eq_true, Bool.not_eq_true'] at h
      exact h q.1 (Types.mem_labels.mp hq)
    · rw [Label.mem_free] at hr ⊢
      exact Types.free_of_mem (Types.mem_labels.mp hq) _ hr
  refine ⟨fun {label} _ => ?_, fun {label} _ q hq => ?_⟩
  · cases hm : label.1.isMeet
    · exact equations.row_support label hm
    rcases label with ⟨t, valid⟩
    cases t <;> simp only [Tree.isMeet, reduceCtorEq] at hm
    rename_i ps
    obtain ⟨hparts, hrow⟩ := meetData ps valid
    let rows := (ps.labels (Bool.and_eq_true_iff.mp valid).1).map fun q => (q, equations.baseRow q)
    -- Its rows are clause rows or meet rows over the parts' conjunction.
    have hshape : equations.graph.params ⟨.meet ps, valid⟩ = false ∧
        equations.graph.schemes ⟨.meet ps, valid⟩ = none ∧
        ∀ c ∈ equations.graph ⟨.meet ps, valid⟩ ++ meetClauses equations.graph ⟨.meet ps, valid⟩,
          c ∈ meetAll ((meetClauseLists rows).eraseDups) := by
      cases hr : meetRigid rows with
      | nil =>
        have hrow' : equations.row ⟨.meet ps, valid⟩ =
            .clauses ((meetAll ((meetClauseLists rows).eraseDups)).filter Clause.isValue) := by
          rw [hrow]; simp only [meetRowOf]; rw [hr]
        obtain ⟨_, hG⟩ := equations.graph_clauses hrow'
        refine ⟨by simp [NormalGraph.params, Equations.graph, NormalGraph.ofRowMap, hrow'],
          by simp [Equations.graph, NormalGraph.ofRowMap, hrow'], fun c hc => ?_⟩
        rw [hG] at hc
        simp only [meetClauses, Equations.graph, NormalGraph.ofRowMap, hrow', Option.map_none,
          Option.getD_none, List.append_nil] at hc
        exact (List.mem_filter.mp hc).1
      | cons p rs =>
        have hrow' : equations.row ⟨.meet ps, valid⟩ = .meet p (meetAll ((meetClauseLists rows).eraseDups)) rs := by
          rw [hrow]; simp only [meetRowOf]; rw [hr]
        refine ⟨by simp [NormalGraph.params, Equations.graph, NormalGraph.ofRowMap, hrow'],
          by simp [Equations.graph, NormalGraph.ofRowMap, hrow'], fun c hc => ?_⟩
        simpa [NormalGraph.clauses, NormalGraph.plain, NormalGraph.params, meetClauses,
          Equations.graph, NormalGraph.ofRowMap, hrow'] using hc
    obtain ⟨hpar, hsch, hcl⟩ := hshape
    refine ⟨(fun h => by rw [hpar] at h; cases h), (fun l hl => ⟨trivial, fun p hp => .inl ?_⟩),
      (fun l hl => by simp [boundReads, hsch] at hl)⟩
    simp only [reads, hsch] at hl
    obtain ⟨c, hc, hl⟩ := List.mem_flatMap.mp hl
    obtain ⟨S, hS, hlS⟩ := List.mem_flatten.mp hl
    obtain ⟨C, hC, d, hd, hSd⟩ := meetAll_operands (hcl c hc) hS
    obtain ⟨⟨q, r⟩, hx, hr⟩ := mem_meetClauseLists (List.mem_eraseDups.mp hC)
    simp only at hr
    subst hr
    obtain ⟨q', hq', he⟩ := List.mem_map.mp hx
    simp only [Prod.mk.injEq] at he
    obtain ⟨he1, hb⟩ := he
    subst q'
    obtain ⟨hflat, hfree⟩ := hparts q hq'
    -- The operand is read by the clause part, whose support is the meet's.
    have hrq := equations.row_nonmeet q hflat
    obtain ⟨hplain, hG⟩ := equations.graph_clauses (hrq.trans hb)
    have hread : l ∈ reads equations.graph q := by
      have hsq : equations.graph.schemes q = none := (NormalGraph.plain_iff.mp hplain).2.1
      simp only [reads, hsq, hG]
      exact List.mem_flatMap.mpr ⟨d, List.mem_append_left _ hd, List.mem_flatten.mpr ⟨S, hSd, hlS⟩⟩
    rcases ((equations.row_support q hflat).2.1 l hread).2 p hp with h | ⟨s, hs, _⟩
    · exact hfree p h
    · rw [(NormalGraph.plain_iff.mp hplain).2.1] at hs; cases hs
  · cases hm : label.1.isMeet
    · -- Only a meet has parts.
      have hn := equations.baseRow_ne_meet label
      have hmeets : equations.graph.meets label = none := by
        simp only [Equations.graph, NormalGraph.ofRowMap, equations.row_nonmeet label hm]
        cases hb : equations.baseRow label with
        | meet p cs ps => exact absurd hb (hn p cs ps)
        | _ => rfl
      simp [meetParts, hmeets] at hq
    rcases label with ⟨t, valid⟩
    cases t <;> simp only [Tree.isMeet, reduceCtorEq] at hm
    rename_i ps
    obtain ⟨hparts, hrow⟩ := meetData ps valid
    let rows := (ps.labels (Bool.and_eq_true_iff.mp valid).1).map fun q => (q, equations.baseRow q)
    have hq' : q ∈ ps.labels (Bool.and_eq_true_iff.mp valid).1 := by
      cases hr : meetRigid rows with
      | nil =>
        have hrow' : equations.row ⟨.meet ps, valid⟩ =
            .clauses ((meetAll ((meetClauseLists rows).eraseDups)).filter Clause.isValue) := by
          rw [hrow]; simp only [meetRowOf]; rw [hr]
        simp [meetParts, Equations.graph, NormalGraph.ofRowMap, hrow'] at hq
      | cons p rs =>
        have hrow' : equations.row ⟨.meet ps, valid⟩ = .meet p (meetAll ((meetClauseLists rows).eraseDups)) rs := by
          rw [hrow]; simp only [meetRowOf]; rw [hr]
        have hmem : q ∈ meetRigid rows := by
          rw [hr]
          simpa [meetParts, Equations.graph, NormalGraph.ofRowMap, hrow'] using hq
        obtain ⟨x, hx, rfl⟩ := mem_meetRigid hmem
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hx
        exact hq'
    obtain ⟨hflat, hfree⟩ := hparts q hq'
    refine ⟨fun hp => hfree q ((equations.row_support q hflat).1 hp), fun _ => ⟨trivial, hfree⟩⟩

/-- An equation type depends only on the free parameters carried by its
application arguments. This covers both values and argument packs. -/
theorem Equations.agree_free (equations : Equations) (η θ : MixedAssignment (Label equations.signature))
    (S : List (Label equations.signature))
    (h : ∀ l ∈ S, ∀ p ∈ l.free, η.1 p = θ.1 p) :
    mixedMeaning equations.graph η S = mixedMeaning equations.graph θ S := by
  have hs := equations.free_support
  exact (mixed_respectsSupport hs).bound _
    (agree_supportWith hs (mixedParameters equations.graph) (mixed_respectsSupport hs))
    η θ S (fun _ _ => True.intro) (fun l hl p hp => congrArg _ (h l hl p hp))

#print axioms Equations.free_support
#print axioms Equations.agree_free

end Verification.EquationGraphs
