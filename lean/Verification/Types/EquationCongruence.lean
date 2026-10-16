import Verification.Types.EquationSupport

/-! Semantic congruence for parameterized equations. Local binders are owned by
an application, but their names must not affect what a quantified type means. -/
namespace Verification.EquationGraphs
open PositiveGraphs PositiveRules PositiveNormalization CallEffects

private theorem assign_index (η : ParameterAssignment k ι) (bs : List ι)
    (As : List (ParameterFamily k)) (unique : bs.Nodup) (lengths : As.length = bs.length)
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
        exact ih As (List.nodup_cons.mp unique).2 (by simpa using lengths) i (by simpa using hi)

theorem Scope.assign_bound (scope : Scope sig) (η : MixedAssignment (Label sig))
    (As : List MixedFamily) (hlen : As.length = sig[scope.head].binders.length)
    (slot : Fin sig[scope.head].binders.length) :
    (assign η scope.binders As).1 (scope.bound slot) = (As[slot.val]'(by omega)).1 := by
  have h := assign_index η scope.binders As scope.binders_nodup (by simpa using hlen)
    slot.val (by simp)
  simpa [Scope.binders, List.getElem_map, List.getElem_finRange] using h

/-- No local of an application is free in any of its captured arguments. -/
theorem Scope.argument_free (scope : Scope sig) (A : List (Label sig)) (hA : A ∈ scope.arguments)
    (l : Label sig) (hl : l ∈ A) (p : Label sig) (hp : p ∈ l.free) : p ∉ scope.binders := by
  intro hin
  obtain ⟨slot, rfl⟩ := Scope.mem_binders.mp hin
  apply scope.bound_fresh slot
  simp only [Scope.rawArgs, Args.free_ofList, Types.free_ofList, List.flatMap_map]
  exact List.mem_flatMap.mpr ⟨A, hA, List.mem_flatMap.mpr ⟨l, hl, Label.mem_free.mp hp⟩⟩

/-- Quantifying a scope's locals leaves its captured type arguments unchanged,
even if those arguments refer to other applications' parameters. -/
theorem Equations.arguments_assign (equations : Equations) (scope : Scope equations.signature)
    (η : MixedAssignment (Label equations.signature)) (As : List MixedFamily)
    (A : List (Label equations.signature)) (hA : A ∈ scope.arguments) :
    mixedMeaning equations.graph (assign η scope.binders As) A = mixedMeaning equations.graph η A := by
  apply equations.agree_free
  intro l hl p hp
  exact assign_nmem η scope.binders As (scope.argument_free A hA l hl p hp)

/-- Local parameters at the same slot receive the same selected semantic
family in two applications of one equation head. -/
theorem Equations.locals_assign (equations : Equations)
    (a b : Scope equations.signature) (head : a.head = b.head)
    (η θ : MixedAssignment (Label equations.signature)) (As : List MixedFamily)
    (hlen : As.length = equations.signature[a.head].binders.length)
    (i : Nat) (hi : i < equations.signature[a.head].binders.length) :
    mixedMeaning equations.graph (assign η a.binders As) [a.bound ⟨i, hi⟩] =
    mixedMeaning equations.graph (assign θ b.binders As) [b.bound ⟨i, by simpa [← head] using hi⟩] := by
  rw [mixedMeaning_parameter _ _ _ _ (equations.kind_bound a ⟨i, hi⟩),
    mixedMeaning_parameter _ _ _ _ (equations.kind_bound b ⟨i, by simpa [← head] using hi⟩)]
  rw [a.assign_bound η As hlen, b.assign_bound θ As (by simpa [← head] using hlen)]
  simp [head]

/-- Positionwise agreement of a declaration's mixed type arguments. -/
def Equations.ArgumentsAgree (equations : Equations)
    (η θ : MixedAssignment (Label equations.signature))
    (As Bs : List (List (Label equations.signature))) (n : Nat) : Prop :=
  As.length = Bs.length ∧ ∀ i (ha : i < As.length) (hb : i < Bs.length),
    Agree (mixedMeaning equations.graph η As[i]) (mixedMeaning equations.graph θ Bs[i]) n

/-- The induction hypothesis needed to lift argument agreement through finite
expressions. This is a proof premise, never an accepted certificate assumption. -/
def Equations.ApplicationsAgree (equations : Equations) (n : Nat) : Prop :=
  ∀ (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature)),
    a.head = b.head → equations.ArgumentsAgree η θ a.arguments b.arguments n →
    Agree (mixedMeaning equations.graph η [a.label]) (mixedMeaning equations.graph θ [b.label]) n

private theorem mixed_append_agree (G : NormalGraph ι) (η θ : MixedAssignment ι)
    (As Bs Cs Ds : List ι)
    (h1 : Agree (mixedMeaning G η As) (mixedMeaning G θ Bs) n)
    (h2 : Agree (mixedMeaning G η Cs) (mixedMeaning G θ Ds) n) :
    Agree (mixedMeaning G η (As ++ Cs)) (mixedMeaning G θ (Bs ++ Ds)) n := by
  intro m hm W x
  have happ (ρ : MixedAssignment ι) (A B : List ι) : mixedMeaning G ρ (A ++ B) m W x ↔
      mixedMeaning G ρ A m W x ∨ mixedMeaning G ρ B m W x := by
    rw [mixedMeaning_union G ρ (A ++ B), mixedMeaning_union G ρ A, mixedMeaning_union G ρ B]
    simp only [List.mem_append, or_and_right, exists_or]
  rw [happ, happ]
  exact or_congr (h1 m hm W x) (h2 m hm W x)

/-- A meet template instantiates to the canonical meets of every choice of a
label from each part's union. -/
theorem Tree.instantiate_meet_labels (scope : Scope sig) (ps : Types)
    (valid : (Tree.meet ps).scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (closed : (Tree.instantiate scope (.meet ps) valid).1.scoped sig 0 0 = true) :
    (Tree.instantiate scope (.meet ps) valid).1.labels closed =
      (choices (Types.instantiateParts scope ps (Bool.and_eq_true_iff.mp valid).1)).map Label.meetOf := by
  simp only [Tree.instantiate]
  exact Types.labels_ofList _ _

mutual
/-- Finite template traversal preserves semantic agreement, assuming it for
applications at the same step index. Captures and locals are separate premises. -/
theorem Tree.instantiate_agree (equations : Equations) (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (locals : allowLocals = true → ∀ i (ha : i < equations.signature[a.head].binders.length)
      (hb : i < equations.signature[b.head].binders.length),
      Agree (mixedMeaning equations.graph η [a.bound ⟨i, ha⟩])
        (mixedMeaning equations.graph θ [b.bound ⟨i, hb⟩]) n)
    (t : Tree) (va : t.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : t.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : t.lexical allowLocals = true) :
    Agree (mixedMeaning equations.graph η ((Tree.instantiate a t va).1.labels (Tree.instantiate a t va).2))
      (mixedMeaning equations.graph θ ((Tree.instantiate b t vb).1.labels (Tree.instantiate b t vb).2)) n := by
  cases t with
  | bound h ts slot => simp [Tree.lexical] at lex
  | var o i k => simp [Tree.lexical] at lex
  | argument i =>
    simpa only [Tree.instantiate, Types.labels_ofList] using args.2 i
      (by have := of_decide_eq_true va; simpa only [a.arity] using this)
      (by have := of_decide_eq_true vb; simpa only [b.arity] using this)
  | «local» i => exact locals lex i (of_decide_eq_true va) (of_decide_eq_true vb)
  | app h ts =>
    let oa := Args.instantiate a ts (Bool.and_eq_true_iff.mp va).2
    let ob := Args.instantiate b ts (Bool.and_eq_true_iff.mp vb).2
    have ca : (Tree.app h oa.1).scoped equations.signature 0 0 = true := by
      have hv := (Tree.instantiate a (.app h ts) va).2
      simpa only [Tree.instantiate, Types.scoped, Bool.and_true] using hv
    have cb : (Tree.app h ob.1).scoped equations.signature 0 0 = true := by
      have hv := (Tree.instantiate b (.app h ts) vb).2
      simpa only [Tree.instantiate, Types.scoped, Bool.and_true] using hv
    let sa := Scope.ofRaw h oa.1 (Bool.and_eq_true_iff.mp ca).1 oa.2.1
    let sb := Scope.ofRaw h ob.1 (Bool.and_eq_true_iff.mp cb).1 ob.2.1
    have hr := Args.instantiate_agree equations apps a b η θ args locals ts
      (Bool.and_eq_true_iff.mp va).2 (Bool.and_eq_true_iff.mp vb).2 lex
    have hs := apps sa sb η θ rfl hr
    dsimp only [sa, sb] at hs
    simp only [Scope.label, Scope.ofRaw_args] at hs
    simpa only [Scope.ofRaw, Tree.instantiate, Types.labels, oa, ob] using hs
  | meet ps =>
    rw [Tree.instantiate_meet_labels, Tree.instantiate_meet_labels]
    have hp := Types.instantiateParts_agree equations apps a b η θ args locals ps
      (Bool.and_eq_true_iff.mp va).1 (Bool.and_eq_true_iff.mp vb).1 lex
    exact equations.distribute_meaning η θ _ _ hp.1 fun i ha hb m hm W v =>
      hp.2 i ha hb m hm W (.inl v)

theorem Types.instantiateParts_agree (equations : Equations) (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (locals : allowLocals = true → ∀ i (ha : i < equations.signature[a.head].binders.length)
      (hb : i < equations.signature[b.head].binders.length),
      Agree (mixedMeaning equations.graph η [a.bound ⟨i, ha⟩])
        (mixedMeaning equations.graph θ [b.bound ⟨i, hb⟩]) n)
    (ts : Types) (va : ts.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : ts.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : ts.lexical allowLocals = true) :
    (Types.instantiateParts a ts va).length = (Types.instantiateParts b ts vb).length ∧
    ∀ i (ha : i < (Types.instantiateParts a ts va).length)
      (hb : i < (Types.instantiateParts b ts vb).length),
      Agree (mixedMeaning equations.graph η (Types.instantiateParts a ts va)[i])
        (mixedMeaning equations.graph θ (Types.instantiateParts b ts vb)[i]) n := by
  cases ts with
  | nil => exact ⟨rfl, fun i hi _ => by simp [Types.instantiateParts] at hi⟩
  | cons t ts =>
    have hh := Tree.instantiate_agree equations apps a b η θ args locals t
      (Bool.and_eq_true_iff.mp va).1 (Bool.and_eq_true_iff.mp vb).1 (Bool.and_eq_true_iff.mp lex).1
    have ht := Types.instantiateParts_agree equations apps a b η θ args locals ts
      (Bool.and_eq_true_iff.mp va).2 (Bool.and_eq_true_iff.mp vb).2 (Bool.and_eq_true_iff.mp lex).2
    refine ⟨by simp only [Types.instantiateParts, List.length_cons, ht.1], ?_⟩
    intro i hi hj
    cases i with
    | zero => exact hh
    | succ i =>
      exact ht.2 i
        (by simpa only [Types.instantiateParts, List.length_cons, Nat.succ_lt_succ_iff] using hi)
        (by simpa only [Types.instantiateParts, List.length_cons, Nat.succ_lt_succ_iff] using hj)

theorem Types.instantiate_agree (equations : Equations) (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (locals : allowLocals = true → ∀ i (ha : i < equations.signature[a.head].binders.length)
      (hb : i < equations.signature[b.head].binders.length),
      Agree (mixedMeaning equations.graph η [a.bound ⟨i, ha⟩])
        (mixedMeaning equations.graph θ [b.bound ⟨i, hb⟩]) n)
    (ts : Types) (va : ts.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : ts.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : ts.lexical allowLocals = true) :
    Agree (mixedMeaning equations.graph η ((Types.instantiate a ts va).1.labels (Types.instantiate a ts va).2))
      (mixedMeaning equations.graph θ ((Types.instantiate b ts vb).1.labels (Types.instantiate b ts vb).2)) n := by
  cases ts with
  | nil =>
    intro m hm W x
    cases x <;> simp [Types.instantiate, Types.labels, mixedMeaning, mixedParameters, graphArguments, Tower.setSem]
  | cons t ts =>
    simp only [Types.instantiate]
    rw [Types.labels_append _ _ (Tree.instantiate a t (Bool.and_eq_true_iff.mp va).1).2
      (Types.instantiate a ts (Bool.and_eq_true_iff.mp va).2).2,
      Types.labels_append _ _ (Tree.instantiate b t (Bool.and_eq_true_iff.mp vb).1).2
      (Types.instantiate b ts (Bool.and_eq_true_iff.mp vb).2).2]
    exact mixed_append_agree _ _ _ _ _ _ _
      (Tree.instantiate_agree equations apps a b η θ args locals t
        (Bool.and_eq_true_iff.mp va).1 (Bool.and_eq_true_iff.mp vb).1 (Bool.and_eq_true_iff.mp lex).1)
      (Types.instantiate_agree equations apps a b η θ args locals ts
        (Bool.and_eq_true_iff.mp va).2 (Bool.and_eq_true_iff.mp vb).2 (Bool.and_eq_true_iff.mp lex).2)

theorem Args.instantiate_agree (equations : Equations) (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (locals : allowLocals = true → ∀ i (ha : i < equations.signature[a.head].binders.length)
      (hb : i < equations.signature[b.head].binders.length),
      Agree (mixedMeaning equations.graph η [a.bound ⟨i, ha⟩])
        (mixedMeaning equations.graph θ [b.bound ⟨i, hb⟩]) n)
    (ts : Args) (va : ts.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : ts.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : ts.lexical allowLocals = true) :
    equations.ArgumentsAgree η θ
      ((Args.instantiate a ts va).1.labels (Args.instantiate a ts va).2.1)
      ((Args.instantiate b ts vb).1.labels (Args.instantiate b ts vb).2.1) n := by
  cases ts with
  | nil => exact ⟨rfl, fun i hi _ => False.elim (Nat.not_lt_zero _ hi)⟩
  | cons t ts =>
    have hh := Types.instantiate_agree equations apps a b η θ args locals t
      (Bool.and_eq_true_iff.mp va).1 (Bool.and_eq_true_iff.mp vb).1 (Bool.and_eq_true_iff.mp lex).1
    have ht := Args.instantiate_agree equations apps a b η θ args locals ts
      (Bool.and_eq_true_iff.mp va).2 (Bool.and_eq_true_iff.mp vb).2 (Bool.and_eq_true_iff.mp lex).2
    refine ⟨by simpa only [Args.instantiate, Args.labels, List.length_cons] using congrArg Nat.succ ht.1, ?_⟩
    intro i hi hj
    cases i with
    | zero => exact hh
    | succ i =>
      exact ht.2 i
        (by simpa only [Args.instantiate, Args.labels, List.length_cons, Nat.succ_lt_succ_iff] using hi)
        (by simpa only [Args.instantiate, Args.labels, List.length_cons, Nat.succ_lt_succ_iff] using hj)
end

theorem Equations.ArgumentsAgree.mono {equations : Equations} {η θ As Bs n m}
    (h : equations.ArgumentsAgree η θ As Bs n) (hm : m ≤ n) :
    equations.ArgumentsAgree η θ As Bs m :=
  ⟨h.1, fun i hi hj => PositiveGraphs.Agree.mono (h.2 i hi hj) hm⟩

/-- Entering binders on both sides preserves agreement of captured arguments. -/
theorem Equations.ArgumentsAgree.assign {equations : Equations}
    {η θ : MixedAssignment (Label equations.signature)} {a b : Scope equations.signature}
    (h : equations.ArgumentsAgree η θ a.arguments b.arguments n) (As Bs : List MixedFamily) :
    equations.ArgumentsAgree (PositiveGraphs.assign η a.binders As)
      (PositiveGraphs.assign θ b.binders Bs) a.arguments b.arguments n := by
  refine ⟨h.1, ?_⟩
  intro i hi hj
  rw [equations.arguments_assign a η As _ (List.getElem_mem hi),
    equations.arguments_assign b θ Bs _ (List.getElem_mem hj)]
  exact h.2 i hi hj

/-- Signature expressions retain agreement after their applications quantify
corresponding locals. The application-congruence premise is the recursive
induction hypothesis, not an external semantic assumption. -/
theorem Equations.signature_expression_agree (equations : Equations)
    (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (head : a.head = b.head)
    (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (As : List MixedFamily) (hlen : As.length = equations.signature[a.head].binders.length)
    (t : Tree) (va : t.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : t.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : t.lexical true = true) :
    Agree (mixedMeaning equations.graph (assign η a.binders As)
      ((Tree.instantiate a t va).1.labels (Tree.instantiate a t va).2))
      (mixedMeaning equations.graph (assign θ b.binders As)
        ((Tree.instantiate b t vb).1.labels (Tree.instantiate b t vb).2)) n := by
  apply Tree.instantiate_agree equations apps a b _ _ (args.assign As As) _ t va vb lex
  intro _ i hi hj
  have he := equations.locals_assign a b head η θ As hlen i hi
  rw [he]
  exact fun _ _ _ _ => Iff.rfl

/-- Bound expressions are compared in their outer environments. They cannot
read a locally quantified parameter, so no local agreement premise is needed. -/
theorem Equations.bound_expression_agree (equations : Equations)
    (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (t : Tree) (va : t.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : t.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : t.lexical false = true) :
    Agree (mixedMeaning equations.graph η ((Tree.instantiate a t va).1.labels (Tree.instantiate a t va).2))
      (mixedMeaning equations.graph θ ((Tree.instantiate b t vb).1.labels (Tree.instantiate b t vb).2)) n :=
  Tree.instantiate_agree equations apps a b η θ args (fun h => Bool.noConfusion h) t va vb lex

private theorem mixed_flatMap_agree (G : NormalGraph ι) (η θ : MixedAssignment ι)
    (f g : α → List ι) (es : List α)
    (h : ∀ e ∈ es, Agree (mixedMeaning G η (f e)) (mixedMeaning G θ (g e)) n) :
    Agree (mixedMeaning G η (es.flatMap f)) (mixedMeaning G θ (es.flatMap g)) n := by
  induction es with
  | nil => intro m hm U x; cases x <;> simp [mixedMeaning, mixedParameters, graphArguments, Tower.setSem]
  | cons e es ih =>
    exact mixed_append_agree _ _ _ _ _ _ _ (h e List.mem_cons_self)
      (ih fun e he => h e (List.mem_cons_of_mem _ he))

private theorem mapped_sem_agree (G : NormalGraph ι) (η θ : MixedAssignment ι)
    (f g : α → List ι) (h : ∀ e, Agree (mixedMeaning G η (f e)) (mixedMeaning G θ (g e)) n)
    (c : Clause α) (W : WorldT n) (v : Val) :
    semWithArgs Ξ (mixedValues G η) (mixedArgs G η) (c.map f) n W v ↔
      semWithArgs Ξ (mixedValues G θ) (mixedArgs G θ) (c.map g) n W v := by
  rw [semWithArgs_map, semWithArgs_map]
  exact semWithArgs_congr _ _ _ _ n (fun _ _ _ _ => Iff.rfl) (fun e m hm U u => h e m hm U (.inl u))
    (fun e m hm U us => h e m hm U (.inr us)) c W v

/-- A clause reads its operand families below the current level. Mapping its
operands changes neither its shape nor the fixed built-in array requirement. -/
private theorem mapped_clause_agree (G : NormalGraph ι) (η θ : MixedAssignment ι)
    (f g : α → List ι) (h : ∀ e, Agree (mixedMeaning G η (f e)) (mixedMeaning G θ (g e)) n)
    (c : Clause α) (W : WorldT n) (v : Val) :
    mixedSem G η (c.map f) n W v ↔ mixedSem G θ (c.map g) n W v := by
  apply and_congr
  · exact mapped_sem_agree G η θ f g h c W v
  · unfold builtinInvariant
    simp only [Clause.carriesInvariant_map]

/-- The value half of the application-congruence induction for a clause head.
All recursive operand reasoning is below the current step index. -/
theorem Equations.clauses_step (equations : Equations) (apps : equations.ApplicationsAgree n)
    (head : Fin equations.signature.length)
    (A B : List (List (Label equations.signature)))
    (ha : A.length = equations.signature[head].parameters)
    (hb : B.length = equations.signature[head].parameters)
    (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ A B n)
    (cs : List (Clause (List (Expression equations.signature equations.signature[head]))))
    (body : (equations.body head).1 = .clauses cs) (W : WorldT n) (v : Val) :
    qDenoteWithArgs equations.graph (mixedParameters equations.graph)
      (η, (Scope.mk head A ha).label) n W v ↔
    qDenoteWithArgs equations.graph (mixedParameters equations.graph)
      (θ, (Scope.mk head B hb).label) n W v := by
  let a : Scope equations.signature := ⟨head, A, ha⟩
  let b : Scope equations.signature := ⟨head, B, hb⟩
  have empty : equations.signature[head].binders = [] := by
    have h := (equations.body head).2
    simpa [body, RowTemplate.wellBound] using h
  have exprs : ∀ es : List (Expression equations.signature equations.signature[head]),
      Agree (mixedMeaning equations.graph η (es.flatMap (Expression.instantiate a)))
        (mixedMeaning equations.graph θ (es.flatMap (Expression.instantiate b))) n := by
    intro es
    apply mixed_flatMap_agree
    intro e _
    apply Tree.instantiate_agree equations apps a b η θ args _ e.1 e.2.1 e.2.1 e.2.2
    intro _ i hi hj
    have hlen := congrArg List.length empty
    have hi' : i < equations.signature[head].binders.length := hi
    simp only [List.length_nil] at hlen
    omega
  have plain (C) (hc : C.length = equations.signature[head].parameters) :
      equations.graph.plain (Scope.mk head C hc).label = true := by
    simp [NormalGraph.plain, NormalGraph.params, Equations.graph, NormalGraph.ofRowMap,
      Equations.row, Equations.baseRow, Template.instantiate, body, GraphRow.map]
  have row (C) (hc : C.length = equations.signature[head].parameters) :
      equations.graph (Scope.mk head C hc).label =
        cs.map (Clause.map (fun es => es.flatMap (Expression.instantiate ⟨head, C, hc⟩))) := by
    simp [NormalGraph.clauses, NormalGraph.plain, NormalGraph.params, Equations.graph,
      NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Template.instantiate, body, GraphRow.map, GraphRow.union]
  rw [mixed_unfold_plain η (plain A ha), mixed_unfold_plain θ (plain B hb), row A ha, row B hb]
  constructor
  · rintro ⟨c', hc', hv⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, (mapped_clause_agree _ η θ _ _ exprs c W v).mp hv⟩
  · rintro ⟨c', hc', hv⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, (mapped_clause_agree _ η θ _ _ exprs c W v).mpr hv⟩

/-- The quantified value step compares bounds outside local assignment, then
compares every instance at matching local families. Both fixed and variadic
signatures use the ordinary call-clause semantics. -/
theorem Equations.scheme_step (equations : Equations) (apps : equations.ApplicationsAgree n)
    (head : Fin equations.signature.length)
    (A B : List (List (Label equations.signature)))
    (ha : A.length = equations.signature[head].parameters)
    (hb : B.length = equations.signature[head].parameters)
    (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ A B n)
    (bs : List (Reference equations.signature equations.signature[head]))
    (sigs : List (Arrow (List (Expression equations.signature equations.signature[head]))))
    (bounds : List (Reference equations.signature equations.signature[head] ×
      List (Expression equations.signature equations.signature[head])))
    (rests : List (RestArrow (List (Expression equations.signature equations.signature[head]))))
    (resolution : List ResolutionSlots) (construct : Bool)
    (body : (equations.body head).1 = .scheme bs sigs bounds rests resolution construct) (W : WorldT n) (v : Val) :
    qDenoteWithArgs equations.graph (mixedParameters equations.graph)
      (η, (Scope.mk head A ha).label) n W v ↔
    qDenoteWithArgs equations.graph (mixedParameters equations.graph)
      (θ, (Scope.mk head B hb).label) n W v := by
  let a : Scope equations.signature := ⟨head, A, ha⟩
  let b : Scope equations.signature := ⟨head, B, hb⟩
  let make (C : List (List (Label equations.signature)))
      (hc : C.length = equations.signature[head].parameters) : SchemeRow (Label equations.signature) :=
    let scope : Scope equations.signature := ⟨head, C, hc⟩
    let inst := fun es => es.flatMap (Expression.instantiate scope)
    ⟨scope.binders, sigs.map (Arrow.map inst),
      bounds.map (fun p => (p.1.instantiate scope, inst p.2)), rests.map (RestArrow.map inst), resolution,
      construct⟩
  have valid := (equations.body head).2
  simp only [body, RowTemplate.wellBound, Bool.and_eq_true_iff, decide_eq_true_eq] at valid
  have row (C) (hc : C.length = equations.signature[head].parameters) :
      equations.graph.schemes (Scope.mk head C hc).label = some (make C hc) := by
    simp only [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Scope.view_label,
      Template.instantiate, body, GraphRow.map, make,
      (Scope.mk head C hc).instantiate_binders bs valid.1]
  have lengths (C) (hc : C.length = equations.signature[head].parameters) :
      (make C hc).binders.length = equations.signature[head].binders.length := by
    exact Scope.binders_length _
  have in_bs : ∀ p ∈ bounds, p.1 ∈ bs := by
    intro p hp
    have h := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid.2 p hp)).1
    obtain ⟨r, hr, he⟩ := List.any_eq_true.mp h
    have he' : r = p.1 := of_decide_eq_true he
    exact he' ▸ hr
  have localRefs : ∀ r ∈ bs,
      ∃ slot : Fin equations.signature[head].binders.length, r.1.1 = Tree.local slot.val := by
    intro r hr
    have hmem : r.1.1 ∈ (List.range equations.signature[head].binders.length).map Tree.local := by
      rw [← valid.1]
      exact List.mem_map.mpr ⟨r, hr, rfl⟩
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hmem
    exact ⟨⟨i, List.mem_range.mp hi⟩, he.symm⟩
  have reference_injective (C) (hc : C.length = equations.signature[head].parameters) :
      ∀ r ∈ bs, ∀ t ∈ bs, r.instantiate (Scope.mk head C hc) =
        t.instantiate (Scope.mk head C hc) → r = t := by
    intro r hr t ht he
    obtain ⟨i, hi⟩ := localRefs r hr
    obtain ⟨j, hj⟩ := localRefs t ht
    rw [r.instantiate_local (Scope.mk head C hc) i hi,
      t.instantiate_local (Scope.mk head C hc) j hj] at he
    have hij := (Scope.mk head C hc).bound_injective he
    apply Subtype.ext
    apply Subtype.ext
    rw [hi, hj, hij]
  have at_slot (C) (hc : C.length = equations.signature[head].parameters)
      (r : Reference equations.signature equations.signature[head]) (hr : r ∈ bs) (p : Nat) :
      (Scope.mk head C hc).binders[p]? = some (r.instantiate (Scope.mk head C hc)) ↔ bs[p]? = some r := by
    rw [← (Scope.mk head C hc).instantiate_binders bs valid.1, List.getElem?_map]
    constructor
    · intro h
      obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp h
      have htr : t = r := reference_injective C hc
        t (List.mem_of_getElem? ht) r hr he
      rwa [htr] at ht
    · intro h
      simp [h]
  have protect (C) (hc : C.length = equations.signature[head].parameters)
      (D) (hd : D.length = equations.signature[head].parameters) :
      (make C hc).protectedSlots → (make D hd).protectedSlots := by
    intro h g hg p hp z hget Z hbound
    change (Scope.mk head D hd).binders[p]? = some z at hget
    change (z, Z) ∈ bounds.map (fun t =>
      (t.1.instantiate (Scope.mk head D hd), t.2.flatMap (Expression.instantiate (Scope.mk head D hd)))) at hbound
    obtain ⟨⟨r, es⟩, hm, he⟩ := List.mem_map.mp hbound
    have hz : z = r.instantiate (Scope.mk head D hd) := (congrArg Prod.fst he).symm
    subst z
    have hlookup := (at_slot C hc r (in_bs (r, es) hm) p).mpr
      ((at_slot D hd r (in_bs (r, es) hm) p).mp hget)
    apply h g hg p hp (r.instantiate (Scope.mk head C hc)) hlookup
      (es.flatMap (Expression.instantiate (Scope.mk head C hc)))
    exact List.mem_map.mpr ⟨(r, es), hm, rfl⟩
  have bound_types : ∀ p ∈ bounds,
      Agree (mixedMeaning equations.graph η (p.2.flatMap (Expression.instantiate a)))
        (mixedMeaning equations.graph θ (p.2.flatMap (Expression.instantiate b))) n := by
    intro p hp
    have hlex := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid.2 p hp)).2
    apply mixed_flatMap_agree
    intro e he
    exact equations.bound_expression_agree apps a b η θ args e.1 e.2.1 e.2.1
      (List.all_eq_true.mp hlex e he)
  rw [qDenoteWithArgs_unfold _ _ (η, a.label), qDenoteWithArgs_unfold _ _ (θ, b.label)]
  have hpa : equations.graph.params a.label ≠ true := by
    simp [NormalGraph.params, equations.kind_application a]
  have hpb : equations.graph.params b.label ≠ true := by
    simp [NormalGraph.params, equations.kind_application b]
  dsimp only [qLayerWithArgs]
  rw [if_neg hpa, if_neg hpb, row A ha, row B hb]
  simp only [schemeSemWithArgs, boundedSem, lengths]
  refine and_congr Iff.rfl (forall_congr' fun q => forall_congr' fun hq => forall_congr' fun As => forall_congr' fun hlen =>
    imp_congr (equations.graph.domain.congr (make A ha) (make B hb) rfl
      ⟨protect A ha B hb, protect B hb A ha⟩ As) (imp_congr ?_ ?_))
  · have assigned : ∀ r ∈ bs,
        (assign η a.binders As).1 (r.instantiate a) =
          (assign θ b.binders As).1 (r.instantiate b) := by
      intro r hr
      have hmem : r.1.1 ∈ (List.range equations.signature[head].binders.length).map Tree.local := by
        rw [← valid.1]
        exact List.mem_map.mpr ⟨r, hr, rfl⟩
      obtain ⟨i, hi, he⟩ := List.mem_map.mp hmem
      let slot : Fin equations.signature[head].binders.length := ⟨i, List.mem_range.mp hi⟩
      rw [r.instantiate_local a slot he.symm, r.instantiate_local b slot he.symm,
        a.assign_bound η As hlen, b.assign_bound θ As hlen]
    have mem_a : ∀ p ∈ bounds, p.1.instantiate a ∈ a.binders := by
      intro p hp
      rw [← a.instantiate_binders bs valid.1]
      exact List.mem_map.mpr ⟨p.1, in_bs p hp, rfl⟩
    have mem_b : ∀ p ∈ bounds, p.1.instantiate b ∈ b.binders := by
      intro p hp
      rw [← b.instantiate_binders bs valid.1]
      exact List.mem_map.mpr ⟨p.1, in_bs p hp, rfl⟩
    change Bounded (fun ρ S => mixedMeaning equations.graph ρ S) η (make A ha) As q ↔
      Bounded (fun ρ S => mixedMeaning equations.graph ρ S) θ (make B hb) As q
    constructor
    · intro h p hp _ j hj U u hu
      obtain ⟨p, hsource, rfl⟩ := List.mem_map.mp hp
      apply (bound_types p hsource j (by omega) U u).mp
      apply h _ (List.mem_map.mpr ⟨p, hsource, rfl⟩) (mem_a p hsource) j hj U u
      rw [assigned p.1 (in_bs p hsource)]
      exact hu
    · intro h p hp _ j hj U u hu
      obtain ⟨p, hsource, rfl⟩ := List.mem_map.mp hp
      apply (bound_types p hsource j (by omega) U u).mpr
      apply h _ (List.mem_map.mpr ⟨p, hsource, rfl⟩) (mem_b p hsource) j hj U u
      rw [← assigned p.1 (in_bs p hsource)]
      exact hu
  · have exprs : ∀ es : List (Expression equations.signature equations.signature[head]),
        Agree (mixedMeaning equations.graph (assign η a.binders As) (es.flatMap (Expression.instantiate a)))
          (mixedMeaning equations.graph (assign θ b.binders As) (es.flatMap (Expression.instantiate b))) n := by
      intro es
      apply mixed_flatMap_agree
      intro e _
      exact equations.signature_expression_agree apps a b rfl η θ args As hlen e.1 e.2.1 e.2.1 e.2.2
    let tc : Clause (List (Expression equations.signature equations.signature[head])) :=
      if construct then .ctors (sigs.map ctorOf) (rests.map ctorRestOf) else .arrs sigs rests
    have hbody : ∀ C hc, (make C hc).body =
        tc.map (fun es => es.flatMap (Expression.instantiate (Scope.mk head C hc))) := by
      intro C hc
      cases construct
      · rfl
      · simp only [tc, make, SchemeRow.body, if_true, Clause.map, List.map_map]
        rfl
    rw [instance_body, instance_body, hbody A ha, hbody B hb]
    exact mapped_sem_agree equations.graph (assign η a.binders As) (assign θ b.binders As)
      _ _ (fun es => Agree.mono (exprs es) hq) tc (trunc q hq W) v

/-- Every admissible equation head preserves value meaning at the current
level when its arguments agree below that level. -/
theorem Equations.values_step (equations : Equations) (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (head : a.head = b.head)
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (W : WorldT n) (v : Val) :
    mixedValues equations.graph η [a.label] n W v ↔
      mixedValues equations.graph θ [b.label] n W v := by
  rcases a with ⟨ha, A, va⟩
  rcases b with ⟨hb, B, vb⟩
  cases head
  simp only [mixedValues, Tower.setSem, List.mem_singleton, exists_eq_left]
  cases body : (equations.body ha).1 with
  | clauses cs => exact equations.clauses_step apps ha A B va vb η θ args cs body W v
  | scheme bs sigs bounds rests resolution construct =>
    exact equations.scheme_step apps ha A B va vb η θ args bs sigs bounds rests resolution construct body W v
  | param label name kind =>
    have h := (equations.body ha).2
    simp [body, RowTemplate.wellBound] at h
  | meet bs cs also =>
    have h := (equations.body ha).2
    simp [body, RowTemplate.wellBound] at h

mutual
/-- Template values at the current level need argument agreement at that
level, but nested applications consume only agreement below it. A meet reads
its parts' values at the same level. -/
theorem Tree.instantiate_values (equations : Equations) (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments (n + 1))
    (locals : allowLocals = true → ∀ i (ha : i < equations.signature[a.head].binders.length)
      (hb : i < equations.signature[b.head].binders.length),
      Agree (mixedMeaning equations.graph η [a.bound ⟨i, ha⟩])
        (mixedMeaning equations.graph θ [b.bound ⟨i, hb⟩]) (n + 1))
    (t : Tree) (va : t.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : t.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : t.lexical allowLocals = true) (W : WorldT n) (v : Val) :
    mixedValues equations.graph η ((Tree.instantiate a t va).1.labels (Tree.instantiate a t va).2) n W v ↔
      mixedValues equations.graph θ ((Tree.instantiate b t vb).1.labels (Tree.instantiate b t vb).2) n W v := by
  cases t with
  | bound h ts slot => simp [Tree.lexical] at lex
  | var o i k => simp [Tree.lexical] at lex
  | argument i =>
    have h := args.2 i
      (by have := of_decide_eq_true va; simpa only [a.arity] using this)
      (by have := of_decide_eq_true vb; simpa only [b.arity] using this) n (by omega) W (.inl v)
    change mixedValues equations.graph η _ n W v ↔
      mixedValues equations.graph θ _ n W v at h
    simpa only [Tree.instantiate, Types.labels_ofList] using h
  | «local» i => exact locals lex i (of_decide_eq_true va) (of_decide_eq_true vb) n (by omega) W (.inl v)
  | app h ts =>
    let oa := Args.instantiate a ts (Bool.and_eq_true_iff.mp va).2
    let ob := Args.instantiate b ts (Bool.and_eq_true_iff.mp vb).2
    have ca : (Tree.app h oa.1).scoped equations.signature 0 0 = true := by
      have hv := (Tree.instantiate a (.app h ts) va).2
      simpa only [Tree.instantiate, Types.scoped, Bool.and_true] using hv
    have cb : (Tree.app h ob.1).scoped equations.signature 0 0 = true := by
      have hv := (Tree.instantiate b (.app h ts) vb).2
      simpa only [Tree.instantiate, Types.scoped, Bool.and_true] using hv
    let sa := Scope.ofRaw h oa.1 (Bool.and_eq_true_iff.mp ca).1 oa.2.1
    let sb := Scope.ofRaw h ob.1 (Bool.and_eq_true_iff.mp cb).1 ob.2.1
    have hr := Args.instantiate_agree equations apps a b η θ (args.mono (by omega))
      (fun h i hi hj => PositiveGraphs.Agree.mono (locals h i hi hj) (by omega)) ts
      (Bool.and_eq_true_iff.mp va).2 (Bool.and_eq_true_iff.mp vb).2 lex
    have hs := equations.values_step apps sa sb η θ rfl hr W v
    dsimp only [sa, sb] at hs
    simp only [Scope.label, Scope.ofRaw_args] at hs
    simpa only [Scope.ofRaw, Tree.instantiate, Types.labels, oa, ob] using hs
  | meet ps =>
    rw [Tree.instantiate_meet_labels, Tree.instantiate_meet_labels, equations.distribute_values,
      equations.distribute_values]
    have hp := Types.instantiateParts_values equations apps a b η θ args locals ps
      (Bool.and_eq_true_iff.mp va).1 (Bool.and_eq_true_iff.mp vb).1 lex W v
    refine and_congr_right fun _ => ⟨fun h B hB => ?_, fun h A hA => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
      exact (hp.2 i (by omega) hi).mp (h _ (List.getElem_mem (by omega)))
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
      exact (hp.2 i hi (by omega)).mpr (h _ (List.getElem_mem (by omega)))

theorem Types.instantiateParts_values (equations : Equations) (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments (n + 1))
    (locals : allowLocals = true → ∀ i (ha : i < equations.signature[a.head].binders.length)
      (hb : i < equations.signature[b.head].binders.length),
      Agree (mixedMeaning equations.graph η [a.bound ⟨i, ha⟩])
        (mixedMeaning equations.graph θ [b.bound ⟨i, hb⟩]) (n + 1))
    (ts : Types) (va : ts.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : ts.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : ts.lexical allowLocals = true) (W : WorldT n) (v : Val) :
    (Types.instantiateParts a ts va).length = (Types.instantiateParts b ts vb).length ∧
    ∀ i (ha : i < (Types.instantiateParts a ts va).length)
      (hb : i < (Types.instantiateParts b ts vb).length),
      (mixedValues equations.graph η (Types.instantiateParts a ts va)[i] n W v ↔
        mixedValues equations.graph θ (Types.instantiateParts b ts vb)[i] n W v) := by
  cases ts with
  | nil => exact ⟨rfl, fun i hi _ => by simp [Types.instantiateParts] at hi⟩
  | cons t ts =>
    have hh := Tree.instantiate_values equations apps a b η θ args locals t
      (Bool.and_eq_true_iff.mp va).1 (Bool.and_eq_true_iff.mp vb).1 (Bool.and_eq_true_iff.mp lex).1 W v
    have ht := Types.instantiateParts_values equations apps a b η θ args locals ts
      (Bool.and_eq_true_iff.mp va).2 (Bool.and_eq_true_iff.mp vb).2 (Bool.and_eq_true_iff.mp lex).2 W v
    refine ⟨by simp only [Types.instantiateParts, List.length_cons, ht.1], ?_⟩
    intro i hi hj
    cases i with
    | zero => exact hh
    | succ i =>
      exact ht.2 i
        (by simpa only [Types.instantiateParts, List.length_cons, Nat.succ_lt_succ_iff] using hi)
        (by simpa only [Types.instantiateParts, List.length_cons, Nat.succ_lt_succ_iff] using hj)
end

private theorem values_flatMap_congr (G : NormalGraph ι) (η θ : MixedAssignment ι)
    (f g : α → List ι) (es : List α) (W : WorldT n) (v : Val)
    (h : ∀ e ∈ es, mixedValues G η (f e) n W v ↔ mixedValues G θ (g e) n W v) :
    mixedValues G η (es.flatMap f) n W v ↔ mixedValues G θ (es.flatMap g) n W v := by
  change mixedMeaning G η (es.flatMap f) n W (.inl v) ↔
    mixedMeaning G θ (es.flatMap g) n W (.inl v)
  rw [mixedMeaning_union G η (es.flatMap f), mixedMeaning_union G θ (es.flatMap g)]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨i, ⟨e, he, hi⟩, hv⟩
    have hv' := (mixedMeaning_union G η (f e) n W (.inl v)).mpr ⟨i, hi, hv⟩
    have hw := (h e he).mp hv'
    obtain ⟨j, hj, hw⟩ := (mixedMeaning_union G θ (g e) n W (.inl v)).mp hw
    exact ⟨j, ⟨e, he, hj⟩, hw⟩
  · rintro ⟨i, ⟨e, he, hi⟩, hv⟩
    have hv' := (mixedMeaning_union G θ (g e) n W (.inl v)).mpr ⟨i, hi, hv⟩
    have hw := (h e he).mpr hv'
    obtain ⟨j, hj, hw⟩ := (mixedMeaning_union G η (f e) n W (.inl v)).mp hw
    exact ⟨j, ⟨e, he, hj⟩, hw⟩

/-- Argument packs read their element values at the current level. Those
values are handled by `values_step`, rather than assuming the conclusion of
mixed application congruence at this level. -/
theorem Equations.arguments_step (equations : Equations) (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (head : a.head = b.head)
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments (n + 1))
    (W : WorldT n) (vs : List Val) :
    mixedArgs equations.graph η [a.label] n W vs ↔
      mixedArgs equations.graph θ [b.label] n W vs := by
  simp only [mixedArgs, graphArguments, List.mem_singleton, exists_eq_left, NormalGraph.listParam,
    equations.kind_application a, equations.kind_application b]
  rcases a with ⟨ha, A, va⟩
  rcases b with ⟨hb, B, vb⟩
  cases head
  let a : Scope equations.signature := ⟨ha, A, va⟩
  let b : Scope equations.signature := ⟨ha, B, vb⟩
  cases body : (equations.body ha).1 with
  | clauses cs =>
    have empty : equations.signature[ha].binders = [] := by
      have h := (equations.body ha).2
      simpa [body, RowTemplate.wellBound] using h
    have exprs (es : List (Expression equations.signature equations.signature[ha])) (v : Val) :
        mixedValues equations.graph η (es.flatMap (Expression.instantiate a)) n W v ↔
          mixedValues equations.graph θ (es.flatMap (Expression.instantiate b)) n W v := by
      apply values_flatMap_congr
      intro e _
      apply Tree.instantiate_values equations apps a b η θ args _ e.1 e.2.1 e.2.1 e.2.2 W v
      intro _ i hi hj
      have hlen := congrArg List.length empty
      have hi' : i < equations.signature[ha].binders.length := hi
      simp only [List.length_nil] at hlen
      omega
    have row (C) (hc : C.length = equations.signature[ha].parameters) :
        equations.graph (Scope.mk ha C hc).label =
          cs.map (Clause.map (fun es => es.flatMap (Expression.instantiate ⟨ha, C, hc⟩))) := by
      simp [NormalGraph.clauses, NormalGraph.plain, NormalGraph.params, Equations.graph,
        NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Template.instantiate, body, GraphRow.map, GraphRow.union]
    rw [row A va, row B vb]
    have congr (c : Clause (List (Expression equations.signature equations.signature[ha]))) :
        clauseArguments (mixedValues equations.graph η)
          (c.map (fun es => es.flatMap (Expression.instantiate a))) n W vs ↔
        clauseArguments (mixedValues equations.graph θ)
          (c.map (fun es => es.flatMap (Expression.instantiate b))) n W vs := by
      rw [clauseArguments_map, clauseArguments_map]
      exact clauseArguments_congr _ _ c n W exprs vs
    constructor
    · rintro ⟨c', hc', hv⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
      exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, (congr c).mp hv⟩
    · rintro ⟨c', hc', hv⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
      exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, (congr c).mpr hv⟩
  | scheme bs sigs bounds rests resolution =>
    simp [NormalGraph.clauses, NormalGraph.plain, NormalGraph.params, Equations.graph,
      NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Template.instantiate, body, GraphRow.map, GraphRow.union]
  | param label name kind =>
    have h := (equations.body ha).2
    simp [body, RowTemplate.wellBound] at h
  | meet bs cs also =>
    have h := (equations.body ha).2
    simp [body, RowTemplate.wellBound] at h

/-- Application congruence for the existing mixed semantics. The step first
compares values, then argument packs at that same level; no semantic hypothesis
is admitted from a certificate or a producer. -/
theorem Equations.applications_agree (equations : Equations) (n : Nat) :
    equations.ApplicationsAgree n := by
  induction n with
  | zero => intro a b η θ head args m hm; omega
  | succ n ih =>
    intro a b η θ head args m hm W x
    by_cases hmn : m < n
    · exact ih a b η θ head (args.mono (by omega)) m hmn W x
    · have he : m = n := by omega
      subst m
      cases x with
      | inl v => exact equations.values_step ih a b η θ head (args.mono (by omega)) W v
      | inr vs => exact equations.arguments_step ih a b η θ head args W vs

/-- Equal semantic arguments give equal recursive application meanings,
including quantified heads, effects, and argument packs. -/
theorem Equations.application_congr (equations : Equations)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (head : a.head = b.head) (lengths : a.arguments.length = b.arguments.length)
    (args : ∀ i (ha : i < a.arguments.length) (hb : i < b.arguments.length),
      mixedMeaning equations.graph η a.arguments[i] = mixedMeaning equations.graph θ b.arguments[i]) :
    mixedMeaning equations.graph η [a.label] = mixedMeaning equations.graph θ [b.label] := by
  funext n W x
  apply propext
  apply equations.applications_agree (n + 1) a b η θ head ?_ n (by omega) W x
  refine ⟨lengths, ?_⟩
  intro i hi hj m hm U u
  rw [args i hi hj]

#print axioms Equations.arguments_assign
#print axioms Equations.locals_assign
#print axioms Equations.signature_expression_agree
#print axioms Equations.bound_expression_agree
#print axioms Equations.clauses_step
#print axioms Equations.scheme_step
#print axioms Equations.application_congr

end Verification.EquationGraphs
