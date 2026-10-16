import Verification.Types.EquationCongruence

/-! Substitution traverses finite application syntax, never recursive rows.
An existing bound name is atomic; an application's changed arguments determine
its new owned binders when its equation is unfolded. -/
namespace Verification.EquationGraphs
open PositiveGraphs PositiveRules PositiveNormalization

-- Use the same equality-backed lookup as the generic instantiation checker.
local instance : BEq (Label sig) := instBEqOfDecidableEq

mutual
/-- Replace parameter names, recursing through captured application arguments.
The supplied map is consulted only for parameters, never for applications. -/
def Tree.substitute (σ : Label sig → List (Label sig)) (t : Tree)
    (valid : t.scoped sig 0 0 = true) : List (Label sig) :=
  match t with
  | .app h ts =>
    let scope := Scope.ofRaw h ts (Bool.and_eq_true_iff.mp valid).1 (Bool.and_eq_true_iff.mp valid).2
    let args := Args.substitute σ ts (Bool.and_eq_true_iff.mp valid).2
    [(Scope.mk scope.head args.1 (by
      rw [args.2]
      exact (Args.labels_length ts _).symm.trans scope.arity)).label]
  | .bound h ts i => σ ⟨.bound h ts i, valid⟩
  | .var o i k => σ ⟨.var o i k, valid⟩
  | .meet ps =>
    -- Intersection distributes over each part's substituted union.
    (choices (Types.substituteParts σ ps (Bool.and_eq_true_iff.mp valid).1)).map Label.meetOf
  | .argument i => False.elim (by simp [Tree.scoped] at valid)
  | .local i => False.elim (by simp [Tree.scoped] at valid)

/-- Each part of a meet substituted to a union. -/
def Types.substituteParts (σ : Label sig → List (Label sig)) (ts : Types)
    (valid : ts.scoped sig 0 0 = true) : List (List (Label sig)) :=
  match ts with
  | .nil => []
  | .cons t ts => Tree.substitute σ t (Bool.and_eq_true_iff.mp valid).1 ::
    Types.substituteParts σ ts (Bool.and_eq_true_iff.mp valid).2

def Types.substitute (σ : Label sig → List (Label sig)) (ts : Types)
    (valid : ts.scoped sig 0 0 = true) : List (Label sig) :=
  match ts with
  | .nil => []
  | .cons t ts => Tree.substitute σ t (Bool.and_eq_true_iff.mp valid).1 ++
    Types.substitute σ ts (Bool.and_eq_true_iff.mp valid).2

def Args.substitute (σ : Label sig → List (Label sig)) (ts : Args)
    (valid : ts.scoped sig 0 0 = true) :
    { args : List (List (Label sig)) // args.length = ts.toList.length } :=
  match ts with
  | .nil => ⟨[], rfl⟩
  | .cons t ts =>
    let tail := Args.substitute σ ts (Bool.and_eq_true_iff.mp valid).2
    ⟨Types.substitute σ t (Bool.and_eq_true_iff.mp valid).1 :: tail.1,
      congrArg Nat.succ tail.2⟩
end

def Label.substitute (σ : Label sig → List (Label sig)) (l : Label sig) : List (Label sig) :=
  Tree.substitute σ l.1 l.2

/-- A semantic parameter map is enough to justify the complete structural
substitution, because application congruence covers every recursive equation. -/
def Equations.ParameterImages (equations : Equations)
    (η θ : MixedAssignment (Label equations.signature))
    (σ : Label equations.signature → List (Label equations.signature)) : Prop :=
  ∀ p, equations.graph.params p = true →
    mixedMeaning equations.graph η [p] = mixedMeaning equations.graph θ (σ p)

private theorem mixed_append (G : NormalGraph ι) (η : MixedAssignment ι)
    (S T : List ι) (n : Nat) (W : WorldT n) (x : ParameterSpace.mixed.Carrier) :
    mixedMeaning G η (S ++ T) n W x ↔
      mixedMeaning G η S n W x ∨ mixedMeaning G η T n W x := by
  rw [mixedMeaning_union G η (S ++ T), mixedMeaning_union G η S, mixedMeaning_union G η T]
  simp only [List.mem_append, or_and_right, exists_or]

mutual
theorem Tree.substitute_meaning (equations : Equations)
    (η θ : MixedAssignment (Label equations.signature)) (σ)
    (images : equations.ParameterImages η θ σ)
    (t : Tree) (valid : t.scoped equations.signature 0 0 = true) :
    mixedMeaning equations.graph η [⟨t, valid⟩] =
      mixedMeaning equations.graph θ (Tree.substitute σ t valid) := by
  cases t with
  | bound h ts i =>
    apply images
    simp [NormalGraph.params, Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Label.view]
  | var o i k =>
    apply images
    simp [NormalGraph.params, Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Label.view]
  | argument i => simp [Tree.scoped] at valid
  | «local» i => simp [Tree.scoped] at valid
  | app h ts =>
    let a := Scope.ofRaw h ts (Bool.and_eq_true_iff.mp valid).1 (Bool.and_eq_true_iff.mp valid).2
    let args := Args.substitute σ ts (Bool.and_eq_true_iff.mp valid).2
    let b : Scope equations.signature := ⟨a.head, args.1, by
      rw [args.2]
      exact (Args.labels_length ts _).symm.trans a.arity⟩
    have eqargs := Args.substitute_meaning equations η θ σ images ts (Bool.and_eq_true_iff.mp valid).2
    have he := equations.application_congr a b η θ rfl
      ((Args.labels_length ts _).trans args.2.symm) eqargs
    have source : a.label = (⟨.app h ts, valid⟩ : Label equations.signature) := by
      apply Subtype.ext
      simp only [a, Scope.label, Scope.ofRaw_args]
      rfl
    rw [source] at he
    exact he
  | meet ps =>
    have hp := Types.substituteParts_meaning equations η θ σ images ps (Bool.and_eq_true_iff.mp valid).1
    funext n W x
    apply propext
    cases x with
    | inr vs =>
      exact iff_of_false (equations.meet_noArguments η ps valid)
        (equations.distribute_noArguments θ _)
    | inl v =>
      rw [mixedMeaning_single_value, equations.meet_denote]
      change _ ↔ mixedValues _ θ _ n W v
      simp only [Tree.substitute]
      rw [equations.distribute_values]
      refine and_congr_right fun _ => ⟨fun h A hA => ?_, fun h q hq => ?_⟩
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
        have hl : i < (ps.labels (Bool.and_eq_true_iff.mp valid).1).length := by omega
        have he := congrFun (congrFun (congrFun (hp.2 i hl hi) n) W) (.inl v)
        change _ = mixedValues _ θ _ n W v at he
        rw [← he, mixedMeaning_single_value]
        exact h _ (List.getElem_mem hl)
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
        have hj : i < (Types.substituteParts σ ps (Bool.and_eq_true_iff.mp valid).1).length := by omega
        have he := congrFun (congrFun (congrFun (hp.2 i hi hj) n) W) (.inl v)
        change _ = mixedValues _ θ _ n W v at he
        rw [← mixedMeaning_single_value, he]
        exact h _ (List.getElem_mem hj)

theorem Types.substituteParts_meaning (equations : Equations)
    (η θ : MixedAssignment (Label equations.signature)) (σ)
    (images : equations.ParameterImages η θ σ)
    (ts : Types) (valid : ts.scoped equations.signature 0 0 = true) :
    (ts.labels valid).length = (Types.substituteParts σ ts valid).length ∧
    ∀ i (ha : i < (ts.labels valid).length) (hb : i < (Types.substituteParts σ ts valid).length),
      mixedMeaning equations.graph η [(ts.labels valid)[i]] =
        mixedMeaning equations.graph θ (Types.substituteParts σ ts valid)[i] := by
  cases ts with
  | nil => exact ⟨rfl, fun i hi _ => by simp [Types.labels] at hi⟩
  | cons t ts =>
    have hh := Tree.substitute_meaning equations η θ σ images t (Bool.and_eq_true_iff.mp valid).1
    have ht := Types.substituteParts_meaning equations η θ σ images ts (Bool.and_eq_true_iff.mp valid).2
    refine ⟨by simp only [Types.labels, Types.substituteParts, List.length_cons, ht.1], ?_⟩
    intro i hi hj
    cases i with
    | zero => exact hh
    | succ i =>
      exact ht.2 i
        (by simpa only [Types.labels, List.length_cons, Nat.succ_lt_succ_iff] using hi)
        (by simpa only [Types.substituteParts, List.length_cons, Nat.succ_lt_succ_iff] using hj)

theorem Types.substitute_meaning (equations : Equations)
    (η θ : MixedAssignment (Label equations.signature)) (σ)
    (images : equations.ParameterImages η θ σ)
    (ts : Types) (valid : ts.scoped equations.signature 0 0 = true) :
    mixedMeaning equations.graph η (ts.labels valid) =
      mixedMeaning equations.graph θ (Types.substitute σ ts valid) := by
  cases ts with
  | nil =>
    funext n W x
    apply propext
    cases x <;> simp [Types.labels, Types.substitute, mixedMeaning, mixedParameters, graphArguments, Tower.setSem]
  | cons t ts =>
    have hh := Tree.substitute_meaning equations η θ σ images t (Bool.and_eq_true_iff.mp valid).1
    have ht := Types.substitute_meaning equations η θ σ images ts (Bool.and_eq_true_iff.mp valid).2
    funext n W x
    apply propext
    change mixedMeaning equations.graph η ([⟨t, _⟩] ++ ts.labels _) n W x ↔ _
    rw [mixed_append, Types.substitute, mixed_append, hh, ht]

theorem Args.substitute_meaning (equations : Equations)
    (η θ : MixedAssignment (Label equations.signature)) (σ)
    (images : equations.ParameterImages η θ σ)
    (ts : Args) (valid : ts.scoped equations.signature 0 0 = true) :
    ∀ i (ha : i < (ts.labels valid).length) (hb : i < (Args.substitute σ ts valid).1.length),
      mixedMeaning equations.graph η (ts.labels valid)[i] =
        mixedMeaning equations.graph θ (Args.substitute σ ts valid).1[i] := by
  cases ts with
  | nil => intro i hi; simp [Args.labels] at hi
  | cons t ts =>
    intro i hi hj
    cases i with
    | zero => exact Types.substitute_meaning equations η θ σ images t (Bool.and_eq_true_iff.mp valid).1
    | succ i =>
      exact Args.substitute_meaning equations η θ σ images ts (Bool.and_eq_true_iff.mp valid).2 i
        (by simpa only [Args.labels, List.length_cons, Nat.succ_lt_succ_iff] using hi)
        (by simpa only [Args.substitute, List.length_cons, Nat.succ_lt_succ_iff] using hj)
end

/-- Substitution's semantic equation, for values and argument packs together. -/
theorem Label.substitute_meaning (equations : Equations)
    (η θ : MixedAssignment (Label equations.signature)) (σ)
    (images : equations.ParameterImages η θ σ) (l : Label equations.signature) :
    mixedMeaning equations.graph η [l] = mixedMeaning equations.graph θ (l.substitute σ) :=
  Tree.substitute_meaning equations η θ σ images l.1 l.2

/-- A context leaves unmapped parameters unchanged. A mapped parameter is
replaced simultaneously, without substituting again inside its replacement. -/
def parameterReplacement (κ : Ctx (Label sig)) (p : Label sig) : List (Label sig) :=
  (κ.lookup p).getD [p]

/-- The existing kind check justifies parameter replacement at both semantic
components. This does not infer a new contract for an argument pack. -/
theorem Equations.assignment_parameterImages (equations : Equations)
    (η : MixedAssignment (Label equations.signature)) (bs) (θs)
    (hlen : θs.length = bs.length) (kinds : instKinds equations.graph bs θs = true) :
    equations.ParameterImages
      (assign η bs (θs.map fun U => ⟨mixedMeaning equations.graph η U,
        mixedMeaning_valid equations.graph η U⟩)) η (parameterReplacement (bs.zip θs)) := by
  intro p hp
  obtain ⟨kind, hk⟩ : ∃ kind, equations.graph.parameterKinds p = some kind := by
    simpa [NormalGraph.params, Option.isSome_iff_exists] using hp
  have hr := mixed_assignment_substitution equations.graph η bs θs hlen kinds [p]
  cases lookup : (bs.zip θs).lookup p with
  | some U =>
    simpa only [parameterReplacement, lookup, Option.getD_some] using
      mixed_parameter_image equations.graph (bs.zip θs) _ η p kind U hk lookup hr
  | none =>
    rw [mixedMeaning_parameter _ _ _ _ hk]
    simp only [parameterReplacement, lookup, Option.getD_none]
    rw [mixedMeaning_parameter _ _ _ _ hk]
    have he := hr p (by simp)
    rw [lookup] at he
    change selectParameter (equations.graph.parameterKinds p) _ =
      selectParameter (equations.graph.parameterKinds p) _ at he
    simpa only [hk] using he

/-- A finite instantiation witness names only the images used at a call.
Every image is checked against structural substitution of complete equations;
no traversal frontier or omitted recursive row is trusted. -/
def substitutionTableOk (tbl : InstTable (Label sig)) : Bool :=
  tbl.all fun (l, κ, image) => decide (l.substitute (parameterReplacement κ) = image)

/-- Equation witnesses discharge the same semantic obligation as finite closed
tables. This theorem alone does not add a new source/CLI acceptance path. -/
theorem Equations.substitutionTable_instanceImages (equations : Equations)
    (η : MixedAssignment (Label equations.signature)) (bs) (θs)
    (tbl : InstTable (Label equations.signature))
    (hlen : θs.length = bs.length) (kinds : instKinds equations.graph bs θs = true)
    (checked : substitutionTableOk tbl = true) :
    InstanceImages equations.graph η bs θs tbl := by
  have images := equations.assignment_parameterImages η bs θs hlen kinds
  intro S S' hS
  funext n W x
  apply propext
  rw [mixedMeaning_union, mixedMeaning_union]
  apply tyImg_iff hS
  intro l hl T hT
  have entry := of_decide_eq_true (List.all_eq_true.mp checked _ (entryImg_mem hT))
  have he := Label.substitute_meaning equations _ η _ images l
  rw [entry] at he
  rw [he]
  exact mixedMeaning_union equations.graph η T n W x

/-- A table whose every image is its label's structural substitution, or a
type `equiv` proves to mean the same at every assignment. -/
def substitutionTableOkUpTo (equiv : List (Label sig) → List (Label sig) → Bool)
    (tbl : InstTable (Label sig)) : Bool :=
  tbl.all fun (l, κ, image) =>
    decide (l.substitute (parameterReplacement κ) = image) ||
      equiv (l.substitute (parameterReplacement κ)) image

/-- Images up to proved equivalence discharge the same obligation: an image
means what the substitution means. -/
theorem Equations.substitutionTableUpTo_instanceImages (equations : Equations)
    (equiv : List (Label equations.signature) → List (Label equations.signature) → Bool)
    (hequiv : ∀ X Y, equiv X Y = true → ∀ η, mixedMeaning equations.graph η X = mixedMeaning equations.graph η Y)
    (η : MixedAssignment (Label equations.signature)) (bs) (θs)
    (tbl : InstTable (Label equations.signature))
    (hlen : θs.length = bs.length) (kinds : instKinds equations.graph bs θs = true)
    (checked : substitutionTableOkUpTo equiv tbl = true) :
    InstanceImages equations.graph η bs θs tbl := by
  have images := equations.assignment_parameterImages η bs θs hlen kinds
  intro S S' hS
  funext n W x
  apply propext
  rw [mixedMeaning_union, mixedMeaning_union]
  apply tyImg_iff hS
  intro l hl T hT
  have entry := List.all_eq_true.mp checked _ (entryImg_mem hT)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at entry
  have he := Label.substitute_meaning equations _ η _ images l
  rcases entry with entry | entry
  · rw [entry] at he
    rw [he]
    exact mixedMeaning_union equations.graph η T n W x
  · rw [he, hequiv _ _ entry η]
    exact mixedMeaning_union equations.graph η T n W x

#print axioms Equations.substitutionTableUpTo_instanceImages
#print axioms Label.substitute_meaning
#print axioms Equations.substitutionTable_instanceImages

end Verification.EquationGraphs
