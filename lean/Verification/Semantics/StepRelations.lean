import Verification.Semantics.IndexFacts

/-! **Relational composition** (the note "Tolerant frames", rule Call;
ARITHMETIC.md, "Two-state postconditions"): the linear facts after a step,
from the linear facts before it and a relation between the two states.

A step relates the state before it, `ρ, h`, and the state after it,
`ρ', h'`, both read at one entry state `ε` (the run's own, fixed). A
relation's variables are terms read in either state (`StepVar`): a
`before` variable is a logical name of a value of the state before the
step, no slot of any environment. The facts after the step are the facts
before it with each term the step keeps read after it, and each term it
changes replaced by its value the relation defines (`b = k - rest`), or
eliminated by Fourier–Motzkin where the relation bounds it; what remains
names after-terms alone. -/
namespace Verification.HeapKnowledge

variable {ε : EntryState}

/-- A variable of a relation between the states before and after a step: a
term read before the step, or a term read after it. -/
inductive StepVar where
  | before (t : Term)
  | after (t : Term)
  deriving DecidableEq, Repr, Hashable

namespace StepVar

/-- An order on variables: every before-variable first, each class by the
order of terms. -/
def lt : StepVar → StepVar → Bool
  | .before a, .before b => a.before b
  | .before _, .after _ => true
  | .after _, .before _ => false
  | .after a, .after b => a.before b

instance : LT StepVar := ⟨fun a b => a.lt b = true⟩

instance : DecidableRel (α := StepVar) (· < ·) := fun a b => inferInstanceAs (Decidable (a.lt b = true))

/-- What a variable denotes: a before-term at `ρ, h`, an after-term at
`ρ', h'`, both at the entry state `ε`. -/
def value (ε : EntryState) (ρ : Env) (h : Heap) (ρ' : Env) (h' : Heap) : StepVar → Int
  | .before t => termValuation ε ρ h t
  | .after t => termValuation ε ρ' h' t

/-- Whether a variable is a before-variable. -/
def isBefore : StepVar → Bool
  | .before _ => true
  | .after _ => false

end StepVar

/-- **A step's relation**: linear facts over before- and after-terms, and
after-terms the step states defined. -/
structure StepRelation where
  facts : List (Linear.Fact StepVar)
  defined : List Term := []

/-- A relation holds of a step from `ρ, h` to `ρ', h'`: each fact holds
wherever its before-terms denote integers, and each `defined` term denotes
one after the step wherever all its facts' before-terms do. -/
def StepRelation.Holds (R : StepRelation) (ε : EntryState) (ρ : Env) (h : Heap) (ρ' : Env) (h' : Heap) : Prop :=
  (∀ F ∈ R.facts, (∀ t, StepVar.before t ∈ F.vars → (termValue ε ρ h t).isSome) →
    F.Holds (StepVar.value ε ρ h ρ' h')) ∧
  ((∀ F ∈ R.facts, ∀ t, StepVar.before t ∈ F.vars → (termValue ε ρ h t).isSome) →
    ∀ t ∈ R.defined, (termValue ε ρ' h' t).isSome)

/-! ## Substituting a defined variable -/

/-- The coefficient a form gives a variable, summed over its occurrences. -/
def Form.coeffOf (b : StepVar) (G : Linear.Form StepVar) : Int :=
  Linear.Form.eval (fun x => if x = b then 1 else 0) G

/-- A form without a variable's occurrences. -/
def Form.without (b : StepVar) : Linear.Form StepVar → Linear.Form StepVar
  | [] => []
  | (x, c) :: t => if x = b then Form.without b t else (x, c) :: Form.without b t

theorem Form.eval_split (v : StepVar → Int) (b : StepVar) :
    ∀ G : Linear.Form StepVar, Linear.Form.eval v G = Form.coeffOf b G * v b + Linear.Form.eval v (Form.without b G)
  | [] => by simp [Form.coeffOf, Form.without, Linear.Form.eval]
  | (x, c) :: t => by
    have ih := Form.eval_split v b t
    simp only [Form.coeffOf] at ih
    by_cases hx : x = b
    · subst hx
      simp only [Form.coeffOf, Form.without, Linear.Form.eval, if_true, Int.mul_one, ih, Int.add_mul]
      omega
    · simp only [Form.coeffOf, Form.without, Linear.Form.eval, hx, if_false, Int.mul_zero, Int.zero_add, ih]
      omega

/-- A form with each occurrence `(b, c)` replaced by `rest` scaled by `-c`:
`b` read as `k - rest`, the bound moved by `c * k` (`substFact`). -/
def Form.subst (b : StepVar) (rest : Linear.Form StepVar) : Linear.Form StepVar → Linear.Form StepVar
  | [] => []
  | (x, c) :: t => (if x = b then rest.scale (-c) else [(x, c)]) ++ Form.subst b rest t

theorem Form.eval_subst (v : StepVar → Int) (b : StepVar) (rest : Linear.Form StepVar) (k : Int)
    (hb : v b = k - Linear.Form.eval v rest) :
    ∀ G : Linear.Form StepVar, Linear.Form.eval v (Form.subst b rest G) = Linear.Form.eval v G - Form.coeffOf b G * k
  | [] => by simp [Form.subst, Form.coeffOf, Linear.Form.eval]
  | (x, c) :: t => by
    have ih := Form.eval_subst v b rest k hb t
    simp only [Form.coeffOf] at ih
    by_cases hx : x = b
    · subst hx
      simp only [Form.subst, Linear.Form.eval_append, ih, Form.coeffOf, Linear.Form.eval, if_true,
        Linear.Form.eval_scale, Int.mul_one]
      rw [hb, Int.mul_sub, Int.add_mul, Int.neg_mul]
      omega
    · simp only [Form.subst, Linear.Form.eval_append, ih, Form.coeffOf, Linear.Form.eval, hx, if_false,
        Int.add_zero, Int.mul_zero, Int.zero_add]
      omega

/-- A fact with the variable `b` read as `k - rest`. -/
def substFact (b : StepVar) (rest : Linear.Form StepVar) (k : Int) : Linear.Fact StepVar → Linear.Fact StepVar
  | .le G d => .le (Form.subst b rest G) (d - Form.coeffOf b G * k)
  | .ne G d => .ne (Form.subst b rest G) (d - Form.coeffOf b G * k)

theorem substFact_holds {v : StepVar → Int} {b : StepVar} {rest : Linear.Form StepVar} {k : Int}
    (hb : v b = k - Linear.Form.eval v rest) {F : Linear.Fact StepVar} (hF : F.Holds v) : (substFact b rest k F).Holds v := by
  cases F with
  | le G d => simp only [substFact, Linear.Fact.Holds, Form.eval_subst v b rest k hb] at hF ⊢; omega
  | ne G d => simp only [substFact, Linear.Fact.Holds, Form.eval_subst v b rest k hb] at hF ⊢; omega

/-- **The definition of a variable in held facts**: a pair `G ≤ k` and
`G' ≤ -k` with `G'` the negation of `G` (equal normal forms), `b`'s
coefficient in `G` one; then `b = k - rest`, `rest` the rest of `G`. The two
facts' positions are returned with it. -/
def definitionOf (known : List (Linear.Fact StepVar)) (b : StepVar) :
    Option (Linear.Form StepVar × Int × Nat × Nat) :=
  let les := (List.range known.length).filterMap fun i => match (known[i]? : Option (Linear.Fact StepVar)) with
    | some (.le G k) => some (i, G, k)
    | _ => none
  les.findSome? fun (i, G, k) =>
    if Form.coeffOf b G = 1 then
      (les.find? fun (_, G', k') => k' = -k && Linear.normalize G' == Linear.normalize (G.scale (-1))).map
        fun (j, _, _) => (Form.without b G, k, i, j)
    else none

theorem definitionOf_sound {v : StepVar → Int} {known : List (Linear.Fact StepVar)} {b : StepVar}
    {rest : Linear.Form StepVar} {k : Int} {i j : Nat} (hk : ∀ F ∈ known, F.Holds v)
    (hd : definitionOf known b = some (rest, k, i, j)) : v b = k - Linear.Form.eval v rest := by
  unfold definitionOf at hd
  obtain ⟨⟨i0, G, k0⟩, hm, hs⟩ := List.exists_of_findSome?_eq_some hd
  simp only at hs
  split at hs
  · rename_i hc
    obtain ⟨⟨j0, G', k'⟩, hf, he⟩ := Option.map_eq_some_iff.mp hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    have hmem : ∀ {i G k}, (i, G, k) ∈ (List.range known.length).filterMap (fun i => match (known[i]? : Option (Linear.Fact StepVar)) with
        | some (.le G k) => some (i, G, k)
        | _ => none) → (Linear.Fact.le G k).Holds v := by
      intro i G k hm
      obtain ⟨i1, -, h1⟩ := List.mem_filterMap.mp hm
      split at h1
      · rename_i G1 k1 hq
        cases h1
        exact hk _ (List.mem_of_getElem? hq)
      · cases h1
    have h1 := hmem hm
    have h2 := hmem (List.mem_of_find?_eq_some hf)
    have hc2 := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc2
    obtain ⟨hk', hn⟩ := hc2
    simp only [Linear.Fact.Holds] at h1 h2
    have hneg : Linear.Form.eval v G' = -Linear.Form.eval v G := by
      rw [← Linear.eval_normalize v G', hn, Linear.eval_normalize, Linear.Form.eval_scale]; omega
    have hsplit := Form.eval_split v b G
    rw [hc] at hsplit
    omega
  · cases hs

/-- Each fact with `b` read as `k - rest`, the two defining facts dropped. -/
def substituteAll (known : List (Linear.Fact StepVar)) (b : StepVar) (rest : Linear.Form StepVar) (k : Int)
    (i j : Nat) : List (Linear.Fact StepVar) :=
  (List.range known.length).filterMap fun n =>
    if n = i ∨ n = j then none else known[n]?.map (substFact b rest k)

theorem substituteAll_holds {v : StepVar → Int} {known : List (Linear.Fact StepVar)} {b : StepVar}
    {rest : Linear.Form StepVar} {k : Int} {i j : Nat} (hk : ∀ F ∈ known, F.Holds v)
    (hb : v b = k - Linear.Form.eval v rest) : ∀ F ∈ substituteAll known b rest k i j, F.Holds v := by
  intro F hF
  obtain ⟨n, -, hn⟩ := List.mem_filterMap.mp hF
  split at hn
  · cases hn
  · obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.mp hn
    exact substFact_holds hb (hk G (List.mem_of_getElem? hG))

/-- **Eliminating the before-variables** `xs` in turn: each by its
definition where the facts define it, by Fourier–Motzkin otherwise
(`Linear.eliminateAll`). -/
def eliminate (known : List (Linear.Fact StepVar)) : List StepVar → List (Linear.Fact StepVar)
  | [] => known
  | b :: xs => match definitionOf known b with
    | some (rest, k, i, j) => eliminate (substituteAll known b rest k i j) xs
    | none => eliminate (Linear.eliminateAll known [b]) xs

theorem eliminate_holds {v : StepVar → Int} :
    ∀ {xs : List StepVar} {known : List (Linear.Fact StepVar)}, (∀ F ∈ known, F.Holds v) →
      ∀ F ∈ eliminate known xs, F.Holds v
  | [], _, hk => hk
  | b :: xs, known, hk => by
    unfold eliminate
    split
    · rename_i rest k i j hd
      exact eliminate_holds (substituteAll_holds hk (definitionOf_sound hk hd))
    · exact eliminate_holds (Linear.eliminateAll_sound hk)

/-! ## Composition -/

/-- A term before the step as a variable: read after it where the step keeps
it (`kept`), a before-variable otherwise. -/
def keptVar (kept : Term → Option Term) (t : Term) : StepVar :=
  match kept t with
  | some t' => .after t'
  | none => .before t

/-- A relation's variable with each before-term the step keeps read after it. -/
def keptRelVar (kept : Term → Option Term) : StepVar → StepVar
  | .before t => keptVar kept t
  | .after t => .after t

/-- An after-variable's term where it is one of `defined`. -/
def definedAfter (defined : List Term) : StepVar → Option Term
  | .after t => if defined.contains t then some t else none
  | .before _ => none

/-- The terms the facts before a step name: each denotes an integer
before it. -/
def beforeTerms (before : List (Linear.Fact Term)) : List Term := before.flatMap (·.vars)

/-- Whether a relation's fact names only before-terms the facts before
name. -/
def namesBefore (bvars : List Term) (F : Linear.Fact StepVar) : Bool :=
  F.vars.all fun
    | .before t => bvars.contains t
    | .after _ => true

/-- The relation's facts naming only before-terms the facts before name,
each before-term the step keeps read after it. -/
def relOf (kept : Term → Option Term) (before : List (Linear.Fact Term)) (R : StepRelation) :
    List (Linear.Fact StepVar) :=
  (R.facts.filter (namesBefore (beforeTerms before))).filterMap (·.mapVars (some ∘ keptRelVar kept))

/-- The before-variables those facts name. -/
def namesOf (rel : List (Linear.Fact StepVar)) : List StepVar :=
  ((rel.flatMap (·.vars)).filter (·.isBefore)).eraseDups

/-- The facts before naming one of `names`, each kept term read after the
step. -/
def preOf (kept : Term → Option Term) (before : List (Linear.Fact Term)) (names : List StepVar) :
    List (Linear.Fact StepVar) :=
  (before.filterMap (·.mapVars (some ∘ keptVar kept))).filter fun F => F.vars.any names.contains

/-- The after-terms known defined: each a kept term before, and the
relation's own where all its facts name only before-terms the facts before
name. -/
def definedOf (kept : Term → Option Term) (before : List (Linear.Fact Term)) (R : StepRelation) : List Term :=
  (beforeTerms before).filterMap kept ++ (if R.facts.all (namesBefore (beforeTerms before)) then R.defined else [])

/-- **The facts after a step** (rule Call's composition): the facts
`before`, each term the step keeps read after it (`kept`), with the facts of
the relation `R` naming only before-terms the facts before define, each
before-variable they name eliminated (`eliminate`) from those facts and the
facts before naming it; each resulting fact naming after-terms alone, each
one the step keeps of a term before or the relation states defined. -/
def compose (kept : Term → Option Term) (before : List (Linear.Fact Term)) (R : StepRelation) :
    List (Linear.Fact Term) :=
  let rel := relOf kept before R
  let names := namesOf rel
  (eliminate (preOf kept before names ++ rel) names).filterMap (·.mapVars (definedAfter (definedOf kept before R)))

theorem mem_vars_defined {F : Linear.Fact Term} {ρ : Env} {h : Heap} (hF : (IndexFact.linear F).HoldsAt ε ρ h)
    {t : Term} (ht : t ∈ F.vars) : (termValue ε ρ h t).isSome := hF.1 t ht

/-- **Composition is sound** (proved): where the facts before hold before
the step, each kept term denotes after the step what it denoted before, and
the relation holds of the step, every composed fact holds after it, at the
same entry state. -/
theorem compose_holds {kept : Term → Option Term} {before : List (Linear.Fact Term)} {R : StepRelation}
    {ρ ρ' : Env} {h h' : Heap}
    (hb : ∀ F ∈ before, (IndexFact.linear F).HoldsAt ε ρ h)
    (hk : ∀ t t' n, kept t = some t' → termValue ε ρ h t = some n → termValue ε ρ' h' t' = some n)
    (hR : R.Holds ε ρ h ρ' h') :
    ∀ F ∈ compose kept before R, (IndexFact.linear F).HoldsAt ε ρ' h' := by
  let v := StepVar.value ε ρ h ρ' h'
  -- A term of a fact before is defined before.
  have hbdef : ∀ t ∈ beforeTerms before, (termValue ε ρ h t).isSome := by
    intro t ht
    obtain ⟨F, hF, ht⟩ := List.mem_flatMap.mp ht
    exact (hb F hF).1 t ht
  -- A term defined before, read through `keptVar`, denotes its value before.
  have hkv : ∀ t, (termValue ε ρ h t).isSome → v (keptVar kept t) = termValuation ε ρ h t := by
    intro t ht
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ht
    unfold keptVar
    split
    · rename_i t' ht'
      simp only [v, StepVar.value, termValuation, hk t t' n ht' hn, hn]
    · rfl
  have hnb : ∀ F, namesBefore (beforeTerms before) F = true → ∀ t, StepVar.before t ∈ F.vars →
      (termValue ε ρ h t).isSome := by
    intro F hF t ht
    have := List.all_eq_true.mp hF _ ht
    exact hbdef t (by simpa using this)
  intro F hF
  unfold compose at hF
  obtain ⟨G, hG, hGF⟩ := List.mem_filterMap.mp hF
  have hall : ∀ G ∈ eliminate (preOf kept before (namesOf (relOf kept before R)) ++ relOf kept before R)
      (namesOf (relOf kept before R)), G.Holds v := by
    refine eliminate_holds fun G hG => ?_
    rcases List.mem_append.mp hG with hG | hG
    · obtain ⟨hG, -⟩ := List.mem_filter.mp hG
      obtain ⟨F0, hF0, hm⟩ := List.mem_filterMap.mp hG
      have hd := (hb F0 hF0).1
      refine (Linear.Fact.holds_mapVars hm fun x hx y hy => ?_).mpr (hb F0 hF0).2
      cases hy
      exact hkv x (hd x hx)
    · obtain ⟨F0, hF0, hm⟩ := List.mem_filterMap.mp hG
      obtain ⟨hF0, hbv⟩ := List.mem_filter.mp hF0
      have hdef := hnb F0 hbv
      refine (Linear.Fact.holds_mapVars hm fun x hx y hy => ?_).mpr (hR.1 F0 hF0 hdef)
      cases hy
      cases x with
      | before t => exact hkv t (hdef t hx)
      | after t => rfl
  have hGv := hall G hG
  -- Each after-term of the result is defined after the step.
  have hdefd : ∀ t ∈ definedOf kept before R, (termValue ε ρ' h' t).isSome := by
    intro t ht
    unfold definedOf at ht
    rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨u, hu, hut⟩ := List.mem_filterMap.mp ht
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hbdef u hu)
      simp [hk u t n hut hn]
    · split at ht
      · rename_i hall
        exact hR.2 (fun F hF => hnb F (List.all_eq_true.mp hall F hF)) t ht
      · cases ht
  have hval : ∀ x ∈ G.vars, ∀ y, definedAfter (definedOf kept before R) x = some y →
      termValuation ε ρ' h' y = v x := by
    intro x _ y hy
    cases x with
    | before _ => cases hy
    | after t =>
      simp only [definedAfter] at hy
      split at hy
      · cases hy; rfl
      · cases hy
  refine ⟨fun y hy => ?_, (Linear.Fact.holds_mapVars hGF hval).mpr hGv⟩
  obtain ⟨x, -, hx⟩ := Linear.Fact.mapVars_vars hGF y hy
  cases x with
  | before _ => cases hx
  | after u =>
    by_cases hc : (definedOf kept before R).contains u = true
    · simp only [definedAfter, hc, if_true, Option.some.injEq] at hx
      subst hx
      exact hdefd u (List.contains_iff_mem.mp hc)
    · simp only [definedAfter, hc, Bool.false_eq_true, if_false, reduceCtorEq] at hx

end Verification.HeapKnowledge
