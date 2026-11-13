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

/-- **A step's relation**: linear facts over before- and after-terms,
after-terms the step states defined, and before-terms it states defined
before it (a callee's post that holds defines its terms,
`IndexFact.defines_holds`). -/
structure StepRelation where
  facts : List (Linear.Fact StepVar)
  defined : List Term := []
  definedBefore : List Term := []

/-- A relation holds of a step from `ρ, h` to `ρ', h'`: each fact holds
wherever its before-terms denote integers, each `defined` term denotes
one after the step wherever all its facts' before-terms do, and each
`definedBefore` term denotes one before it. -/
def StepRelation.Holds (R : StepRelation) (ε : EntryState) (ρ : Env) (h : Heap) (ρ' : Env) (h' : Heap) : Prop :=
  (∀ F ∈ R.facts, (∀ t, StepVar.before t ∈ F.vars → (termValue ε ρ h t).isSome) →
    F.Holds (StepVar.value ε ρ h ρ' h')) ∧
  ((∀ F ∈ R.facts, ∀ t, StepVar.before t ∈ F.vars → (termValue ε ρ h t).isSome) →
    ∀ t ∈ R.defined, (termValue ε ρ' h' t).isSome) ∧
  (∀ t ∈ R.definedBefore, (termValue ε ρ h t).isSome)

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

/-- The before-terms known defined: those the facts before name and those
the relation states defined. -/
def knownBefore (before : List (Linear.Fact Term)) (R : StepRelation) : List Term :=
  beforeTerms before ++ R.definedBefore

/-- Whether a relation's fact names only before-terms the facts before
name. -/
def namesBefore (bvars : List Term) (F : Linear.Fact StepVar) : Bool :=
  F.vars.all fun
    | .before t => bvars.contains t
    | .after _ => true

/-- The relation's facts naming only before-terms known defined
(`knownBefore`), each before-term the step keeps read after it. -/
def relOf (kept : Term → Option Term) (before : List (Linear.Fact Term)) (R : StepRelation) :
    List (Linear.Fact StepVar) :=
  (R.facts.filter (namesBefore (knownBefore before R))).filterMap (·.mapVars (some ∘ keptRelVar kept))

/-- The before-variables those facts name. -/
def namesOf (rel : List (Linear.Fact StepVar)) : List StepVar :=
  ((rel.flatMap (·.vars)).filter (·.isBefore)).eraseDups

/-- The facts before naming one of `names`, each kept term read after the
step. -/
def preOf (kept : Term → Option Term) (before : List (Linear.Fact Term)) (names : List StepVar) :
    List (Linear.Fact StepVar) :=
  (before.filterMap (·.mapVars (some ∘ keptVar kept))).filter fun F => F.vars.any names.contains

/-- The after-terms known defined: each a kept term before, and the
relation's own where all its facts name only before-terms known defined. -/
def definedOf (kept : Term → Option Term) (before : List (Linear.Fact Term)) (R : StepRelation) : List Term :=
  (beforeTerms before).filterMap kept ++ (if R.facts.all (namesBefore (knownBefore before R)) then R.defined else [])

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
  have hnb : ∀ F, namesBefore (knownBefore before R) F = true → ∀ t, StepVar.before t ∈ F.vars →
      (termValue ε ρ h t).isSome := by
    intro F hF t ht
    have := List.all_eq_true.mp hF _ ht
    rcases List.mem_append.mp (by simpa [knownBefore] using this) with hm | hm
    · exact hbdef t hm
    · exact hR.2.2 t hm
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
        exact hR.2.1 (fun F hF => hnb F (List.all_eq_true.mp hall F hF)) t ht
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


/-! ## Composing a fact of every form

A callee's post fact of any form is composed into the caller's facts after
the call by the same principle as a linear one, constructor by constructor:
a linear fact by `compose`, its before-variables substituted or eliminated
together with the post's own linear facts and the caller's; a disjunction,
a guard and a quantified fact by composing their parts, which the
elimination commutes with: `(∃b. C ∧ (A ∨ B)) ⇒ (∃b. C ∧ A) ∨ (∃b. C ∧ B)`,
`(∃b. C ∧ (g ∨ B)) ⇒ g ∨ ∃b. C ∧ B` for a guard `g` read after the step,
and, the variable `b` read outside the quantifier,
`(∃b. C ∧ ∀i<n. φ) ⇒ ∀i<n'. ∃b. C ∧ φ` for every `n' ≤ n`. A fact naming no
before-variable is its renaming. -/

/-- What a step variable denotes, where it denotes an integer. -/
def StepVar.val (ε : EntryState) (ρ : Env) (h : Heap) (ρ' : Env) (h' : Heap) : StepVar → Option Int
  | .before t => termValue ε ρ h t
  | .after t => termValue ε ρ' h' t

theorem StepVar.value_eq {ρ ρ' : Env} {h h' : Heap} (x : StepVar) :
    StepVar.value ε ρ h ρ' h' x = (StepVar.val ε ρ h ρ' h' x).getD 0 := by
  cases x <;> rfl

/-- A relation with one more fact, its after-terms stated defined. -/
def StepRelation.with (R : StepRelation) (G : Linear.Fact StepVar) : StepRelation :=
  { facts := R.facts ++ [G], defined := R.defined ++ G.vars.filterMap (fun
      | .after u => some u
      | .before _ => none),
    definedBefore := R.definedBefore ++ G.vars.filterMap fun
      | .before u => some u
      | .after _ => none }

/-- A variable of the body of a quantified fact read across a step: the
bound index, element or projection, or a step variable. -/
inductive BodyVar where
  | bound (b : Bound)
  | step (x : StepVar)
  deriving DecidableEq

namespace BodyVar

/-- An order on body variables, the bound ones first. -/
def lt : BodyVar → BodyVar → Bool
  | .bound _, .step _ => true
  | .step a, .step b => a.lt b
  | _, _ => false

instance : LT BodyVar := ⟨fun a b => a.lt b = true⟩

instance : DecidableRel (α := BodyVar) (· < ·) := fun a b => inferInstanceAs (Decidable (a.lt b = true))

end BodyVar

/-- **What a composition reads** (rule Call): the terms the step keeps, the
linear facts before it, the relation the post's linear facts state, and how
the post's terms and current slots read across the step: an entry term as
a before-variable, a current term as an after-variable, a current slot as
the slot after the step holding it. -/
structure Composer where
  kept : Term → Option Term
  before : List (Linear.Fact Term)
  rel : StepRelation
  term : Term → Option StepVar
  slot : Nat → Option Nat
  /-- A post term reading a value the step's states give `undefined` at. -/
  absent : Term → Bool
  /-- A current slot of the post holding `undefined`. -/
  absentSlot : Nat → Bool

namespace Composer

variable (P : Composer)

/-- A post's term as a variable of the step, read after it where the step
keeps it. -/
def var (t : Term) : Option StepVar := (P.term t).map (keptRelVar P.kept)

/-- The linear facts both states meet, over the step's variables: the facts
before, each kept term read after the step, and the relation's facts naming
only before-terms the facts before name. -/
def context : List (Linear.Fact StepVar) :=
  P.before.filterMap (·.mapVars (some ∘ keptVar P.kept)) ++ relOf P.kept P.before P.rel

/-- The fact that never holds, `0 ≤ -1`. -/
def falsum : IndexFact := .linear (.le [] (-1))

/-- Whether a fact is a linear bound of the empty form below zero, which
never holds. -/
def isFalsum : IndexFact → Bool
  | .linear (.le [] c) => decide (c < 0)
  | _ => false

/-- Whether an atom of the forms reading a slot's value as a number, an
array or an index reads a slot holding `undefined` there, where it never
holds. -/
def readsAbsent : IndexFact → Bool
  | .index k | .int k | .pastSafe k => P.absentSlot k
  | .length x n => P.absentSlot x || P.absentSlot n
  | .bound x k _ => P.absentSlot x || P.absentSlot k
  | .element _ x k => P.absentSlot x || P.absentSlot k
  | _ => false

/-- A linear post fact naming an entry term composed with the relation
(`compose`); a fact reading a term no slot of the step holds enters no
fact. -/
def linear (G : Linear.Fact Term) : List IndexFact :=
  match G.mapVars P.term with
  | some G' => (compose P.kept P.before (P.rel.with G')).map .linear
  | none => []

/-- The terms after the step a quantified fact's bound `stop` may be read
as: itself after the step where the step keeps it, and otherwise each term
after it the linear facts both states meet bound it below by. -/
def stops (stop : Term) : List Term :=
  match P.var stop with
  | some (.after u) => [u]
  | some (.before u) => (definedOf P.kept P.before P.rel).eraseDups.filter fun t' =>
      Linear.entails P.context (.le [(.after t', 1), (.before u, -1)] 0)
  | none => []

/-- A body variable as a variable of the step. -/
def bodyVar : Bound → Option BodyVar
  | .free t => (P.var t).map .step
  | b => some (.bound b)

/-- A step's body variable read back after the step: a bound variable of
`locals`, an after-term of `allowed`. -/
def back (locals : List Bound) (allowed : List Term) : BodyVar → Option Bound
  | .bound b => if locals.contains b then some b else none
  | .step (.after u) => if allowed.contains u then some (.free u) else none
  | .step (.before _) => none

/-- Whether a body variable is a before-variable. -/
def BodyVar.isBefore : BodyVar → Bool
  | .step (.before _) => true
  | _ => false

/-- A body atom composed: its before-variables eliminated with the linear
facts both states meet, which name no bound variable, for each index alike;
the facts naming its own bound variables and after-terms known defined. -/
def atom (F : Linear.Fact Bound) : List (Linear.Fact Bound) :=
  if F.vars.any (fun | .free t => P.absent t | _ => false) then [.le [] (-1)] else
  match F.mapVars P.bodyVar with
  | none => []
  | some F' =>
    let locals := F.vars.filter fun | .free _ => false | _ => true
    let allowed := definedOf P.kept P.before P.rel ++ F'.vars.filterMap fun
      | .step (.after u) => some u
      | _ => none
    let known := P.context.filterMap (·.mapVars (some ∘ BodyVar.step)) ++ [F']
    let names := ((known.flatMap (·.vars)).filter BodyVar.isBefore).eraseDups
    (Linear.eliminateAll known names).filterMap (·.mapVars (back locals allowed))

/-- A body clause composed: an atom's facts, and a disjunction of each two
facts its alternatives compose to. -/
def clause : LinearClause Bound → List (LinearClause Bound)
  | .atom F => (P.atom F).map .atom
  | .either A B => (clause A).flatMap fun a => (clause B).map (.either a ·)

/-- The disjunction of two facts neither of which is `isFalsum`. -/
def orPair : IndexFact → IndexFact → Option IndexFact
  | .linear (.le G c), .linear (.le G' c') =>
    if G = G' then some (.linear (.le G (max c c')))
    else if Linear.normalize G' == Linear.normalize (G.scale (-1)) && decide (-c' ≤ c + 1) then none
    else some (.either (.linear (.le G c)) (.linear (.le G' c')))
  | a, b => some (.either a b)

/-- The disjunction of two facts, where it is one: an arm that never holds
(`isFalsum`) is the other; otherwise `orPair`'s, where two bounds on one
linear form are the larger bound and two bounds on opposite forms covering
every integer state nothing. -/
def orFacts (a b : IndexFact) : Option IndexFact :=
  if isFalsum a then some b else if isFalsum b then some a else orPair a b

/-- **A post fact composed** (rule Call): by structural recursion over
every form of fact, each value the step's states give `undefined` read as
`undefined`: a term reading one denotes no integer, so a linear fact or a
quantified fact's bound naming it never holds (`falsum`); a guard reading
one with the empty path reads `undefined`, which is the guard's tag or the
body holds, and with a path reads nothing; an atom reading one as a number,
an array or an index never holds (`readsAbsent`); a disjunction with an arm
that never holds is its other arm (`orFacts`). -/
def fact : IndexFact → List IndexFact
  | .linear G => if G.vars.any P.absent then [falsum]
    else if G.vars.any (·.atEntry) then P.linear G else ((IndexFact.linear G).mapM P.slot).toList
  | .either A B => (fact A).flatMap fun a => (fact B).filterMap (orFacts a)
  | .guarded s p tag B => if P.absentSlot s then
      (if p.isEmpty then (if tag = .undef then [] else fact B) else [falsum])
    else match P.slot s with
    | some s' => (fact B).map (.guarded s' p tag)
    | none => []
  | .every s p stop body => if P.absentSlot s || P.absent stop then [falsum] else
    match P.slot s with
    | some s' => (P.stops stop).map fun st => .every s' p st (body.flatMap P.clause)
    | none => []
  | F@(.index _) | F@(.length _ _) | F@(.bound _ _ _) | F@(.int _) | F@(.pastSafe _)
  | F@(.element _ _ _) | F@(.apart _ _) | F@(.storeApart _ _ _ _) =>
    if P.readsAbsent F then [falsum] else (F.mapM P.slot).toList

end Composer

section ComposeSound

variable {kept : Term → Option Term} {before : List (Linear.Fact Term)} {R : StepRelation}
  {ρ ρ' : Env} {h h' : Heap}

theorem keptVar_value
    (hk : ∀ t t' n, kept t = some t' → termValue ε ρ h t = some n → termValue ε ρ' h' t' = some n)
    {t : Term} (ht : (termValue ε ρ h t).isSome) :
    StepVar.value ε ρ h ρ' h' (keptVar kept t) = termValuation ε ρ h t := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ht
  unfold keptVar
  split
  · rename_i t' ht'
    simp only [StepVar.value, termValuation, hk t t' n ht' hn, hn]
  · rfl

theorem val_keptRelVar
    (hk : ∀ t t' n, kept t = some t' → termValue ε ρ h t = some n → termValue ε ρ' h' t' = some n)
    {x : StepVar} {n : Int} (hx : StepVar.val ε ρ h ρ' h' x = some n) :
    StepVar.val ε ρ h ρ' h' (keptRelVar kept x) = some n := by
  cases x with
  | after t => exact hx
  | before t =>
    simp only [keptRelVar, keptVar]
    split
    · rename_i t' ht'; exact hk t t' n ht' hx
    · exact hx

theorem definedOf_defined (hb : ∀ F ∈ before, (IndexFact.linear F).HoldsAt ε ρ h)
    (hk : ∀ t t' n, kept t = some t' → termValue ε ρ h t = some n → termValue ε ρ' h' t' = some n)
    (hR : R.Holds ε ρ h ρ' h') : ∀ t ∈ definedOf kept before R, (termValue ε ρ' h' t).isSome := by
  have hbdef : ∀ t ∈ beforeTerms before, (termValue ε ρ h t).isSome := by
    intro t ht
    obtain ⟨F, hF, ht⟩ := List.mem_flatMap.mp ht
    exact (hb F hF).1 t ht
  intro t ht
  unfold definedOf at ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨u, hu, hut⟩ := List.mem_filterMap.mp ht
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hbdef u hu)
    simp [hk u t n hut hn]
  · split at ht
    · rename_i hall
      refine hR.2.1 (fun F hF x hx => ?_) t ht
      have := List.all_eq_true.mp (List.all_eq_true.mp hall F hF) _ hx
      rcases List.mem_append.mp (by simpa [knownBefore] using this) with hm | hm
      · exact hbdef x hm
      · exact hR.2.2 x hm
    · cases ht

theorem context_holds (hb : ∀ F ∈ before, (IndexFact.linear F).HoldsAt ε ρ h)
    (hk : ∀ t t' n, kept t = some t' → termValue ε ρ h t = some n → termValue ε ρ' h' t' = some n)
    (hR : R.Holds ε ρ h ρ' h') :
    ∀ G ∈ (Composer.mk kept before R term slot absent absentSlot).context, G.Holds (StepVar.value ε ρ h ρ' h') := by
  show ∀ G ∈ before.filterMap (·.mapVars (some ∘ keptVar kept)) ++ relOf kept before R, _
  have hbdef : ∀ t ∈ beforeTerms before, (termValue ε ρ h t).isSome := by
    intro t ht
    obtain ⟨F, hF, ht⟩ := List.mem_flatMap.mp ht
    exact (hb F hF).1 t ht
  intro G hG
  rcases List.mem_append.mp hG with hG | hG
  · obtain ⟨F0, hF0, hm⟩ := List.mem_filterMap.mp hG
    refine (Linear.Fact.holds_mapVars hm fun x hx y hy => ?_).mpr (hb F0 hF0).2
    cases hy
    exact keptVar_value hk ((hb F0 hF0).1 x hx)
  · obtain ⟨F0, hF0, hm⟩ := List.mem_filterMap.mp hG
    obtain ⟨hF0, hbv⟩ := List.mem_filter.mp hF0
    have hdef : ∀ t, StepVar.before t ∈ F0.vars → (termValue ε ρ h t).isSome := fun t ht => by
      rcases List.mem_append.mp (by simpa [knownBefore] using List.all_eq_true.mp hbv _ ht) with hm | hm
      · exact hbdef t hm
      · exact hR.2.2 t hm
    refine (Linear.Fact.holds_mapVars hm fun x hx y hy => ?_).mpr (hR.1 F0 hF0 hdef)
    cases hy
    cases x with
    | before t => exact keptVar_value hk (hdef t hx)
    | after t => rfl

theorem fact_mapVars_none {V W : Type} {f : V → Option W} {F : Linear.Fact V} (h : F.mapVars f = none) :
    ∃ x ∈ F.vars, f x = none := by
  have hform : ∀ G : Linear.Form V, Linear.Form.mapVars f G = none → ∃ x ∈ G.map (·.1), f x = none := by
    intro G
    induction G with
    | nil => intro h; simp [Linear.Form.mapVars] at h
    | cons a t ih =>
      intro h
      obtain ⟨x, c⟩ := a
      cases hx : f x with
      | none => exact ⟨x, by simp, hx⟩
      | some y =>
        cases ht : Linear.Form.mapVars f t with
        | none => obtain ⟨z, hz, hfz⟩ := ih ht; exact ⟨z, by simp [hz], hfz⟩
        | some t' => simp [Linear.Form.mapVars, hx, ht] at h
  cases F with
  | le G d =>
    simp only [Linear.Fact.mapVars, Option.map_eq_none_iff] at h
    exact hform G h
  | ne G d =>
    simp only [Linear.Fact.mapVars, Option.map_eq_none_iff] at h
    exact hform G h

end ComposeSound


section ComposeFacts

variable {P : Composer} {ε₀ : EntryState} {ρ ρ' τ : Env} {h h' : Heap}

theorem StepRelation.with_holds {R : StepRelation} (hR : R.Holds ε ρ h ρ' h') {G : Linear.Fact StepVar}
    (hd : ∀ x ∈ G.vars, (StepVar.val ε ρ h ρ' h' x).isSome) (hG : G.Holds (StepVar.value ε ρ h ρ' h')) :
    (R.with G).Holds ε ρ h ρ' h' := by
  refine ⟨fun F hF hdef => ?_, fun hall t ht => ?_, fun t ht => ?_⟩
  · rcases List.mem_append.mp hF with hF | hF
    · exact hR.1 F hF hdef
    · simp only [List.mem_singleton] at hF; subst hF; exact hG
  · rcases List.mem_append.mp ht with ht | ht
    · exact hR.2.1 (fun F hF => hall F (List.mem_append_left _ hF)) t ht
    · obtain ⟨x, hx, hxt⟩ := List.mem_filterMap.mp ht
      cases x with
      | before _ => cases hxt
      | after u => cases hxt; exact hd _ hx
  · rcases List.mem_append.mp ht with ht | ht
    · exact hR.2.2 t ht
    · obtain ⟨x, hx, hxt⟩ := List.mem_filterMap.mp ht
      cases x with
      | after _ => cases hxt
      | before u => cases hxt; exact hd _ hx

/-- **What a composition assumes** of a step from `ρ, h` to `ρ', h'`, the
post read at the callee's entry `ε₀` and its environment `τ` after the
step: the facts before hold before it, each kept term denotes after the step
what it denoted before, the relation holds of the step, each post term's
variable denotes what the term denotes, and each current slot's image holds
its value. -/
structure Composer.Sound (P : Composer) (ε ε₀ : EntryState) (ρ : Env) (h : Heap) (ρ' τ : Env) (h' : Heap) : Prop where
  before : ∀ F ∈ P.before, (IndexFact.linear F).HoldsAt ε ρ h
  kept : ∀ t t' n, P.kept t = some t' → termValue ε ρ h t = some n → termValue ε ρ' h' t' = some n
  rel : P.rel.Holds ε ρ h ρ' h'
  term : ∀ t x, P.term t = some x → StepVar.val ε ρ h ρ' h' x = termValue ε₀ τ h' t
  slot : ∀ s s', P.slot s = some s' → ρ' s' = τ s
  absent : ∀ t, P.absent t = true → termValue ε₀ τ h' t = none
  absentSlot : ∀ s, P.absentSlot s = true → τ s = .undef

theorem Composer.var_val (hs : P.Sound ε ε₀ ρ h ρ' τ h') {t : Term} {y : StepVar} {n : Int}
    (hy : P.var t = some y) (hn : termValue ε₀ τ h' t = some n) : StepVar.val ε ρ h ρ' h' y = some n := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
  exact val_keptRelVar hs.kept (by rw [hs.term t x hx]; exact hn)

theorem Composer.linear_holds (hs : P.Sound ε ε₀ ρ h ρ' τ h') {G : Linear.Fact Term}
    (hG : (IndexFact.linear G).HoldsAt ε₀ τ h') : ∀ F ∈ P.linear G, F.HoldsAt ε ρ' h' := by
  intro F hF
  unfold Composer.linear at hF
  split at hF
  · rename_i G' hm
    obtain ⟨F0, hF0, rfl⟩ := List.mem_map.mp hF
    have hval : ∀ x ∈ G.vars, ∀ y, P.term x = some y → StepVar.value ε ρ h ρ' h' y = termValuation ε₀ τ h' x := by
      intro x _ y hy; rw [StepVar.value_eq, hs.term x y hy]; rfl
    have hd : ∀ y ∈ G'.vars, (StepVar.val ε ρ h ρ' h' y).isSome := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := Linear.Fact.mapVars_vars hm y hy
      rw [hs.term x y hxy]; exact hG.1 x hx
    have hG' := (Linear.Fact.holds_mapVars hm hval).mpr hG.2
    exact compose_holds hs.before hs.kept (StepRelation.with_holds hs.rel hd hG') F0 hF0
  · cases hF

theorem Composer.stops_bound (hs : P.Sound ε ε₀ ρ h ρ' τ h') {stop : Term} {n : Int}
    (hn : termValue ε₀ τ h' stop = some n) :
    ∀ st ∈ P.stops stop, ∃ n', termValue ε ρ' h' st = some n' ∧ n' ≤ n := by
  intro st hst
  unfold Composer.stops at hst
  split at hst
  · rename_i u hu
    simp only [List.mem_singleton] at hst; subst hst
    exact ⟨n, P.var_val hs hu hn, Int.le_refl _⟩
  · rename_i u hu
    obtain ⟨hmem, hent⟩ := List.mem_filter.mp hst
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp
      (definedOf_defined hs.before hs.kept hs.rel st (List.mem_eraseDups.mp hmem))
    have hle := Linear.entails_sound hent (context_holds (term := P.term) (slot := P.slot) (absent := P.absent) (absentSlot := P.absentSlot) hs.before hs.kept hs.rel)
    have hb : termValue ε ρ h u = some n := P.var_val hs hu hn
    simp only [Linear.Fact.Holds, Linear.Form.eval, StepVar.value, termValuation, hn', hb] at hle
    exact ⟨n', hn', by simp at hle; omega⟩
  · cases hst

theorem boundValue_local {ε ε' : EntryState} {ρ ρ' : Env} {h : Heap} {ls : List (Option Nat)} {i : Nat}
    {b : Bound} (hb : ∀ t, b ≠ .free t) : boundValue ε ρ h ls i b = boundValue ε' ρ' h ls i b := by
  cases b with
  | free t => exact absurd rfl (hb t)
  | _ => rfl

/-- What a body variable denotes at an index of a store, after the step. -/
def BodyVar.val (ε : EntryState) (ρ : Env) (h : Heap) (ρ' : Env) (h' : Heap) (ls : List (Option Nat)) (i : Nat) :
    BodyVar → Option Int
  | .bound b => boundValue ε ρ' h' ls i b
  | .step x => StepVar.val ε ρ h ρ' h' x

theorem Composer.atom_holds (hs : P.Sound ε ε₀ ρ h ρ' τ h') {ls : List (Option Nat)} {i : Nat}
    {F : Linear.Fact Bound} (hF : FactAt (boundValue ε₀ τ h' ls i) F) :
    ∀ D ∈ P.atom F, FactAt (boundValue ε ρ' h' ls i) D := by
  intro D hD
  unfold Composer.atom at hD
  split at hD
  · rename_i ha
    obtain ⟨x, hx, hxa⟩ := List.any_eq_true.mp ha
    cases x with
    | free t =>
      have := hF.1 _ hx
      simp only [boundValue, hs.absent t hxa] at this
      cases this
    | _ => cases hxa
  split at hD
  · cases hD
  · rename_i F' hm
    let bv := BodyVar.val ε ρ h ρ' h' ls i
    have hmap : ∀ x ∈ F.vars, ∀ y, P.bodyVar x = some y → bv y = boundValue ε₀ τ h' ls i x := by
      intro x hx y hy
      cases x with
      | free t =>
        simp only [Composer.bodyVar, Option.map_eq_some_iff] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hF.1 _ hx)
        exact (P.var_val hs hz hn).trans hn.symm
      | _ =>
        simp only [Composer.bodyVar, Option.some.injEq] at hy
        subst hy
        rfl
    have hF' : F'.Holds fun y => (bv y).getD 0 :=
      (Linear.Fact.holds_mapVars hm fun x hx y hy => by rw [hmap x hx y hy]).mpr hF.2
    have hknown : ∀ G ∈ P.context.filterMap (·.mapVars (some ∘ BodyVar.step)) ++ [F'],
        G.Holds fun y => (bv y).getD 0 := by
      intro G hG
      rcases List.mem_append.mp hG with hG | hG
      · obtain ⟨G0, hG0, hm0⟩ := List.mem_filterMap.mp hG
        refine (Linear.Fact.holds_mapVars hm0 fun x _ y hy => ?_).mpr
          (context_holds (term := P.term) (slot := P.slot) (absent := P.absent) (absentSlot := P.absentSlot) hs.before hs.kept hs.rel G0 hG0)
        cases hy
        exact (StepVar.value_eq x).symm
      · simp only [List.mem_singleton] at hG; subst hG; exact hF'
    obtain ⟨D0, hD0, hback⟩ := List.mem_filterMap.mp hD
    have hD0h := Linear.eliminateAll_sound hknown D0 hD0
    refine ⟨fun z hz => ?_, (Linear.Fact.holds_mapVars hback fun y _ z hz => ?_).mpr hD0h⟩
    · obtain ⟨y, -, hyz⟩ := Linear.Fact.mapVars_vars hback z hz
      cases y with
      | bound b =>
        simp only [Composer.back] at hyz
        split at hyz
        · rename_i hc
          cases hyz
          obtain ⟨hbF, hloc⟩ := List.mem_filter.mp (List.contains_iff_mem.mp hc)
          have hnf : ∀ t, z ≠ .free t := by intro t ht; subst ht; simp at hloc
          rw [boundValue_local (ε' := ε₀) (ρ' := τ) hnf]
          exact hF.1 z hbF
        · cases hyz
      | step x =>
        cases x with
        | before _ => simp [Composer.back] at hyz
        | after u =>
          simp only [Composer.back] at hyz
          split at hyz
          · rename_i hc
            cases hyz
            show (termValue ε ρ' h' u).isSome
            rcases List.mem_append.mp (List.contains_iff_mem.mp hc) with hu | hu
            · exact definedOf_defined hs.before hs.kept hs.rel u hu
            · obtain ⟨y', hy', hy'u⟩ := List.mem_filterMap.mp hu
              have hy'eq : y' = .step (.after u) := by
                cases y' with
                | bound _ => cases hy'u
                | step x' => cases x' with
                  | before _ => cases hy'u
                  | after u' => cases hy'u; rfl
              subst hy'eq
              obtain ⟨x, hx, hxy⟩ := Linear.Fact.mapVars_vars hm _ hy'
              have := hmap x hx _ hxy
              simp only [bv, BodyVar.val, StepVar.val] at this
              rw [this]; exact hF.1 x hx
          · cases hyz
    · cases y with
      | bound b =>
        simp only [Composer.back] at hz
        split at hz
        · cases hz; rfl
        · cases hz
      | step x =>
        cases x with
        | before _ => simp [Composer.back] at hz
        | after u =>
          simp only [Composer.back] at hz
          split at hz
          · cases hz; rfl
          · cases hz

theorem Composer.clause_holds (hs : P.Sound ε ε₀ ρ h ρ' τ h') {ls : List (Option Nat)} {i : Nat} :
    ∀ {C : LinearClause Bound}, C.HoldsAt (boundValue ε₀ τ h' ls i) →
      ∀ D ∈ P.clause C, D.HoldsAt (boundValue ε ρ' h' ls i)
  | .atom F, hC, D, hD => by
    simp only [Composer.clause, List.mem_map] at hD
    obtain ⟨D0, hD0, rfl⟩ := hD
    exact P.atom_holds hs hC D0 hD0
  | .either A B, hC, D, hD => by
    simp only [Composer.clause, List.mem_flatMap, List.mem_map] at hD
    obtain ⟨a, ha, b, hb, rfl⟩ := hD
    rcases hC with hA | hB
    · exact .inl (Composer.clause_holds hs hA a ha)
    · exact .inr (Composer.clause_holds hs hB b hb)

theorem isFalsum_not {ρ : Env} {h : Heap} {a : IndexFact} (ha : Composer.isFalsum a = true) :
    ¬ a.HoldsAt ε ρ h := by
  intro hh
  unfold Composer.isFalsum at ha
  split at ha
  · rename_i c
    have := hh.2
    simp only [Linear.Fact.Holds, Linear.Form.eval, decide_eq_true_eq] at this ha
    omega
  · cases ha

theorem falsum_not {ρ : Env} {h : Heap} : ¬ Composer.falsum.HoldsAt ε ρ h := isFalsum_not rfl

theorem orPair_holds {ρ : Env} {h : Heap} {a b D : IndexFact} (hD : Composer.orPair a b = some D)
    (hab : a.HoldsAt ε ρ h ∨ b.HoldsAt ε ρ h) : D.HoldsAt ε ρ h := by
  unfold Composer.orPair at hD
  split at hD
  · rename_i G c G' c'
    split at hD
    · rename_i he
      cases hD; subst he
      rcases hab with ⟨hd, hc⟩ | ⟨hd, hc⟩ <;>
        exact ⟨hd, by simp only [Linear.Fact.Holds] at hc ⊢; omega⟩
    · split at hD
      · cases hD
      · cases hD; exact hab
  · cases hD; exact hab

theorem orFacts_holds {ρ : Env} {h : Heap} {a b D : IndexFact} (hD : Composer.orFacts a b = some D)
    (hab : a.HoldsAt ε ρ h ∨ b.HoldsAt ε ρ h) : D.HoldsAt ε ρ h := by
  unfold Composer.orFacts at hD
  split at hD
  · rename_i ha; cases hD; exact hab.resolve_left (isFalsum_not ha)
  split at hD
  · rename_i hb; cases hD; exact hab.resolve_right (isFalsum_not hb)
  exact orPair_holds hD hab

/-- An atom reading `undefined` as a number, an array or an index never
holds. -/
theorem readsAbsent_not (hs : P.Sound ε ε₀ ρ h ρ' τ h') {F : IndexFact} (ha : P.readsAbsent F = true) :
    ¬ F.HoldsAt ε₀ τ h' := by
  have hst : ∀ x, P.absentSlot x = true → Footprints.storeOf (τ x) = none := fun x hx => by
    rw [hs.absentSlot x hx]; simp [Footprints.storeOf, Footprints.fieldsOf]
  have hel : ∀ x, P.absentSlot x = true → elementsOf (τ x) = none := fun x hx => by
    rw [hs.absentSlot x hx]; simp [elementsOf, Footprints.storeOf, Footprints.fieldsOf]
  intro hF
  cases F with
  | index k => obtain ⟨b, i, hb, -⟩ := hF; rw [hs.absentSlot k ha] at hb; cases hb
  | int k => simp only [IndexFact.HoldsAt, hs.absentSlot k ha] at hF; simp [intValue] at hF
  | pastSafe k => simp only [IndexFact.HoldsAt, hs.absentSlot k ha] at hF; cases hF
  | length x n =>
    obtain ⟨s, ls, hx, -, hn, -⟩ := hF
    rcases Bool.or_eq_true_iff.mp ha with ha | ha
    · rw [hst x ha] at hx; cases hx
    · rw [hs.absentSlot n ha] at hn; cases hn
  | bound x k st =>
    obtain ⟨s, ls, b, i, hx, -, hk, -⟩ := hF
    rcases Bool.or_eq_true_iff.mp ha with ha | ha
    · rw [hst x ha] at hx; cases hx
    · rw [hs.absentSlot k ha] at hk; cases hk
  | element v x k =>
    obtain ⟨s, ls, b, i, hx, -, hk, -⟩ := hF
    rcases Bool.or_eq_true_iff.mp ha with ha | ha
    · rw [hel x ha] at hx; cases hx
    · rw [hs.absentSlot k ha] at hk; cases hk
  | _ => simp [Composer.readsAbsent] at ha

/-- **Composition is sound for every form of fact** (proved): where a post
fact holds at the callee's states and the composition's assumptions hold of
the step, every fact it composes to holds after the step, at the caller's
entry state. -/
theorem Composer.fact_holds (hs : P.Sound ε ε₀ ρ h ρ' τ h') :
    ∀ {F : IndexFact}, F.HoldsAt ε₀ τ h' → ∀ G ∈ P.fact F, G.HoldsAt ε ρ' h' := by
  have hmapped : ∀ {F G : IndexFact}, F.entrySlots = [] → F.HoldsAt ε₀ τ h' → G ∈ (F.mapM P.slot).toList →
      G.HoldsAt ε ρ' h' := by
    intro F G he hF hG
    have hm : F.mapM P.slot = some G := by simpa using hG
    exact (IndexFact.holdsAt_mapM hm fun s _ t ht => hs.slot s t ht).mpr ((IndexFact.holdsAt_entry he ε₀).mpr hF)
  intro F
  induction F with
  | linear G =>
    intro hF D hD
    simp only [Composer.fact] at hD
    split at hD
    · rename_i ha
      obtain ⟨x, hx, hxa⟩ := List.any_eq_true.mp ha
      have := hF.1 x hx
      rw [hs.absent x hxa] at this
      cases this
    split at hD
    · exact P.linear_holds hs hF D hD
    · rename_i hany
      refine hmapped ?_ hF hD
      simp only [IndexFact.entrySlots, List.flatMap_eq_nil_iff]
      intro t ht
      have : t.atEntry = false := by simpa using List.any_eq_false.mp (by simpa using hany) t ht
      simp [Term.entrySlots, this]
  | either A B ihA ihB =>
    intro hF D hD
    simp only [Composer.fact, List.mem_flatMap, List.mem_filterMap] at hD
    obtain ⟨a, ha, b, hb, hab⟩ := hD
    rcases hF with hA | hB
    · exact orFacts_holds hab (.inl (ihA hA a ha))
    · exact orFacts_holds hab (.inr (ihB hB b hb))
  | guarded s p tag B ih =>
    intro hF D hD
    simp only [Composer.fact] at hD
    obtain ⟨v, hv, hor⟩ := hF
    split at hD
    · rename_i habs
      rw [hs.absentSlot s habs] at hv
      split at hD
      · rename_i hp
        have hp : p = [] := by simpa using hp
        subst hp
        simp only [readGuard, Option.some.injEq] at hv
        subst hv
        split at hD
        · cases hD
        · rename_i htag
          refine ih (hor.resolve_left fun he => htag ?_) D hD
          cases tag <;> first | rfl | (simp only [GuardTag.val] at he; cases he)
      · cases p with
        | nil => simp at *
        | cons f q => simp [readGuard] at hv
    split at hD
    · rename_i s' hs'
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hD
      refine ⟨v, by rw [hs.slot s s' hs']; exact hv, hor.imp id fun hB => ih hB b hb⟩
    · cases hD
  | every s p stop body =>
    intro hF D hD
    simp only [Composer.fact] at hD
    obtain ⟨w, sto, ls, n, hw, hsto, hls, hn, hall⟩ := hF
    split at hD
    · rename_i habs
      rcases Bool.or_eq_true_iff.mp habs with ha | ha
      · rw [hs.absentSlot s ha] at hw
        cases p with
        | nil =>
          simp only [readPath, Option.some.injEq] at hw
          subst hw
          simp [elementsOf, Footprints.storeOf, Footprints.fieldsOf] at hsto
        | cons f q => simp [readPath] at hw
      · rw [hs.absent stop ha] at hn; cases hn
    split at hD
    · rename_i s' hs'
      obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hD
      obtain ⟨n', hn', hle⟩ := P.stops_bound hs hn st hst
      refine ⟨w, sto, ls, n', by rw [hs.slot s s' hs']; exact hw, hsto, hls, hn', fun i hi C hC => ?_⟩
      obtain ⟨C0, hC0, hC⟩ := List.mem_flatMap.mp hC
      exact P.clause_holds hs (hall i (by omega) C0 hC0) C hC
    · cases hD
  | _ =>
    intro hF D hD
    simp only [Composer.fact] at hD
    split at hD
    · rename_i ha; exact absurd hF (readsAbsent_not hs ha)
    · exact hmapped rfl hF hD

end ComposeFacts

end Verification.HeapKnowledge
