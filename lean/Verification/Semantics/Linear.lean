/-! # Linear certificates over the integers

The entailment steps of the linear atoms (RFC #115 §4.2): a linear atom
`Σ cᵢ·xᵢ ≤ d` over integer variables, a disequality `Σ cᵢ·xᵢ ≠ d`, and two
step forms, each concluding one atom from atoms already held:

- **combination**: natural multipliers `λⱼ` over premises `aⱼ·x ≤ bⱼ` and a
  divisor `g ≥ 1` give `c·x ≤ d` where `Σⱼ λⱼ·aⱼ = g·c` as linear forms and
  `⌊(Σⱼ λⱼ·bⱼ) / g⌋ ≤ d`; with `g = 1` a nonnegative combination, with
  `g > 1` one rounding, valid because `c·x` is an integer;
- **disequality**: `c·x ≤ d` and `c·x ≠ d` give `c·x ≤ d - 1`.

Steps chain: each conclusion is a premise of later steps. `check_sound`
states that every fact an accepted certificate concludes holds of every
integer valuation meeting the facts it starts from. The steps are
incomplete for integer arithmetic: an implication no chain derives is
refused. -/
namespace Verification.Linear
/-! The variables of a fact are of any type `V` with a decidable equality and
a decidable order, which `normalize` sorts by. -/
variable {V W : Type}


/-- A linear form: coefficients by variable. Two forms with the same value at
every valuation may differ as lists; `normalize` gives one representative. -/
abbrev Form (V : Type) := List (V × Int)

/-- A form's value at an integer valuation. -/
def Form.eval (v : V → Int) : Form V → Int
  | [] => 0
  | (x, c) :: t => c * v x + Form.eval v t

theorem Form.eval_append (v : V → Int) (s t : Form V) : Form.eval v (s ++ t) = Form.eval v s + Form.eval v t := by
  induction s with
  | nil => simp [Form.eval]
  | cons p s ih => obtain ⟨x, c⟩ := p; simp only [List.cons_append, Form.eval, ih]; omega

/-- A form scaled by an integer. -/
def Form.scale (k : Int) (f : Form V) : Form V := f.map fun (x, c) => (x, k * c)

theorem Form.eval_scale (v : V → Int) (k : Int) (f : Form V) : Form.eval v (f.scale k) = k * Form.eval v f := by
  induction f with
  | nil => simp [Form.scale, Form.eval]
  | cons p f ih =>
    obtain ⟨x, c⟩ := p
    simp only [Form.scale, List.map_cons, Form.eval] at ih ⊢
    rw [ih, Int.mul_add, Int.mul_assoc]

/-- Adds `c` to the coefficient of `x` in a form sorted by variable, keeping
it sorted and free of zero coefficients. -/
def insertTerm [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (x : V) (c : Int) : Form V → Form V
  | [] => if c = 0 then [] else [(x, c)]
  | (y, d) :: t =>
    if x < y then (if c = 0 then (y, d) :: t else (x, c) :: (y, d) :: t)
    else if x = y then (if c + d = 0 then t else (y, c + d) :: t)
    else (y, d) :: insertTerm x c t

theorem eval_insertTerm [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (v : V → Int) (x : V) (c : Int) (f : Form V) :
    Form.eval v (insertTerm x c f) = c * v x + Form.eval v f := by
  induction f with
  | nil => simp only [insertTerm]; split <;> simp_all [Form.eval]
  | cons p f ih =>
    obtain ⟨y, d⟩ := p
    simp only [insertTerm]
    split
    · split <;> simp_all [Form.eval]
    · split
      · rename_i hxy; subst hxy
        split
        · rename_i h0; simp only [Form.eval]
          have : c * v x + d * v x = 0 := by rw [← Int.add_mul, h0, Int.zero_mul]
          omega
        · simp only [Form.eval, Int.add_mul]; omega
      · simp only [Form.eval, ih]; omega

/-- The normal form: sorted by variable, one coefficient each, none zero. -/
def normalize [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (f : Form V) : Form V := f.foldr (fun (x, c) acc => insertTerm x c acc) []

theorem eval_normalize [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (v : V → Int) (f : Form V) : Form.eval v (normalize f) = Form.eval v f := by
  induction f with
  | nil => rfl
  | cons p f ih =>
    obtain ⟨x, c⟩ := p
    simp only [normalize, List.foldr_cons] at ih ⊢
    rw [eval_insertTerm, ih]; rfl

/-! ## Facts -/

/-- A linear fact over integer variables: `form ≤ bound`, or `form ≠ bound`. -/
inductive Fact (V : Type) where
  | le (form : Form V) (bound : Int)
  | ne (form : Form V) (bound : Int)
  deriving DecidableEq, Repr, Hashable

def Fact.Holds (v : V → Int) : Fact V → Prop
  | .le f d => Form.eval v f ≤ d
  | .ne f d => Form.eval v f ≠ d

/-- The variables a fact names. -/
def Fact.vars : Fact V → List V
  | .le f _ | .ne f _ => f.map (·.1)

theorem Form.eval_congr {v v' : V → Int} {f : Form V} (h : ∀ x ∈ f.map (·.1), v x = v' x) :
    Form.eval v f = Form.eval v' f := by
  induction f with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨x, c⟩ := p
    simp only [List.map_cons, List.mem_cons] at h
    simp only [Form.eval, h x (.inl rfl), ih (fun y hy => h y (.inr hy))]

/-- A fact reads its variables alone. -/
theorem Fact.holds_congr {v v' : V → Int} {F : Fact V} (h : ∀ x ∈ F.vars, v x = v' x) :
    F.Holds v ↔ F.Holds v' := by
  cases F <;> simp only [Fact.Holds, Fact.vars] at h ⊢ <;> rw [Form.eval_congr h]

/-! ## Steps -/

/-- One step: a combination of held `le` facts, by their positions and
natural multipliers, with a divisor; or a disequality step from a held `le`
fact and a held `ne` fact with the same form and bound. Each names the fact
it concludes. -/
inductive Step (V : Type) where
  | combine (premises : List (Nat × Nat)) (divisor : Nat) (form : Form V) (bound : Int)
  | strict (le : Nat) (ne : Nat)
  /-- Any fact, from a held `0 ≤ b` with `b < 0`: facts no valuation meets. -/
  | absurd (premise : Nat) (goal : Fact V)
  deriving DecidableEq, Repr, Hashable

/-- The sum `Σ λⱼ·aⱼ ≤ Σ λⱼ·bⱼ` of the premises a combination names. -/
def combineSum (known : List (Fact V)) : List (Nat × Nat) → Option (Form V × Int)
  | [] => some ([], 0)
  | (j, l) :: rest => do
    let .le f b ← known[j]? | none
    let (s, t) ← combineSum known rest
    some (f.scale l ++ s, l * b + t)

theorem combineSum_holds {v : V → Int} {known : List (Fact V)} (hk : ∀ F ∈ known, F.Holds v) :
    ∀ {ps : List (Nat × Nat)} {s : Form V} {t : Int}, combineSum known ps = some (s, t) → Form.eval v s ≤ t := by
  intro ps
  induction ps with
  | nil => intro s t h; simp only [combineSum, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [Form.eval]
  | cons p rest ih =>
    intro s t h
    obtain ⟨j, l⟩ := p
    simp only [combineSum] at h
    cases hj : known[j]? with
    | none => simp [hj] at h
    | some F =>
      cases F with
      | ne f b => simp [hj] at h
      | le f b =>
        cases hr : combineSum known rest with
        | none => simp [hj, hr] at h
        | some st =>
          obtain ⟨s', t'⟩ := st
          simp only [hj, hr, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hF : Form.eval v f ≤ b := hk _ (List.mem_of_getElem? hj)
          have h' := ih hr
          rw [Form.eval_append, Form.eval_scale]
          have : (l : Int) * Form.eval v f ≤ l * b := Int.mul_le_mul_of_nonneg_left hF (Int.natCast_nonneg l)
          omega

/-- The fact a step concludes from the facts held, where it is accepted. -/
def Step.conclude [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) : Step V → Option (Fact V)
  | .combine ps g c d => do
    if g = 0 then none
    let (s, t) ← combineSum known ps
    if normalize s = normalize (c.scale g) ∧ t / (g : Int) ≤ d then some (.le c d) else none
  | .strict i j => do
    let .le f d ← known[i]? | none
    let .ne f' d' ← known[j]? | none
    if f = f' ∧ d = d' then some (.le f (d - 1)) else none
  | .absurd i goal => do
    let .le f b ← known[i]? | none
    if normalize f = [] ∧ b < 0 then some goal else none

theorem Step.conclude_sound [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} {known : List (Fact V)} (hk : ∀ F ∈ known, F.Holds v) :
    ∀ {s : Step V} {F : Fact V}, s.conclude known = some F → F.Holds v := by
  intro s F h
  cases s with
  | combine ps g c d =>
    simp only [Step.conclude] at h
    by_cases hg : g = 0
    · simp [hg] at h
    · rw [if_neg hg] at h
      cases hs : combineSum known ps with
      | none => simp [hs] at h
      | some st =>
        obtain ⟨s, t⟩ := st
        simp only [hs, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · rename_i hc
          cases h
          have hst := combineSum_holds hk hs
          have he : Form.eval v s = g * Form.eval v c := by
            rw [← eval_normalize v s, hc.1, eval_normalize, Form.eval_scale]
          rw [he] at hst
          show Form.eval v c ≤ d
          have hgp : (0 : Int) < g := by omega
          have : Form.eval v c ≤ t / g := (Int.le_ediv_iff_mul_le hgp).mpr (by rw [Int.mul_comm]; exact hst)
          omega
        · cases h
  | strict i j =>
    simp only [Step.conclude] at h
    cases hi : known[i]? with
    | none => simp [hi] at h
    | some Fi =>
      cases Fi with
      | ne _ _ => simp [hi] at h
      | le f d =>
        cases hj : known[j]? with
        | none => simp [hi, hj] at h
        | some Fj =>
          cases Fj with
          | le _ _ => simp [hi, hj] at h
          | ne f' d' =>
            simp only [hi, hj, Option.bind_eq_bind, Option.bind_some] at h
            split at h
            · rename_i hc
              obtain ⟨rfl, rfl⟩ := hc
              cases h
              have h1 : Form.eval v f ≤ d := hk _ (List.mem_of_getElem? hi)
              have h2 : Form.eval v f ≠ d := hk _ (List.mem_of_getElem? hj)
              show Form.eval v f ≤ d - 1
              omega
            · cases h
  | absurd i goal =>
    simp only [Step.conclude] at h
    cases hi : known[i]? with
    | none => simp [hi] at h
    | some Fi =>
      cases Fi with
      | ne _ _ => simp [hi] at h
      | le f b =>
        simp only [hi, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · rename_i hc
          have h1 : Form.eval v f ≤ b := hk _ (List.mem_of_getElem? hi)
          have h0 : Form.eval v f = 0 := by rw [← eval_normalize v f, hc.1]; rfl
          omega
        · cases h

/-- A certificate's steps run in order, each conclusion appended to the facts
held; the facts at the end, or none where a step is refused. -/
def check [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) : List (Step V) → Option (List (Fact V))
  | [] => some known
  | s :: rest => do
    let F ← s.conclude known
    check (known ++ [F]) rest

/-- **Linear certificates are sound.** Every fact an accepted certificate
concludes holds of every integer valuation meeting the facts it starts from. -/
theorem check_sound [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} :
    ∀ {steps : List (Step V)} {known out : List (Fact V)}, (∀ F ∈ known, F.Holds v) → check known steps = some out →
      ∀ F ∈ out, F.Holds v := by
  intro steps
  induction steps with
  | nil => intro known out hk h; simp only [check, Option.some.injEq] at h; subst h; exact hk
  | cons s rest ih =>
    intro known out hk h
    simp only [check] at h
    cases hc : s.conclude known with
    | none => simp [hc] at h
    | some F =>
      simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
      refine ih ?_ h
      intro G hG
      rcases List.mem_append.mp hG with hG | hG
      · exact hk G hG
      · simp only [List.mem_singleton] at hG; subst hG; exact Step.conclude_sound hk hc

/-! ## Renaming -/

/-- A form with each variable renamed by a partial map, where it maps every one. -/
def Form.mapVars (f : V → Option W) : Form V → Option (Form W)
  | [] => some []
  | (x, c) :: t => do
    let y ← f x
    let t' ← Form.mapVars f t
    pure ((y, c) :: t')

theorem Form.eval_mapVars {f : V → Option W} {v : V → Int} {v' : W → Int} :
    ∀ {F : Form V} {F' : Form W}, Form.mapVars f F = some F' → (∀ x ∈ F.map (·.1), ∀ y, f x = some y → v' y = v x) →
      Form.eval v' F' = Form.eval v F := by
  intro F
  induction F with
  | nil => intro F' h _; simp only [Form.mapVars, Option.some.injEq] at h; subst h; rfl
  | cons p t ih =>
    intro F' h hv
    obtain ⟨x, c⟩ := p
    simp only [Form.mapVars, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, t', ht, rfl⟩ := h
    simp only [Form.eval]
    rw [ih ht (fun x hx y hy => hv x (by simp [hx]) y hy), hv x (by simp) y hy]

theorem Form.mapVars_vars {f : V → Option W} :
    ∀ {F : Form V} {F' : Form W}, Form.mapVars f F = some F' → ∀ y ∈ F'.map (·.1), ∃ x ∈ F.map (·.1), f x = some y := by
  intro F
  induction F with
  | nil => intro F' h; simp only [Form.mapVars, Option.some.injEq] at h; subst h; simp
  | cons p t ih =>
    intro F' h y hy
    obtain ⟨x, c⟩ := p
    simp only [Form.mapVars, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y', hy', t', ht, rfl⟩ := h
    simp only [List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨x, by simp, hy'⟩
    · obtain ⟨x', hx', hf⟩ := ih ht y hy
      exact ⟨x', by simp [hx'], hf⟩

theorem Form.mapVars_vars_fwd {f : V → Option W} :
    ∀ {F : Form V} {F' : Form W}, Form.mapVars f F = some F' → ∀ x ∈ F.map (·.1), ∃ y ∈ F'.map (·.1), f x = some y := by
  intro F
  induction F with
  | nil => intro F' _ x hx; simp at hx
  | cons p t ih =>
    intro F' h x hx
    obtain ⟨x0, c⟩ := p
    simp only [Form.mapVars, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y', hy', t', ht, rfl⟩ := h
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨y', by simp, hy'⟩
    · obtain ⟨y, hy, hf⟩ := ih ht x hx
      exact ⟨y, by simp [hy], hf⟩

theorem Form.mapVars_some (f : V → W) : ∀ F : Form V, ∃ F', Form.mapVars (some ∘ f) F = some F'
  | [] => ⟨[], rfl⟩
  | (x, c) :: t => by
    obtain ⟨t', ht⟩ := Form.mapVars_some f t
    exact ⟨(f x, c) :: t', by simp [Form.mapVars, ht]⟩

def Fact.mapVars (f : V → Option W) : Fact V → Option (Fact W)
  | .le F d => (Form.mapVars f F).map (.le · d)
  | .ne F d => (Form.mapVars f F).map (.ne · d)

theorem Fact.holds_mapVars {f : V → Option W} {v : V → Int} {v' : W → Int} {F : Fact V} {F' : Fact W}
    (h : F.mapVars f = some F') (hv : ∀ x ∈ F.vars, ∀ y, f x = some y → v' y = v x) :
    F'.Holds v' ↔ F.Holds v := by
  cases F with
  | le G d =>
    simp only [Fact.mapVars, Option.map_eq_some_iff] at h
    obtain ⟨G', hG, rfl⟩ := h
    simp only [Fact.Holds, Form.eval_mapVars hG hv]
  | ne G d =>
    simp only [Fact.mapVars, Option.map_eq_some_iff] at h
    obtain ⟨G', hG, rfl⟩ := h
    simp only [Fact.Holds, Form.eval_mapVars hG hv]

theorem Fact.mapVars_vars_fwd {f : V → Option W} {F : Fact V} {F' : Fact W} (h : F.mapVars f = some F') :
    ∀ x ∈ F.vars, ∃ y ∈ F'.vars, f x = some y := by
  cases F with
  | le G d =>
    simp only [Fact.mapVars, Option.map_eq_some_iff] at h
    obtain ⟨G', hG, rfl⟩ := h
    exact Form.mapVars_vars_fwd hG
  | ne G d =>
    simp only [Fact.mapVars, Option.map_eq_some_iff] at h
    obtain ⟨G', hG, rfl⟩ := h
    exact Form.mapVars_vars_fwd hG

theorem Fact.mapVars_some (f : V → W) (F : Fact V) : ∃ F', F.mapVars (some ∘ f) = some F' := by
  cases F with
  | le G d => obtain ⟨G', h⟩ := Form.mapVars_some f G; exact ⟨.le G' d, by simp [Fact.mapVars, h]⟩
  | ne G d => obtain ⟨G', h⟩ := Form.mapVars_some f G; exact ⟨.ne G' d, by simp [Fact.mapVars, h]⟩

theorem Fact.mapVars_vars {f : V → Option W} {F : Fact V} {F' : Fact W} (h : F.mapVars f = some F') :
    ∀ y ∈ F'.vars, ∃ x ∈ F.vars, f x = some y := by
  cases F with
  | le G d =>
    simp only [Fact.mapVars, Option.map_eq_some_iff] at h
    obtain ⟨G', hG, rfl⟩ := h
    exact Form.mapVars_vars hG
  | ne G d =>
    simp only [Fact.mapVars, Option.map_eq_some_iff] at h
    obtain ⟨G', hG, rfl⟩ := h
    exact Form.mapVars_vars hG

/-! ## Finding a certificate

A search proposes the steps; `check` decides them, so the search needs no
proof. It tightens each held `≤` fact whose coefficients share a divisor `g`
(a rounding step), turns a `≤` fact strict where a `≠` fact of the same form
and bound is held, then eliminates variables from the held `≤` facts and the
goal's negation (Fourier–Motzkin), tracking the multipliers of each row, until
a row with no variable and a negative bound is found. Its multipliers are the
goal's combination step, with the negation's multiplier as the divisor. -/

/-- A row of the elimination: `form ≤ bound`, as `Σⱼ λⱼ·(fact j) + μ·(¬goal)`. -/
structure Row (V : Type) where
  form : Form V
  bound : Int
  mult : List (Nat × Nat)
  goal : Nat
  deriving Inhabited

def Form.coeff [DecidableEq V] (F : Form V) (x : V) : Int := ((F.find? (·.1 == x)).map (·.2)).getD 0

def addMult : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], m => m
  | (j, l) :: rest, m =>
    match m.find? (·.1 == j) with
    | some (_, l') => addMult rest ((j, l + l') :: m.filter (·.1 != j))
    | none => addMult rest ((j, l) :: m)

def Row.scale (k : Nat) (r : Row V) : Row V :=
  { form := r.form.scale k, bound := k * r.bound, mult := r.mult.map fun (j, l) => (j, k * l), goal := k * r.goal }

def Row.add [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (r s : Row V) : Row V :=
  { form := normalize (r.form ++ s.form), bound := r.bound + s.bound, mult := addMult r.mult s.mult,
    goal := r.goal + s.goal }

/-- Eliminates `x` from the rows: those without it, and each pair of opposite
signs combined to cancel it. -/
def eliminate [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (x : V) (rows : List (Row V)) : List (Row V) :=
  let pos := rows.filter fun r => 0 < r.form.coeff x
  let neg := rows.filter fun r => r.form.coeff x < 0
  let zero := rows.filter fun r => r.form.coeff x = 0
  zero ++ pos.flatMap fun p => neg.map fun n =>
    (p.scale (n.form.coeff x).natAbs).add (n.scale (p.form.coeff x).natAbs)

def gcdForm (F : Form V) : Nat := F.foldl (fun g (_, c) => Nat.gcd g c.natAbs) 0

/-- The tightening and strict steps of the held facts, each concluding a fact
appended after them. -/
def preSteps [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) : List (Step V) × List (Fact V) := Id.run do
  let mut steps : List (Step V) := []
  let mut facts := known
  for j in List.range known.length do
    match known[j]? with
    | some (.le F d) =>
      let g := gcdForm (normalize F)
      if g > 1 then
        let c := (normalize F).map fun (x, a) => (x, a / (g : Int))
        steps := steps ++ [.combine [(j, 1)] g c (d / (g : Int))]
        facts := facts ++ [.le c (d / (g : Int))]
      for i in List.range known.length do
        match known[i]? with
        | some (.ne F' d') =>
          if F = F' ∧ d = d' then
            steps := steps ++ [.strict j i]
            facts := facts ++ [.le F (d - 1)]
        | _ => pure ()
    | _ => pure ()
  return (steps, facts)

/-- The variables of the rows, each once. -/
def rowVars [DecidableEq V] (rows : List (Row V)) : List V :=
  (rows.flatMap fun r => r.form.map (·.1)).eraseDups

/-- The variable of the rows whose elimination combines the fewest pairs,
the first such: Fourier–Motzkin's usual order, keeping the rows few. -/
def cheapestVar [DecidableEq V] (rows : List (Row V)) : Option V :=
  let cost := fun x =>
    (rows.filter fun r => 0 < r.form.coeff x).length * (rows.filter fun r => r.form.coeff x < 0).length
  ((rowVars rows).foldl (fun best x => match best with
    | some (y, c) => if cost x < c then some (x, cost x) else some (y, c)
    | none => some (x, cost x)) none).map (·.1)

/-- The steps establishing `c·x ≤ d` from the held facts, where the search
finds them, within `limit` rows at every stage. -/
def prove [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) (c : Form V) (d : Int) (limit : Nat := 400) : Option (List (Step V)) := Id.run do
  let (pre, facts) := preSteps known
  let rows0 : List (Row V) := (List.range facts.length).filterMap fun j =>
    match (facts[j]? : Option (Fact V)) with
    | some (.le F b) => some { form := normalize F, bound := b, mult := [(j, 1)], goal := 0 }
    | _ => none
  let negGoal : Row V := { form := normalize (c.scale (-1)), bound := -d - 1, mult := [], goal := 1 }
  let mut rows := negGoal :: rows0
  for _ in List.range (rowVars rows).length do
    if rows.any fun r => r.form.isEmpty && r.bound < 0 then break
    match cheapestVar rows with
    | some x =>
      rows := eliminate x rows
      if rows.length > limit then return none
    | none => break
  match rows.find? fun r => r.form.isEmpty && r.bound < 0 && 0 < r.goal with
  | some r => return some (pre ++ [.combine r.mult r.goal c d])
  | none =>
    -- The held facts alone meet no valuation: their sum `0 ≤ b`, `b < 0`,
    -- concludes the goal (`absurd`).
    match rows.find? fun r => r.form.isEmpty && r.bound < 0 && r.goal = 0 with
    | some r => return some (pre ++ [.combine r.mult 1 [] r.bound, .absurd facts.length (.le c d)])
    | none => return none

/-- The held facts connected to the goal's variables: those sharing a
variable with the goal or with a fact already selected, so the elimination
works over the facts that can matter. A goal naming no variable (a constant
fact, which only facts no valuation meets entail besides a true one) is
searched over every held fact. -/
def relevant [DecidableEq V] (known : List (Fact V)) (goal : Fact V) : List (Fact V) := Id.run do
  if goal.vars.isEmpty then return known
  let mut vars := goal.vars
  let mut chosen : List (Fact V) := []
  for _ in List.range (known.length + 1) do
    let more := known.filter fun F => !chosen.contains F && F.vars.any vars.contains
    if more.isEmpty then break
    chosen := chosen ++ more
    vars := vars ++ more.flatMap (·.vars)
  return known.filter chosen.contains

theorem relevant_mem [DecidableEq V] {known : List (Fact V)} {goal F : Fact V}
    (h : F ∈ relevant known goal) : F ∈ known := by
  unfold relevant at h
  split at h
  · exact h
  · exact (List.mem_filter.mp h).1

/-- Whether the held facts entail `goal`, by a certificate `check` accepts,
searched over the facts connected to the goal. -/
def entailsDirect [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) (goal : Fact V) : Bool :=
  known.contains goal ||
  match goal with
  | .le c d =>
    let near := relevant known goal
    match prove near c d with
    | some steps => match check near steps with
      | some out => out.contains goal
      | none => false
    | none => false
  | .ne _ _ => false

theorem entailsDirect_sound [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} {known : List (Fact V)} {goal : Fact V} (h : entailsDirect known goal = true)
    (hk : ∀ F ∈ known, F.Holds v) : goal.Holds v := by
  unfold entailsDirect at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact hk goal (List.contains_iff_mem.mp h)
  · cases goal with
    | ne _ _ => cases h
    | le c d =>
      simp only at h
      have hn : ∀ F ∈ relevant known (.le c d), F.Holds v := by
        intro F hF
        exact hk F (relevant_mem hF)
      split at h
      · split at h
        · rename_i out hc
          exact check_sound hn hc _ (List.contains_iff_mem.mp h)
        · cases h
      · cases h

/-- The held facts with the strict bounds their inequalities give: for each
`c·x ≠ d`, the bound `c·x ≤ d - 1` where the facts entail `c·x ≤ d`, and
`-c·x ≤ -d - 1` where they entail `-c·x ≤ -d` (`entailsDirect`). -/
def strengthen [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) : List (Fact V) :=
  known ++ known.flatMap fun
    | .ne F d =>
      (if entailsDirect known (.le F d) then [.le F (d - 1)] else []) ++
      (if entailsDirect known (.le (F.scale (-1)) (-d)) then [.le (F.scale (-1)) (-d - 1)] else [])
    | .le _ _ => []

theorem strengthen_holds [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} {known : List (Fact V)}
    (hk : ∀ F ∈ known, F.Holds v) : ∀ F ∈ strengthen known, F.Holds v := by
  intro G hG
  rcases List.mem_append.mp hG with hG | hG
  · exact hk G hG
  · obtain ⟨H, hH, hG⟩ := List.mem_flatMap.mp hG
    cases H with
    | le _ _ => cases hG
    | ne F d =>
      have hne : Form.eval v F ≠ d := hk _ hH
      rcases List.mem_append.mp hG with hG | hG
      · split at hG
        · rename_i he
          simp only [List.mem_singleton] at hG; subst hG
          have := entailsDirect_sound he hk
          show Form.eval v F ≤ d - 1
          simp only [Fact.Holds] at this; omega
        · cases hG
      · split at hG
        · rename_i he
          simp only [List.mem_singleton] at hG; subst hG
          have := entailsDirect_sound he hk
          show Form.eval v (F.scale (-1)) ≤ -d - 1
          simp only [Fact.Holds, Form.eval_scale] at this ⊢; omega
        · cases hG

/-- Whether the held facts entail `goal`: directly (`entailsDirect`), or
with the strict bounds their inequalities give (`strengthen`). -/
def entails [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) (goal : Fact V) : Bool :=
  entailsDirect known goal ||
    (known.any (fun | .ne _ _ => true | .le _ _ => false) && entailsDirect (strengthen known) goal)

/-- **Entailment is sound.** -/
theorem entails_sound [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} {known : List (Fact V)} {goal : Fact V} (h : entails known goal = true)
    (hk : ∀ F ∈ known, F.Holds v) : goal.Holds v := by
  unfold entails at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact entailsDirect_sound h hk
  · exact entailsDirect_sound (Bool.and_eq_true_iff.mp h).2 (strengthen_holds hk)

/-- Whether the held facts entail `goal`, or, where they alone do not, the
held facts with `extra`: facts read only where needed, so the search over
the held facts alone stays as small as it was. -/
def entailsWith [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (known extra : List (Fact V)) (goal : Fact V) : Bool :=
  entails known goal || entails (known ++ extra) goal

theorem entailsWith_sound [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} {known extra : List (Fact V)}
    {goal : Fact V} (h : entailsWith known extra goal = true)
    (hk : ∀ F ∈ known, F.Holds v) (he : ∀ F ∈ extra, F.Holds v) : goal.Holds v := by
  unfold entailsWith at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact entails_sound h hk
  · exact entails_sound h fun F hF => (List.mem_append.mp hF).elim (hk F) (he F)

/-! ## Eliminating a variable

The facts implied by held `≤` facts that do not name a variable `x`: each
pair of opposite signs on `x` combined to cancel it (Fourier–Motzkin), each
combination a `combine` step `check` decides. -/

/-- The steps combining each pair of held facts of opposite signs on `x`. -/
def elimSteps [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) (x : V) (limit : Nat := 64) : List (Step V) :=
  let les := (List.range known.length).filterMap fun j => match (known[j]? : Option (Fact V)) with
    | some (.le F b) => some (j, normalize F, b)
    | _ => none
  let pos := les.filter fun (_, F, _) => 0 < F.coeff x
  let neg := les.filter fun (_, F, _) => F.coeff x < 0
  ((pos.flatMap fun (i, F, b) => neg.map fun (j, F', b') =>
    let p := (F'.coeff x).natAbs
    let q := (F.coeff x).natAbs
    Step.combine [(i, p), (j, q)] 1 (normalize (F.scale p ++ F'.scale q)) (p * b + q * b'))).take limit

/-- The held facts with each variable of `xs` eliminated in turn, the derived
facts appended; `known` itself where a step is refused. -/
def eliminateAll [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) : List V → List (Fact V)
  | [] => known
  | x :: xs => match check known (elimSteps known x) with
    | some out => eliminateAll out xs
    | none => eliminateAll known xs

theorem eliminateAll_sound [DecidableEq V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} :
    ∀ {xs : List V} {known : List (Fact V)}, (∀ F ∈ known, F.Holds v) → ∀ F ∈ eliminateAll known xs, F.Holds v := by
  intro xs
  induction xs with
  | nil => intro known hk; exact hk
  | cons x xs ih =>
    intro known hk
    simp only [eliminateAll]
    split
    · rename_i out hc; exact ih (check_sound hk hc)
    · exact ih hk

/-! ## Witnesses

`sumPairs` of decision 6: from `2j - 2n ≤ -1` (the loop's `2 * j < pairs.length`
with `pairs.length = 2n`), one step with divisor 2 gives `j - n ≤ -1`, and a
combination gives `2j + 1 - 2n ≤ -1`. A wrong multiplier is refused, and so is
a rounding that would need a divisor the premise's form is not a multiple of. -/

-- j is variable 0, n is variable 1.
#guard (check [.le [(0, 2), (1, -2)] (-1)]
  [.combine [(0, 1)] 2 [(0, 1), (1, -1)] (-1), .combine [(1, 2)] 1 [(0, 2), (1, -2)] (-2)]).isSome
#guard (check [.le [(0, 2), (1, -2)] (-1)] [.combine [(0, 2)] 2 [(0, 1), (1, -1)] (-2)]).isNone
#guard (check [.le [(0, 2), (1, -2)] (-1)] [.combine [(0, 1)] 1 [(0, 1), (1, -1)] (-1)]).isNone
-- `atEnd`: from `i + 1 - count ≤ 0` and `i + 1 ≠ count` (as `i - count ≠ -1`), `i + 1 - count ≤ -1`.
#guard (check [.le [(0, 1), (1, -1)] (-1), .ne [(0, 1), (1, -1)] (-1)] [.strict 0 1]) =
  some [.le [(0, 1), (1, -1)] (-1), .ne [(0, 1), (1, -1)] (-1), .le [(0, 1), (1, -1)] (-2)]

-- `entails` finds the same chain: `2j - 2n ≤ -1` gives `2j + 1 - 2n ≤ -1`, and
-- `i + 1 - count ≤ 0` with `i + 1 ≠ count` gives `i + 2 - count ≤ 0`; `j ≤ n` gives
-- no `j ≤ n - 1`.
#guard entails [.le [(0, 2), (1, -2)] (-1)] (.le [(0, 2), (1, -2)] (-2))
#guard entails [.le [(0, 1), (1, -1)] (-1), .ne [(0, 1), (1, -1)] (-1)] (.le [(0, 1), (1, -1)] (-2))
#guard !entails [.le [(0, 1), (1, -1)] 0] (.le [(0, 1), (1, -1)] (-1))
-- `0 ≤ i`, `i < n`, `n ≤ 2^32 - 1` give `i ≤ 2^32 - 2`.
#guard entails [.le [(0, -1)] 0, .le [(0, 1), (1, -1)] (-1), .le [(1, 1)] 4294967295] (.le [(0, 1)] 4294967294)

-- Eliminating `j` (variable 0) from `j - n ≤ -1` and `-j ≤ 0` gives `-n ≤ -1`.
#guard (eliminateAll [.le [(0, 1), (1, -1)] (-1), .le [(0, -1)] 0] [0]).contains (.le [(1, -1)] (-1))

end Verification.Linear
