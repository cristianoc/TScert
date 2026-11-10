import Std.Data.HashMap
import Std.Data.HashSet

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


/-- `List.eraseDups` by a hash set of the elements kept: each element once, at
its first occurrence, in time linear in the list (`dedupHash_eq`). -/
def dedupHash {α : Type} [BEq α] [Hashable α] (l : List α) : List α := go l {} []
where
  go : List α → Std.HashSet α → List α → List α
  | [], _, acc => acc.reverse
  | a :: l, s, acc => if s.contains a then go l s acc else go l (s.insert a) (a :: acc)

theorem dedupHash_go {α : Type} [BEq α] [Hashable α] [LawfulBEq α] :
    ∀ (l : List α) (s : Std.HashSet α) (acc : List α), (∀ x, s.contains x = acc.any (x == ·)) →
      dedupHash.go l s acc = List.eraseDupsBy.loop (· == ·) l acc := by
  intro l
  induction l with
  | nil => intro s acc _; rfl
  | cons a l ih =>
    intro s acc hs
    simp only [dedupHash.go, List.eraseDupsBy.loop, hs a]
    cases acc.any (a == ·)
    · simp only [Bool.false_eq_true, ite_false]
      refine ih _ _ fun x => ?_
      rw [Std.HashSet.contains_insert, hs x]
      simp only [List.any_cons]
      cases hx : x == a
      · have hne : (a == x) = false := by
          rw [beq_eq_false_iff_ne] at hx ⊢; exact fun h => hx h.symm
        simp [hne]
      · simp_all
    · simp only [ite_true]
      exact ih _ _ hs

/-- **Hash deduplication is `eraseDups`.** -/
theorem dedupHash_eq {α : Type} [BEq α] [Hashable α] [LawfulBEq α] (l : List α) : dedupHash l = l.eraseDups :=
  dedupHash_go l {} [] fun x => by simp

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
appended after them: for each held `≤` fact in order, its tightening, then a
strict step with each held `≠` fact of the same form and bound. -/
def preSteps [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) :
    List (Step V) × List (Fact V) := Id.run do
  let arr := known.toArray
  let mut nes : Std.HashMap (Form V × Int) (Array Nat) := {}
  for h : i in [0:arr.size] do
    match arr[i] with
    | .ne F d => nes := nes.alter (F, d) fun | some a => some (a.push i) | none => some #[i]
    | .le _ _ => pure ()
  let mut steps : Array (Step V) := #[]
  let mut extra : Array (Fact V) := #[]
  for h : j in [0:arr.size] do
    match arr[j] with
    | .le F d =>
      let g := gcdForm (normalize F)
      if g > 1 then
        let c := (normalize F).map fun (x, a) => (x, a / (g : Int))
        steps := steps.push (.combine [(j, 1)] g c (d / (g : Int)))
        extra := extra.push (.le c (d / (g : Int)))
      for i in nes.getD (F, d) #[] do
        steps := steps.push (.strict j i)
        extra := extra.push (.le F (d - 1))
    | .ne _ _ => pure ()
  return (steps.toList, known ++ extra.toList)

/-- The number of distinct variables of the rows. -/
def rowVarCount [BEq V] [Hashable V] (rows : List (Row V)) : Nat :=
  (rows.foldl (fun (s : Std.HashSet V) r => r.form.foldl (fun s (x, _) => s.insert x) s) {}).size

/-- The variable of the rows whose elimination combines the fewest pairs,
the first such in order of first occurrence: Fourier–Motzkin's usual order,
keeping the rows few. The rows' forms are normal, each variable once. -/
def cheapestVar [BEq V] [Hashable V] (rows : List (Row V)) : Option V := Id.run do
  let mut order : Array V := #[]
  let mut signs : Std.HashMap V (Nat × Nat) := {}
  for r in rows do
    for (x, c) in r.form do
      if !signs.contains x then order := order.push x
      let (p, n) := signs.getD x (0, 0)
      signs := signs.insert x (if 0 < c then (p + 1, n) else if c < 0 then (p, n + 1) else (p, n))
  let mut best : Option (V × Nat) := none
  for x in order do
    let (p, n) := signs.getD x (0, 0)
    let cost := p * n
    match best with
    | some (_, c) => if cost < c then best := some (x, cost)
    | none => best := some (x, cost)
  return best.map (·.1)

/-- The steps establishing `c·x ≤ d` from the held facts, where the search
finds them, within `limit` rows at every stage. -/
def prove [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) (c : Form V) (d : Int) (limit : Nat := 400) : Option (List (Step V)) := Id.run do
  let (pre, facts) := preSteps known
  let rows0 : List (Row V) := facts.zipIdx.filterMap fun
    | (.le F b, j) => some { form := normalize F, bound := b, mult := [(j, 1)], goal := 0 }
    | (.ne _ _, _) => none
  let negGoal : Row V := { form := normalize (c.scale (-1)), bound := -d - 1, mult := [], goal := 1 }
  let mut rows := negGoal :: rows0
  for _ in [0:rowVarCount rows] do
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

/-- Whether the facts `near` entail `goal`: it is one of them, or a
certificate the search finds over them `check` accepts. -/
def searchIn [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] (near : List (Fact V)) (goal : Fact V) : Bool :=
  near.contains goal ||
  match goal with
  | .le c d =>
    match prove near c d with
    | some steps => match check near steps with
      | some out => out.contains goal
      | none => false
    | none => false
  | .ne _ _ => false

theorem searchIn_sound [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} {near : List (Fact V)}
    {goal : Fact V} (h : searchIn near goal = true) (hk : ∀ F ∈ near, F.Holds v) : goal.Holds v := by
  unfold searchIn at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact hk goal (List.contains_iff_mem.mp h)
  · cases goal with
    | ne _ _ => cases h
    | le c d =>
      simp only at h
      split at h
      · split at h
        · rename_i out hc
          exact check_sound hk hc _ (List.contains_iff_mem.mp h)
        · cases h
      · cases h

/-- Whether the held facts entail `goal`, by a certificate `check` accepts,
searched over the facts connected to the goal. -/
def entailsDirect [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) (goal : Fact V) : Bool :=
  searchIn (relevant known goal) goal

theorem entailsDirect_sound [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} {known : List (Fact V)} {goal : Fact V} (h : entailsDirect known goal = true)
    (hk : ∀ F ∈ known, F.Holds v) : goal.Holds v :=
  searchIn_sound h fun _ hF => hk _ (relevant_mem hF)

/-- The facts `near` with the strict bounds their inequalities give: for each
`c·x ≠ d`, the bound `c·x ≤ d - 1` where the facts `nearOf` gives for it
entail `c·x ≤ d`, and `-c·x ≤ -d - 1` where they entail `-c·x ≤ -d`
(`searchIn`). -/
def strengthenWith [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] (nearOf : Fact V → List (Fact V))
    (near : List (Fact V)) : List (Fact V) :=
  near ++ near.flatMap fun
    | .ne F d =>
      (if searchIn (nearOf (.le F d)) (.le F d) then [.le F (d - 1)] else []) ++
      (if searchIn (nearOf (.le (F.scale (-1)) (-d))) (.le (F.scale (-1)) (-d)) then [.le (F.scale (-1)) (-d - 1)] else [])
    | .le _ _ => []

theorem strengthenWith_holds [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int}
    {nearOf : Fact V → List (Fact V)} {near : List (Fact V)}
    (hn : ∀ G, ∀ F ∈ nearOf G, F.Holds v) (hk : ∀ F ∈ near, F.Holds v) : ∀ F ∈ strengthenWith nearOf near, F.Holds v := by
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
          have := searchIn_sound he (hn _)
          show Form.eval v F ≤ d - 1
          simp only [Fact.Holds] at this; omega
        · cases hG
      · split at hG
        · rename_i he
          simp only [List.mem_singleton] at hG; subst hG
          have := searchIn_sound he (hn _)
          show Form.eval v (F.scale (-1)) ≤ -d - 1
          simp only [Fact.Holds, Form.eval_scale] at this ⊢; omega
        · cases hG

/-- The held facts with the strict bounds their inequalities give
(`strengthenWith`), each searched over the facts connected to it. -/
def strengthen [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) : List (Fact V) :=
  strengthenWith (relevant known) known

theorem strengthen_holds [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} {known : List (Fact V)}
    (hk : ∀ F ∈ known, F.Holds v) : ∀ F ∈ strengthen known, F.Holds v :=
  strengthenWith_holds (fun _ _ hF => hk _ (relevant_mem hF)) hk

/-! ## Prepared facts

A knowledge's facts prepared once for every query against it: each fact once,
in order of first occurrence, the held ones first and the extra ones after
(`base` counts the held ones); for each normal form, the position of its `≤`
fact of least bound; for each variable, the positions of the facts naming
it. A query first tries the direct answer (`Known.direct`), then searches
over the facts connected to the goal (`Known.near`). The tables only propose
positions: each answer is decided on the facts at them, so soundness reads
nothing of the tables but that every fact held holds. -/

structure Known (V : Type) [DecidableEq V] [Hashable V] where
  facts : Array (Fact V) := #[]
  base : Nat := 0
  pos : Std.HashMap (Fact V) Nat := {}
  leForm : Std.HashMap (Form V) Nat := {}
  byVar : Std.HashMap V (Array Nat) := {}

namespace Known
variable [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)]

/-- Every prepared fact holds. -/
def Holds (K : Known V) (v : V → Int) : Prop := ∀ F ∈ K.facts, F.Holds v

/-- The facts with `F` added, where it is new. -/
def add (K : Known V) (F : Fact V) : Known V :=
  if K.pos.contains F then K else
  let ⟨facts, base, pos, leForm, byVar⟩ := K
  let i := facts.size
  let leForm := match F with
    | .le G b =>
      let n := normalize G
      match leForm[n]? with
      | some j => match facts[j]? with
        | some (.le _ b') => if b < b' then leForm.insert n i else leForm
        | _ => leForm.insert n i
      | none => leForm.insert n i
    | .ne _ _ => leForm
  let byVar := F.vars.foldl (fun m x => m.alter x fun | some a => some (a.push i) | none => some #[i]) byVar
  { facts := facts.push F, base, pos := pos.insert F i, leForm, byVar }

theorem mem_add {K : Known V} {F G : Fact V} (h : G ∈ (K.add F).facts) : G ∈ K.facts ∨ G = F := by
  unfold add at h
  split at h
  · exact .inl h
  · simpa using Array.mem_push.mp h

theorem mem_foldl_add : ∀ {l : List (Fact V)} {K : Known V} {G : Fact V}, G ∈ (l.foldl add K).facts → G ∈ K.facts ∨ G ∈ l := by
  intro l
  induction l with
  | nil => intro K G h; exact .inl h
  | cons F l ih =>
    intro K G h
    rcases ih h with h | h
    · rcases mem_add h with h | h
      · exact .inl h
      · exact .inr (h ▸ List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h)

/-- The facts `known`, then the facts `extra`, prepared. -/
def build (known extra : List (Fact V)) : Known V :=
  let K := known.foldl add {}
  extra.foldl add { K with base := K.facts.size }

theorem build_holds {v : V → Int} {known extra : List (Fact V)} (hk : ∀ F ∈ known, F.Holds v)
    (he : ∀ F ∈ extra, F.Holds v) : (build known extra).Holds v := by
  intro F hF
  rcases mem_foldl_add hF with h | h
  · rcases mem_foldl_add (l := known) (K := {}) h with h | h
    · simp at h
    · exact hk F h
  · exact he F h

/-- The prepared facts below position `lim` connected to the goal's
variables, in order: those sharing a variable with the goal or with a fact
already selected, found through the facts by variable. A goal naming no
variable is searched over every fact below `lim`. -/
def nearChosen (K : Known V) (lim : Nat) (goal : Fact V) : Array Bool :=
  if goal.vars.isEmpty then Array.replicate lim true else Id.run do
    let mut chosen := Array.replicate lim false
    let mut seen : Std.HashSet V := {}
    let mut queue : Array Nat := #[]
    let mut vars := goal.vars
    let mut head := 0
    for _ in [0:lim + 1] do
      for x in vars do
        if !seen.contains x then
          seen := seen.insert x
          for i in K.byVar.getD x #[] do
            if i < lim && !chosen[i]! then
              chosen := chosen.set! i true
              queue := queue.push i
      if head < queue.size then
        vars := match K.facts[queue[head]!]? with
          | some F => F.vars
          | none => []
        head := head + 1
      else break
    return chosen

@[inherit_doc nearChosen]
def near (K : Known V) (lim : Nat) (goal : Fact V) : List (Fact V) :=
  let chosen := K.nearChosen lim goal
  (List.range lim).filterMap fun i => if chosen[i]?.getD false then K.facts[i]? else none

omit [LT V] [DecidableRel (α := V) (· < ·)] in
theorem near_mem {K : Known V} {lim : Nat} {goal F : Fact V} (h : F ∈ K.near lim goal) : F ∈ K.facts := by
  unfold near at h
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.mp h
  revert hi
  split
  · exact Array.mem_of_getElem?
  · intro hi; cases hi

/-- The direct answer: the goal `c·x ≤ d` with `c` of normal form empty and
`0 ≤ d`; or a held `≤` fact of the goal's normal form with a bound at most
`d`; or a `≠` goal held itself. -/
def direct (K : Known V) (goal : Fact V) : Bool :=
  match goal with
  | .le c d =>
    let n := normalize c
    (n.isEmpty && decide (0 ≤ d)) ||
    match K.leForm[n]? with
    | some i => match K.facts[i]? with
      | some (.le F b) => normalize F == n && decide (b ≤ d)
      | _ => false
    | none => false
  | .ne _ _ => match K.pos[goal]? with
    | some i => K.facts[i]? == some goal
    | none => false

theorem direct_sound {K : Known V} {v : V → Int} {goal : Fact V} (hK : K.Holds v) (h : K.direct goal = true) :
    goal.Holds v := by
  unfold direct at h
  split at h
  · rename_i c d
    rcases Bool.or_eq_true_iff.mp h with h | h
    · simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at h
      show Form.eval v c ≤ d
      rw [← eval_normalize v c, h.1]
      simpa [Form.eval] using h.2
    · split at h
      · split at h
        · rename_i i F b hi
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
          have hF : Form.eval v F ≤ b := hK _ (Array.mem_of_getElem? hi)
          show Form.eval v c ≤ d
          rw [← eval_normalize v c, ← h.1, eval_normalize]
          omega
        · cases h
      · cases h
  · split at h
    · rename_i i _
      simp only [beq_iff_eq] at h
      exact hK _ (Array.mem_of_getElem? h)
    · cases h

/-- Whether the facts `near` entail `goal`, alone or with the strict bounds
their inequalities give, each searched over the facts `nearOf` gives. -/
def entailsNear (nearOf : Fact V → List (Fact V)) (near : List (Fact V)) (goal : Fact V) : Bool :=
  searchIn near goal ||
    (near.any (fun | .ne _ _ => true | .le _ _ => false) && searchIn (strengthenWith nearOf near) goal)

theorem entailsNear_sound {v : V → Int} {nearOf : Fact V → List (Fact V)} {near : List (Fact V)} {goal : Fact V}
    (hn : ∀ G, ∀ F ∈ nearOf G, F.Holds v) (hk : ∀ F ∈ near, F.Holds v) (h : entailsNear nearOf near goal = true) :
    goal.Holds v := by
  unfold entailsNear at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact searchIn_sound h hk
  · exact searchIn_sound (Bool.and_eq_true_iff.mp h).2 (strengthenWith_holds hn hk)

/-- The search below position `lim`: over the facts connected to the goal,
alone or strengthened, each disequality's bounds searched over the same facts
where the goal names a variable (they are connected to it), over the facts
connected to the bound otherwise. -/
def entailsBelow (K : Known V) (lim : Nat) (near : List (Fact V)) (goal : Fact V) : Bool :=
  entailsNear (if goal.vars.isEmpty then K.near lim else fun _ => near) near goal

theorem entailsBelow_sound {K : Known V} {v : V → Int} {lim : Nat} {near : List (Fact V)} {goal : Fact V}
    (hK : K.Holds v) (hk : ∀ F ∈ near, F.Holds v) (h : K.entailsBelow lim near goal = true) : goal.Holds v := by
  unfold entailsBelow at h
  refine entailsNear_sound ?_ hk h
  split
  · exact fun _ _ hF => hK _ (near_mem hF)
  · exact fun _ => hk

/-- Whether the prepared facts entail `goal`: directly (`direct`); or by a
search over the held facts connected to it; or, where the extra facts add
facts connected to it, by a search over all of those. -/
def entails (K : Known V) (goal : Fact V) : Bool :=
  K.direct goal ||
    let near := K.near K.base goal
    K.entailsBelow K.base near goal ||
      (decide (K.base < K.facts.size) &&
        let near' := K.near K.facts.size goal
        near'.length != near.length && K.entailsBelow K.facts.size near' goal)

/-- **Prepared entailment is sound.** -/
theorem entails_sound {K : Known V} {v : V → Int} {goal : Fact V} (hK : K.Holds v) (h : K.entails goal = true) :
    goal.Holds v := by
  unfold entails at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact direct_sound hK h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · exact entailsBelow_sound hK (fun _ hF => hK _ (near_mem hF)) h
    · simp only [Bool.and_eq_true] at h
      exact entailsBelow_sound hK (fun _ hF => hK _ (near_mem hF)) h.2.2

end Known

/-- Whether the held facts entail `goal` (`Known.entails`). -/
def entails [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] (known : List (Fact V)) (goal : Fact V) : Bool :=
  (Known.build known []).entails goal

/-- **Entailment is sound.** -/
theorem entails_sound [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} {known : List (Fact V)} {goal : Fact V} (h : entails known goal = true)
    (hk : ∀ F ∈ known, F.Holds v) : goal.Holds v :=
  Known.entails_sound (Known.build_holds hk (by simp)) h

/-- Whether the held facts entail `goal`, or, where they alone do not, the
held facts with `extra`: facts read only where needed, so the search over
the held facts alone stays as small as it was. -/
def entailsWith [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] (known extra : List (Fact V)) (goal : Fact V) : Bool :=
  (Known.build known extra).entails goal

theorem entailsWith_sound [DecidableEq V] [Hashable V] [LT V] [DecidableRel (α := V) (· < ·)] {v : V → Int} {known extra : List (Fact V)}
    {goal : Fact V} (h : entailsWith known extra goal = true)
    (hk : ∀ F ∈ known, F.Holds v) (he : ∀ F ∈ extra, F.Holds v) : goal.Holds v :=
  Known.entails_sound (Known.build_holds hk he) h

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
