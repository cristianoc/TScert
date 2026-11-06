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

/-- A linear form: coefficients by variable. Two forms with the same value at
every valuation may differ as lists; `normalize` gives one representative. -/
abbrev Form := List (Nat × Int)

/-- A form's value at an integer valuation. -/
def Form.eval (v : Nat → Int) : Form → Int
  | [] => 0
  | (x, c) :: t => c * v x + Form.eval v t

theorem Form.eval_append (v : Nat → Int) (s t : Form) : Form.eval v (s ++ t) = Form.eval v s + Form.eval v t := by
  induction s with
  | nil => simp [Form.eval]
  | cons p s ih => obtain ⟨x, c⟩ := p; simp only [List.cons_append, Form.eval, ih]; omega

/-- A form scaled by an integer. -/
def Form.scale (k : Int) (f : Form) : Form := f.map fun (x, c) => (x, k * c)

theorem Form.eval_scale (v : Nat → Int) (k : Int) (f : Form) : Form.eval v (f.scale k) = k * Form.eval v f := by
  induction f with
  | nil => simp [Form.scale, Form.eval]
  | cons p f ih =>
    obtain ⟨x, c⟩ := p
    simp only [Form.scale, List.map_cons, Form.eval] at ih ⊢
    rw [ih, Int.mul_add, Int.mul_assoc]

/-- Adds `c` to the coefficient of `x` in a form sorted by variable, keeping
it sorted and free of zero coefficients. -/
def insertTerm (x : Nat) (c : Int) : Form → Form
  | [] => if c = 0 then [] else [(x, c)]
  | (y, d) :: t =>
    if x < y then (if c = 0 then (y, d) :: t else (x, c) :: (y, d) :: t)
    else if x = y then (if c + d = 0 then t else (y, c + d) :: t)
    else (y, d) :: insertTerm x c t

theorem eval_insertTerm (v : Nat → Int) (x : Nat) (c : Int) (f : Form) :
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
def normalize (f : Form) : Form := f.foldr (fun (x, c) acc => insertTerm x c acc) []

theorem eval_normalize (v : Nat → Int) (f : Form) : Form.eval v (normalize f) = Form.eval v f := by
  induction f with
  | nil => rfl
  | cons p f ih =>
    obtain ⟨x, c⟩ := p
    simp only [normalize, List.foldr_cons] at ih ⊢
    rw [eval_insertTerm, ih]; rfl

/-! ## Facts -/

/-- A linear fact over integer variables: `form ≤ bound`, or `form ≠ bound`. -/
inductive Fact where
  | le (form : Form) (bound : Int)
  | ne (form : Form) (bound : Int)
  deriving DecidableEq, Repr, Hashable

def Fact.Holds (v : Nat → Int) : Fact → Prop
  | .le f d => Form.eval v f ≤ d
  | .ne f d => Form.eval v f ≠ d

/-- The variables a fact names. -/
def Fact.vars : Fact → List Nat
  | .le f _ | .ne f _ => f.map (·.1)

/-! ## Steps -/

/-- One step: a combination of held `le` facts, by their positions and
natural multipliers, with a divisor; or a disequality step from a held `le`
fact and a held `ne` fact with the same form and bound. Each names the fact
it concludes. -/
inductive Step where
  | combine (premises : List (Nat × Nat)) (divisor : Nat) (form : Form) (bound : Int)
  | strict (le : Nat) (ne : Nat)
  deriving DecidableEq, Repr, Hashable

/-- The sum `Σ λⱼ·aⱼ ≤ Σ λⱼ·bⱼ` of the premises a combination names. -/
def combineSum (known : List Fact) : List (Nat × Nat) → Option (Form × Int)
  | [] => some ([], 0)
  | (j, l) :: rest => do
    let .le f b ← known[j]? | none
    let (s, t) ← combineSum known rest
    some (f.scale l ++ s, l * b + t)

theorem combineSum_holds {v : Nat → Int} {known : List Fact} (hk : ∀ F ∈ known, F.Holds v) :
    ∀ {ps : List (Nat × Nat)} {s : Form} {t : Int}, combineSum known ps = some (s, t) → Form.eval v s ≤ t := by
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
def Step.conclude (known : List Fact) : Step → Option Fact
  | .combine ps g c d => do
    if g = 0 then none
    let (s, t) ← combineSum known ps
    if normalize s = normalize (c.scale g) ∧ t / (g : Int) ≤ d then some (.le c d) else none
  | .strict i j => do
    let .le f d ← known[i]? | none
    let .ne f' d' ← known[j]? | none
    if f = f' ∧ d = d' then some (.le f (d - 1)) else none

theorem Step.conclude_sound {v : Nat → Int} {known : List Fact} (hk : ∀ F ∈ known, F.Holds v) :
    ∀ {s : Step} {F : Fact}, s.conclude known = some F → F.Holds v := by
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

/-- A certificate's steps run in order, each conclusion appended to the facts
held; the facts at the end, or none where a step is refused. -/
def check (known : List Fact) : List Step → Option (List Fact)
  | [] => some known
  | s :: rest => do
    let F ← s.conclude known
    check (known ++ [F]) rest

/-- **Linear certificates are sound.** Every fact an accepted certificate
concludes holds of every integer valuation meeting the facts it starts from. -/
theorem check_sound {v : Nat → Int} :
    ∀ {steps : List Step} {known out : List Fact}, (∀ F ∈ known, F.Holds v) → check known steps = some out →
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

end Verification.Linear
