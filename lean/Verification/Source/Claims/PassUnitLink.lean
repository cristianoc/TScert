import Verification.Source.Claims.PassUnitHeadline

/-! # The single pass's unit theorem: linking a file's units

A unit's acceptance assumes, through `EnvOk` of its inputs, the interfaces
of the functions it calls: its own group's members (recursion included) and
the units its group depends on (`FilePlans.dependencies`, the `depends` of
its verdict line). This module states the closure of a file's verdicts
(`closedUnits`, the Lean function the agreement tool's `closed` stands for),
the step-indexed linking induction that discharges the assumed interfaces
over a closed set (`link`, `closedUnits_linked`), and how a discharged
interface meets a caller's input slot (`envOk_of_linked`). -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-! ## The closure of a file's verdicts -/

/-- A file's verdicts: per unit, its accepted dependencies, or `none` where
refused. -/
abbrev Verdicts := List (String × Option (List String))

/-- The accepted dependencies of a unit, where it is accepted. -/
def Verdicts.accepted (vs : Verdicts) (u : String) : Option (List String) :=
  (vs.lookup u).join

/-- A set of units is closed under the verdicts: each is accepted, with
every dependency in the set. -/
def ClosedIn (vs : Verdicts) (S : List String) : Prop :=
  ∀ u ∈ S, ∃ ds, vs.accepted u = some ds ∧ ∀ d ∈ ds, d ∈ S

/-- One round: the units of `S` accepted with every dependency in `S`. -/
def shrink (vs : Verdicts) (S : List String) : List String :=
  S.filter fun u => match vs.accepted u with
    | some ds => ds.all S.contains
    | none => false

/-- Whether `S` is closed, decided. -/
def closedCheck (vs : Verdicts) (S : List String) : Bool :=
  S.all fun u => match vs.accepted u with
    | some ds => ds.all S.contains
    | none => false

/-- **The closed units**: the accepted units, shrunk until every remaining
one has its dependencies remaining (at most one round per unit), kept only
where the result is closed. A dependency with no verdict refuses its
dependents. -/
def closedUnits (vs : Verdicts) : List String :=
  let S := (List.range (vs.length + 1)).foldl (fun S _ => shrink vs S)
    (vs.filterMap fun (u, v) => v.map fun _ => u)
  if closedCheck vs S then S else []

theorem closedCheck_sound {vs : Verdicts} {S : List String} (h : closedCheck vs S = true) : ClosedIn vs S := by
  intro u hu
  have hx := List.all_eq_true.mp h u hu
  cases ha : vs.accepted u with
  | none => rw [ha] at hx; cases hx
  | some ds =>
    rw [ha] at hx
    exact ⟨ds, rfl, fun d hd => by simpa using List.all_eq_true.mp hx d hd⟩

/-- **The closed units are closed** (proved). -/
theorem closedUnits_closed (vs : Verdicts) : ClosedIn vs (closedUnits vs) := by
  unfold closedUnits
  dsimp only
  split
  · rename_i h; exact closedCheck_sound h
  · intro u hu; cases hu

/-! ## The closure of mode 8's verdicts -/

/-- **Mode 8's verdicts of a file**, as its CLI loop prints them: per
selected unit, its identity and, where `passGroup` accepts its group, the
dependencies it prints. -/
def fileVerdicts (f : FilePlans) (selection : Option (List String)) (givenLines : Std.HashMap String Json)
    (fuel : Nat) (compare : Bool) (debugNode repeats : Nat) (given : Option (Std.HashMap String Json))
    (observe : Option String) (counting : Bool) : Verdicts :=
  (f.fr.selected selection).map fun i => (f.fr.unitId i,
    ((f.withHeadFacts givenLines false).passGroup fuel (f.fr.group i) compare debugNode repeats given observe
      counting).2.toOption)

theorem lookup_mem {vs : Verdicts} {u : String} {v : Option (List String)} (h : vs.lookup u = some v) :
    (u, v) ∈ vs := by
  induction vs with
  | nil => cases h
  | cons p vs ih =>
    obtain ⟨k, w⟩ := p
    by_cases hk : u = k
    · subst hk
      simp only [List.lookup, beq_self_eq_true] at h
      injection h with h; subst h
      exact List.mem_cons_self
    · have hne : (u == k) = false := by simpa using hk
      simp only [List.lookup, hne] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- **Every closed unit of mode 8's verdicts is safe** (proved, under H1–H4
as `passUnit_safe`): a unit of `closedUnits (fileVerdicts …)` is a selected
unit whose group `passGroup` accepts, so every member of its group is safe;
and every unit its group depends on is closed too (`closedUnits_closed`). -/
theorem closedUnits_safe
    (hrun : ∀ (ι : Type) [Labels ι], RunSound ι) (hkeep : ∀ (ι : Type) [Labels ι], RunKeepsSummaries ι)
    (hgroup : PassGroupChecks)
    {ast : Json} {fileKey : String} {budget : PositiveCertificates.SearchBudget}
    {selection : Option (List String)} {standIns : StandIns} {force : List String} {f : FilePlans}
    {givenLines : Std.HashMap String Json} {fuel : Nat} {compare : Bool} {debugNode repeats : Nat}
    {given : Option (Std.HashMap String Json)} {observe : Option String} {counting : Bool}
    (hplans : fragmentPlans ast fileKey budget selection standIns force = .ok f) {u : String}
    (hu : u ∈ closedUnits (fileVerdicts f selection givenLines fuel compare debugNode repeats given observe counting)) :
    ∃ i, f.fr.unitId i = u ∧ PassUnitSafe (f.withHeadFacts givenLines false) i := by
  obtain ⟨ds, ha, -⟩ := closedUnits_closed _ u hu
  unfold Verdicts.accepted at ha
  cases hl : (fileVerdicts f selection givenLines fuel compare debugNode repeats given observe counting).lookup u with
  | none => rw [hl] at ha; cases ha
  | some v =>
    rw [hl] at ha
    simp only [Option.join_some] at ha
    subst ha
    have hm := lookup_mem hl
    simp only [fileVerdicts, List.mem_map, Prod.mk.injEq] at hm
    obtain ⟨i, hi, hid, hv⟩ := hm
    cases hp : ((f.withHeadFacts givenLines false).passGroup fuel (f.fr.group i) compare debugNode repeats given
        observe counting).2 with
    | error e => rw [hp] at hv; cases hv
    | ok d => exact ⟨i, hid, passUnit_safe hrun hkeep hgroup hplans hi hp⟩

/-! ## The linking induction -/

/-- **Linking** (proved): over a set closed under dependencies, interfaces
`Meets u n` (step-indexed by the budget `n`) that hold at budget `0`, and
that each unit establishes at `n + 1` from its dependencies at every budget
up to `n` (itself among them, for recursion), hold at every budget. A
dependency cycle needs no order on units: the budget decreases. -/
theorem link {U : Type} (S : U → Prop) (deps : U → List U) (Meets : U → Nat → Prop)
    (hclosed : ∀ u, S u → ∀ d ∈ deps u, S d)
    (hzero : ∀ u, Meets u 0)
    (hstep : ∀ u, S u → ∀ n, (∀ m ≤ n, Meets u m) → (∀ d ∈ deps u, ∀ m ≤ n, Meets d m) → Meets u (n + 1)) :
    ∀ n, ∀ u, S u → Meets u n := by
  have h : ∀ n, ∀ m ≤ n, ∀ u, S u → Meets u m := by
    intro n
    induction n with
    | zero => intro m hm u _; rw [Nat.le_zero.mp hm]; exact hzero u
    | succ n ih =>
      intro m hm u hu
      rcases Nat.lt_or_eq_of_le hm with hlt | rfl
      · exact ih m (Nat.lt_succ_iff.mp hlt) u hu
      · exact hstep u hu n (fun m hm => ih m hm u hu) (fun d hd m hm => ih m hm d (hclosed u hu d hd))
  exact fun n u hu => h n n (Nat.le_refl n) u hu

/-- **A file's closed units meet their interfaces** (proved, under the
realization hypothesis `hreal`): every unit of `closedUnits` meets its
interface at every budget, where each accepted unit establishes its
interface one budget up from its group's and its dependencies'. -/
theorem closedUnits_linked (vs : Verdicts) (Meets : String → Nat → Prop)
    (hzero : ∀ u, Meets u 0)
    (hreal : ∀ u ds, vs.accepted u = some ds → ∀ n, (∀ m ≤ n, Meets u m) →
      (∀ d ∈ ds, ∀ m ≤ n, Meets d m) → Meets u (n + 1)) :
    ∀ u ∈ closedUnits vs, ∀ n, Meets u n := by
  have hc := closedUnits_closed vs
  let deps : String → List String := fun u => (vs.accepted u).getD []
  have key := link (fun u => u ∈ closedUnits vs) deps Meets
    (fun u hu d hd => by
      obtain ⟨ds, ha, hds⟩ := hc u hu
      simp only [deps, ha, Option.getD_some] at hd
      exact hds d hd)
    hzero
    (fun u hu n hself hdeps => by
      obtain ⟨ds, ha, _⟩ := hc u hu
      exact hreal u ds ha n hself (fun d hd => hdeps d (by simp only [deps, ha, Option.getD_some]; exact hd)))
  exact fun u hu n => key n u hu

/-! ## A discharged interface at a caller's slot -/

section
variable {ι : Type}

/-- The interface of a function value: its value meets its type at budget
`n` in every world. -/
def MeetsAt (G : PositiveGraphs.NormalGraph ι) (A : Ty ι) (v : Tm) (n : Nat) : Prop :=
  ∀ W : WorldT n, meaning G A n W v

/-- **A linked environment meets the inputs** (proved): where each slot `i`
the link names holds the module value of its callee, at the type its
callee's interface states, and that interface holds at the budget, and every
other slot meets its type, the environment meets the inputs (`EnvOk`). So
`RequestSafe`'s entry premise holds of a caller run in the module's
environment once its callees' interfaces are discharged. -/
theorem envOk_of_linked {G : PositiveGraphs.NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat} {W : WorldT n}
    {U : Type} (link : Nat → Option U) (value : U → Tm) (iface : U → Ty ι)
    (hscoped : ∀ i, Scoped 0 (ρ i))
    (hlinked : ∀ i u, link i = some u → ρ i = value u ∧ Γ[i]? = some (iface u))
    (hmeets : ∀ i u, link i = some u → MeetsAt G (iface u) (value u) n)
    (hrest : ∀ i A, link i = none → Γ[i]? = some A → meaning G A n W (ρ i)) :
    EnvOk G Γ ρ n W := by
  refine ⟨hscoped, fun i A hA => ?_⟩
  cases hl : link i with
  | none => exact hrest i A hl hA
  | some u =>
    obtain ⟨hv, hty⟩ := hlinked i u hl
    rw [hty] at hA
    injection hA with hA
    subst hA
    rw [hv]
    exact hmeets i u hl W

end

end Verification.SourceClaimJson.PassUnit
