import Verification.Source.Claims.PassUnitLink

/-! # The single pass's unit theorem: realizing a file's interfaces

A unit's acceptance assumes, through `EnvOk` of its inputs, values for its
module slots. This module defines the environment that discharges them (the
module's functions as graph code closures, `ModuleCode`, at every depth of
unfolding, `approx`), proves that a closure whose code meets its signatures
meets its arrow wherever its captures meet theirs below the budget
(`closure_meets_below`), that a safe unit request is graph code at its
signature (`unitSpec_of_requestSafe`), and that over a set of units closed
under their links every unfolding meets its interface at every budget
(`approx_meets`), so that each closed unit's inputs are met by the module's
environment (`approx_envOk`). The definitions and the residue are presented in
docs/drafts/pass-unit-theorem.md, section 4. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-! ## The module's environment -/

/-- What a module slot of a unit's frame holds: the value of a module
function of the file (a unit, linked), or a value from outside the file's
functions (an import, a host value, a module constant or cell the
initialization binds). -/
inductive Slot (U : Type) where
  | linked (u : U)
  | outside (v : Tm)

/-- **A module function's code**: its graph code (arity, node lists, start,
kind), the object it is (fields and identity), and per capture, in frame
order after its receiver and parameters, its type and what it holds. -/
structure ModuleCode (ι U : Type) where
  arity : Nat
  exprs : List Tm
  conts : List (ControlFlow.Continuation × Option ControlFlow.Target)
  start : Nat
  kind : Invoke
  fields : List (PropKey × Nat)
  oid : Nat
  captures : List (Ty ι)
  slots : List (Slot U)

/-- What a slot holds, with each linked function's value given by `f`. -/
def Slot.valueWith {U : Type} (f : U → Tm) : Slot U → Tm
  | .linked u => f u
  | .outside v => v

/-- The closure of a module function's code over the captured values `vs`. -/
def ModuleCode.closure {ι U : Type} (c : ModuleCode ι U) (vs : List Tm) : Tm :=
  .objAt c.fields (.graph c.arity c.exprs c.conts c.start vs c.kind false) c.oid

/-- The captured values of a function's closure at depth `n + 1`, its linked
functions given by `f` (the depth-`n` environment). -/
def ModuleCode.captured {ι U : Type} (c : ModuleCode ι U) (f : U → Tm) : List Tm :=
  c.slots.map (Slot.valueWith f)

/-- **The module's environment, unfolded `n` times**: each function's
closure, whose linked captures hold the other functions' closures unfolded
once less, and whose outside captures hold their values; at depth `0` the
linked captures hold `null`. A run of at most `n` steps calls through at most
`n` closures, so the depth-`n` environment is the one a budget-`n` run sees. -/
def approxEnv {ι U : Type} (code : U → ModuleCode ι U) : Nat → U → Tm
  | 0 => fun _ => .nul
  | n + 1 => fun u => (code u).closure ((code u).captured (approxEnv code n))

/-- The value of each module function at depth `n`: its closure over the
environment one depth below. -/
def approx {ι U : Type} (code : U → ModuleCode ι U) (n : Nat) (u : U) : Tm :=
  approxEnv code (n + 1) u

/-- Every outside value is a closed value. -/
def OutsideValues {ι U : Type} (code : U → ModuleCode ι U) : Prop :=
  ∀ u v, Slot.outside v ∈ (code u).slots → isVal v = true ∧ Scoped 0 v

theorem closure_scoped {ι U : Type} (c : ModuleCode ι U) {vs : List Tm} (h : ∀ v ∈ vs, Scoped 0 v) :
    Scoped 0 (c.closure vs) := by
  simpa [ModuleCode.closure, Scoped] using h

theorem captured_values {ι U : Type} {code : U → ModuleCode ι U} (ho : OutsideValues code) {f : U → Tm}
    (hf : ∀ d, isVal (f d) = true ∧ Scoped 0 (f d)) (u : U) :
    ∀ v ∈ (code u).captured f, isVal v = true ∧ Scoped 0 v := by
  intro v hv
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hv
  cases s with
  | linked d => exact hf d
  | outside v => exact ho u v hs

theorem approxEnv_value {ι U : Type} {code : U → ModuleCode ι U} (ho : OutsideValues code) :
    ∀ n u, isVal (approxEnv code n u) = true ∧ Scoped 0 (approxEnv code n u) := by
  intro n
  induction n with
  | zero => intro u; exact ⟨rfl, by simp [approxEnv, Scoped]⟩
  | succ n ih =>
    intro u
    exact ⟨rfl, closure_scoped _ fun v hv => (captured_values ho ih u v hv).2⟩

theorem captured_get {ι U : Type} {c : ModuleCode ι U} {f : U → Tm} {k : Nat} {s : Slot U}
    (hs : c.slots[k]? = some s) : (c.captured f)[k]? = some (s.valueWith f) := by
  simp only [ModuleCode.captured, List.getElem?_map, hs, Option.map_some]

section
variable {ι : Type}

/-! ## A closure meets its arrow -/

/-- **A closure meets its arrow from captures meeting theirs below the
budget** (proved): graph code of fixed arity offering the signatures of `F`,
whose captured values meet their types at every budget below `n`, in every
world, meets `F` at `n` in every world. Every call of the closure runs its
code below the budget at which it is made. The induction of `offers_self`
with the self entry replaced by captures given at every smaller budget. -/
theorem closure_meets_below {G : NormalGraph ι} {arity E K start Cs vs} {kind : Invoke}
    {F : Ty ι} {L : List (CallEffects.Arrow (Ty ι))} {S : List (CallEffects.RestArrow (Ty ι))} (fs : List (PropKey × Nat)) {oid : Nat}
    (hr : Represents G F (.arrs L S)) (hk : KindOffers G kind L S)
    (ho : CodeOffers G arity E K start Cs false L S [])
    (hlen : Cs.length ≤ vs.length) (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs)
    {n : Nat} (hcaps : ∀ j < n, ∀ U : WorldT j, EnvOk G Cs (envOf vs .nul) j U) (W : WorldT n) :
    meaning G F n W (.objAt fs (.graph arity E K start vs kind false) oid) := by
  obtain ⟨hkind, hrows⟩ := hk
  have hbL : ∀ p ∈ L, KindBinds G kind p.receiver :=
    fun p hp => kindOffers_binds (hrows p (List.mem_append_left _ hp))
  have hbS : ∀ s ∈ S, KindBinds G kind s.receiver :=
    fun s hs => kindOffers_binds (hrows _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩)))
  have hself : Scoped 0 (.objAt fs (.graph arity E K start vs kind false) oid) := by simpa [Scoped] using hsc
  apply (represents_back hr n W _)
  refine ⟨⟨⟨fs, _, _, rfl, callable_of_kind hkind, hself⟩, ?_⟩, ⟨⟨fs, _, _, rfl, callable_of_kind hkind, hself⟩, ?_⟩⟩
  · intro q hq j hj U hx hu heap hh r hrv hrr args hvals ha hreq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    have henv := (hcaps j hj U).withSelf hlen hself
    exact ⟨_, .graph hrv hvals (hbL p hp j U r hrr),
      graph_invoke_at (ho p (List.mem_append_left _ hp)) henv
        (Values.withSelf hvalues rfl) hu hh hrr ha (fun F hF => hreq.2 F hF)⟩
  · intro q hq j hj U hx hu heap hh r hrv hrr args hvals ha hreq
    obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
    have hspec := ho _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, hsm, rfl⟩))
    have hle : arity ≤ s.arguments.1.length := hspec.1
    have hbelow : s.fixed.effect.below arity = true := hspec.2.1
    have henv := (hcaps j hj U).withSelf hlen hself
    have hsafe := graph_invoke_at hspec henv (Values.withSelf hvalues rfl) hu hh
      (args := args.take s.arguments.1.length) hrr
      (by simpa [CallEffects.RestArrow.mapWith, CallEffects.Contract.map, CallEffects.RestArrow.fixed] using ha.1)
      (fun F hF => (CallEffects.Effect.pre_take hbelow hle hF r args heap).mpr
        (hreq.2 F (by simpa [CallEffects.RestArrow.mapWith, CallEffects.Contract.map, CallEffects.RestArrow.fixed] using hF)))
    have hp : CallArguments.parameters arity (args.take s.arguments.1.length) =
        CallArguments.parameters arity args := by
      rw [← CallArguments.parameters_take arity (args.take _), List.take_take,
        Nat.min_eq_left hle, CallArguments.parameters_take]
    rw [hp, CallEffects.Effect.promised_take (e := s.fixed.effect) hbelow hle] at hsafe
    exact ⟨_, .graph hrv hvals (hbS s hsm j U r hrr), HeapObservations.SafePostExc.weaken
      (fun _ _ h => CallEffects.Effect.post_args (CallEffects.Effect.below_ensures hbelow)
      (CallEffects.Effect.below_grows hbelow) (CallEffects.Effect.below_write hbelow)
      (CallEffects.Effect.below_regions hbelow) h)
      (fun _ h => CallEffects.Effect.excPost_args (CallEffects.Effect.below_regions hbelow) h) hsafe⟩

theorem reassign_env (G : NormalGraph ι) : reassign G G.env = G := by
  cases G; rfl

end

/-! ## A safe unit request is graph code at its signature -/

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **A unit request is a code's**: unqualified, its inputs the code's frame
(receiver, parameters, then the captures), its program the code's node
lists, its start and goal the code's, no entry separation, the code's
precondition as its entry facts, and the code's footprint, fresh flag and
throw flag as its own. -/
structure UnitIsCode (r : SourceRequest σ ι) (c : CodeEntry ι) : Prop where
  unqualified : r.qualification = none
  inputs : r.inputs = codeFrame c.arity c.row c.captures c.store
  exprs : c.exprs = r.program.map (·.expression)
  conts : c.conts = r.program.map fun n => (n.continuation, n.handler)
  start : r.start = c.start
  goal : r.goal = c.goal
  separation : r.entrySeparation = {}
  indices : r.entryIndices = GraphCode.codeEntryIndices c
  footprint : r.footprint = c.row.effect.footprint
  fresh : r.fresh = c.row.effect.fresh
  onThrow : r.onThrow = c.row.effect.onThrow

omit [Labels ι] [StoreView σ ι] in
theorem codeBound_some {c : CodeEntry ι} {Φ : Footprints.Closed} {fresh onThrow : Bool}
    (h : codeBound c = some (Φ, fresh, onThrow)) :
    Φ = c.row.effect.footprint ∧ fresh = c.row.effect.fresh ∧ onThrow = c.row.effect.onThrow ∧
      (c.row.effect.footprint ≠ .top ∨ c.row.effect.onThrow = true ∨ c.row.effect.fresh = true) := by
  unfold codeBound at h
  split at h
  · cases h
  · rename_i hne
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, rfl, rfl, ?_⟩
      by_cases hfp : c.row.effect.footprint = .top
      · right
        cases hf : c.row.effect.fresh <;> cases ho : c.row.effect.onThrow <;> simp_all
      · exact Or.inl hfp

/-- **A safe unit request is graph code at its signature** (proved): where a
unit request is a code's (`UnitIsCode`) and the code meets the conditions
`passGroup` checks of a code (`codeConditions`), the request's safety
(`RequestSafe`: its safety and footprint clauses) makes the code meet its
signature at every assignment (`CodeEntry.Spec`). -/
theorem unitSpec_of_requestSafe {r : SourceRequest σ ι} {c : CodeEntry ι}
    (hsafe : RequestSafe r) (hu : UnitIsCode r c) (hcond : codeConditions c = true) :
    ∀ η, c.Spec (reassign (RequestJson.graph r.toRequest) η) := by
  have hadm : ∀ η, r.Admits η := fun η => by simp [SourceRequest.Admits, hu.unqualified]
  have hprog : r.program = GraphCode.program c.exprs c.conts := by
    rw [hu.exprs, hu.conts, program_nodes]
  have hgoto : ∀ L d, gotoOf r.program r.start L d = .goto c.exprs c.conts c.start L d := by
    intro L d; simp only [gotoOf, hu.exprs, hu.conts, hu.start]
  apply codeSpec_of_clauses hcond
  · intro η n W h ρ he
    have := hsafe.1 η (hadm η) n W h ρ (by rw [hu.inputs, hu.separation, hu.indices]; exact he)
    rw [hprog, hu.goal, hu.start] at this
    exact this
  · intro Φ fresh onThrow hb η n W h L d he hvals hd
    obtain ⟨rfl, rfl, rfl, hne⟩ := codeBound_some hb
    have hpre : r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true := by
      rw [hu.footprint, hu.onThrow, hu.fresh]; exact hne
    have := hsafe.2.1 hpre η n W h L d (by rw [hu.inputs, hu.separation, hu.indices]; exact he) hvals hd
    rw [hgoto, hu.goal, hu.footprint, hu.fresh, hu.onThrow] at this
    exact this

end

/-! ## The module's environment meets every closed unit's interface -/

section
variable {ι U : Type}

/-- **What a unit of the module must meet to be realized**: its interface
`iface u` presents one clause of signatures `L` and variadic signatures `Sg`
which its code offers, kind included (`CodeOffers`, `KindOffers`); each of its
captures is a slot; each linked capture is read at its callee's interface
and its callee is in the set (`S`): the slot agreement; and each outside
capture's value meets its type at every budget in every world: the
contract of the import, host value, stand-in or module value it holds. -/
def Realizes (G : NormalGraph ι) (code : U → ModuleCode ι U) (iface : U → Ty ι) (S : U → Prop) (u : U) :
    Prop :=
  ∃ (L : List (CallEffects.Arrow (Ty ι))) (Sg : List (CallEffects.RestArrow (Ty ι))),
    Represents G (iface u) (.arrs L Sg) ∧ KindOffers G (code u).kind L Sg ∧
    CodeOffers G (code u).arity (code u).exprs (code u).conts (code u).start (code u).captures false L Sg [] ∧
    (code u).captures.length = (code u).slots.length ∧
    (∀ (k : Nat) d, (code u).slots[k]? = some (Slot.linked d) → (code u).captures[k]? = some (iface d) ∧ S d) ∧
    (∀ (k : Nat) v A, (code u).slots[k]? = some (Slot.outside v) → (code u).captures[k]? = some A →
      ∀ j (V : WorldT j), meaning G A j V v)

/-- The captures of a realized unit meet their types at `j`, where every
linked function's value, given by `f`, meets its interface there. -/
theorem captures_envOk {G : NormalGraph ι} {code : U → ModuleCode ι U} {iface : U → Ty ι} {S : U → Prop}
    {u : U} (hr : Realizes G code iface S u) (ho : OutsideValues code) {f : U → Tm}
    (hf : ∀ d, isVal (f d) = true ∧ Scoped 0 (f d)) {j : Nat} {V : WorldT j}
    (hm : ∀ d, S d → meaning G (iface d) j V (f d)) :
    EnvOk G (code u).captures (envOf ((code u).captured f) .nul) j V := by
  obtain ⟨L, Sg, -, -, -, hlen, hagree, hout⟩ := hr
  apply EnvOk.envOf_nul (fun v hv => (captured_values ho hf u v hv).2)
    (by simp [ModuleCode.captured, hlen])
  intro k A hA v hv
  have hk : k < (code u).slots.length := by
    have := (List.getElem?_eq_some_iff.mp hA).1; omega
  have hs : (code u).slots[k]? = some (code u).slots[k] := List.getElem?_eq_getElem hk
  rw [captured_get hs] at hv
  injection hv with hv
  subst hv
  cases hsk : (code u).slots[k] with
  | linked d =>
    rw [hsk] at hs
    obtain ⟨hty, hd⟩ := hagree k d hs
    rw [hty] at hA; injection hA with hA; subst hA
    exact hm d hd
  | outside w =>
    rw [hsk] at hs
    exact hout k w A hs hA j V

/-- **The module's environment meets every closed unit's interface**
(proved): over a set `S` of units each realized against `S`, the value of
each unit unfolded `n` times meets its interface at every budget up to `n`
in every world. By induction on `n`: a call at budget `m ≤ n + 1` runs the
code below `m`, where the captured values, unfolded `n` times, meet their
interfaces. Recursion and cycles go through, the budget decreasing. -/
theorem approx_meets {G : NormalGraph ι} {code : U → ModuleCode ι U} {iface : U → Ty ι} {S : U → Prop}
    (hreal : ∀ u, S u → Realizes G code iface S u) (ho : OutsideValues code) :
    ∀ n u, S u → ∀ m ≤ n, ∀ W : WorldT m, meaning G (iface u) m W (approx code n u) := by
  intro n
  induction n with
  | zero =>
    intro u hu m hm W
    obtain ⟨L, Sg, hrep, hk, hoff, hlen, -, -⟩ := hreal u hu
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    exact closure_meets_below (code u).fields hrep hk hoff (by simp [ModuleCode.captured, hlen])
      (fun v hv => (captured_values ho (approxEnv_value ho 0) u v hv).2)
      (fun v hv => (captured_values ho (approxEnv_value ho 0) u v hv).1)
      (fun j hj => absurd hj (Nat.not_lt_zero j)) W
  | succ n ih =>
    intro u hu m hm W
    obtain ⟨L, Sg, hrep, hk, hoff, hlen, -, -⟩ := hreal u hu
    exact closure_meets_below (code u).fields hrep hk hoff (by simp [ModuleCode.captured, hlen])
      (fun v hv => (captured_values ho (approxEnv_value ho (n + 1)) u v hv).2)
      (fun v hv => (captured_values ho (approxEnv_value ho (n + 1)) u v hv).1)
      (fun j hj V => captures_envOk (hreal u hu) ho (approxEnv_value ho (n + 1))
        (fun d hd => ih d hd j (by omega) V)) W

/-- **Each closed unit's captures are met by the module's environment**
(proved): the values the depth-`n` environment captures for a unit of `S`
meet the unit's capture types at budget `n` in every world. With the
receiver and the arguments meeting the unit's parameters, this is the entry
premise of the unit's `RequestSafe` (`envOk_of_linked` states the same for
a caller's input slots). -/
theorem approx_captures_envOk {G : NormalGraph ι} {code : U → ModuleCode ι U} {iface : U → Ty ι}
    {S : U → Prop} (hreal : ∀ u, S u → Realizes G code iface S u) (ho : OutsideValues code)
    (n : Nat) {u : U} (hu : S u) (W : WorldT n) :
    EnvOk G (code u).captures (envOf ((code u).captured (approx code n)) .nul) n W :=
  captures_envOk (hreal u hu) ho (fun d => approxEnv_value ho (n + 1) d)
    (fun d hd => approx_meets hreal ho n d hd n (Nat.le_refl n) W)

/-- **The interfaces as `link` states them** (proved): the realization
premise of the linking induction (`closedUnits_linked`'s `hreal`) holds of
the module's environment, with `Meets u n` the unfolding `n` meeting the
interface at every budget up to `n`. -/
theorem approx_link {G : NormalGraph ι} {code : U → ModuleCode ι U} {iface : U → Ty ι} {S : U → Prop}
    (hreal : ∀ u, S u → Realizes G code iface S u) (ho : OutsideValues code) :
    ∀ n u, S u → (fun u n => ∀ m ≤ n, MeetsAt G (iface u) (approx code n u) m) u n :=
  fun n u hu m hm W => approx_meets hreal ho n u hu m hm W

end

end Verification.SourceClaimJson.PassUnit
