import Verification.Source.Claims.PassUnitLink
import Verification.Semantics.ComponentTags

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
docs/SINGLE-PASS-THEOREM.md, section 4. -/

namespace Verification.SourceClaimJson.PassUnit
variable {ε : Verification.HeapKnowledge.EntryState}
open Lean ProgramTyping RequestJson SourceElaboration ControlFlow PositiveGraphs PositiveRules LabelStore

/-! ## The module's environment -/

/-- What a module slot of a unit's frame holds: the value of a module
function of the file (a unit, linked), or values from outside the file's
functions (an import, a host value, a module constant or cell the
initialization binds), one per depth of unfolding: an import's value is its
own module's environment at that depth. -/
inductive Slot (U : Type) where
  | linked (u : U)
  | outside (v : Nat → Tm)

/-- **A module function's code**: its graph code (arity, node lists, start,
kind), the object it is (fields and identity), per capture, in frame order
after its receiver and parameters, its type and what it holds, and the
separation of its frames. -/
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
  /-- The separation its calls' frames assume: its module cells' apart
  (`moduleCellSeparation`), at the frame's depth. -/
  sep : HeapSeparation.Separation := {}
  /-- The component whose code it is: the ghost tag of its frames. -/
  comp : ComponentTag

/-- What a slot holds at depth `i`, with each linked function's value given
by `f`. -/
def Slot.valueAt {U : Type} (f : U → Tm) (i : Nat) : Slot U → Tm
  | .linked u => f u
  | .outside v => v i

/-- The closure of a module function's code over the captured values `vs`,
its frames tagged with its component. -/
def ModuleCode.closure {ι U : Type} (c : ModuleCode ι U) (vs : List Tm) : Tm :=
  .objAt c.fields (.graph c.arity c.exprs c.conts c.start vs c.kind false c.comp) c.oid

/-- The captured values of a function's closure at depth `i + 1`, its linked
functions given by `f` (the depth-`i` environment). -/
def ModuleCode.captured {ι U : Type} (c : ModuleCode ι U) (f : U → Tm) (i : Nat) : List Tm :=
  c.slots.map (Slot.valueAt f i)

/-- **The module's environment, unfolded `n` times**: each function's
closure, whose linked captures hold the other functions' closures unfolded
once less, and whose outside captures hold their values at that depth; at depth `0` the
linked captures hold `null`. A run of at most `n` steps calls through at most
`n` closures, so the depth-`n` environment is the one a budget-`n` run sees. -/
def approxEnv {ι U : Type} (code : U → ModuleCode ι U) : Nat → U → Tm
  | 0 => fun _ => .nul
  | n + 1 => fun u => (code u).closure ((code u).captured (approxEnv code n) n)

/-- The value of each module function at depth `n`: its closure over the
environment one depth below. -/
def approx {ι U : Type} (code : U → ModuleCode ι U) (n : Nat) (u : U) : Tm :=
  approxEnv code (n + 1) u

/-- Every outside value is a closed value, at every depth. -/
def OutsideValues {ι U : Type} (code : U → ModuleCode ι U) : Prop :=
  ∀ u v, Slot.outside v ∈ (code u).slots → ∀ i, isVal (v i) = true ∧ Scoped 0 (v i)

theorem closure_scoped {ι U : Type} (c : ModuleCode ι U) {vs : List Tm} (h : ∀ v ∈ vs, Scoped 0 v) :
    Scoped 0 (c.closure vs) := by
  simpa [ModuleCode.closure, Scoped] using h

theorem captured_values {ι U : Type} {code : U → ModuleCode ι U} (ho : OutsideValues code) {f : U → Tm}
    (hf : ∀ d, isVal (f d) = true ∧ Scoped 0 (f d)) (u : U) (i : Nat) :
    ∀ v ∈ (code u).captured f i, isVal v = true ∧ Scoped 0 v := by
  intro v hv
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hv
  cases s with
  | linked d => exact hf d
  | outside v => exact ho u v hs i

theorem approxEnv_value {ι U : Type} {code : U → ModuleCode ι U} (ho : OutsideValues code) :
    ∀ n u, isVal (approxEnv code n u) = true ∧ Scoped 0 (approxEnv code n u) := by
  intro n
  induction n with
  | zero => intro u; exact ⟨rfl, by simp [approxEnv, Scoped]⟩
  | succ n ih =>
    intro u
    exact ⟨rfl, closure_scoped _ fun v hv => (captured_values ho ih u n v hv).2⟩

theorem captured_get {ι U : Type} {c : ModuleCode ι U} {f : U → Tm} {i k : Nat} {s : Slot U}
    (hs : c.slots[k]? = some s) : (c.captured f i)[k]? = some (s.valueAt f i) := by
  simp only [ModuleCode.captured, List.getElem?_map, hs, Option.map_some]

/-! ## Stable unfoldings -/

/-- **An acyclic module of constant outside values**, ranked by `ht`: each
linked slot of a function names a function of smaller height, and each
outside slot holds one value at every depth (an audited realm value). -/
def StableLayout {ι U : Type} (code : U → ModuleCode ι U) (ht : U → Nat) : Prop :=
  ∀ u s, s ∈ (code u).slots → (∃ u', s = .linked u' ∧ ht u' < ht u) ∨ ∃ c, s = .outside fun _ => c

/-- **One unfolding past the height** (`approx_stable`, the framed
acceptance draft's "Initialization"): in an acyclic module whose outside
slots are constant in the depth, a function's closure is the same at every
depth from its height on. With no linked slot (height `0`) it is the same
at every depth. -/
theorem approx_stable {ι U : Type} {code : U → ModuleCode ι U} {ht : U → Nat} (hs : StableLayout code ht) :
    ∀ u n k, ht u ≤ n → ht u ≤ k → approx code n u = approx code k u := by
  suffices h : ∀ m u, ht u ≤ m → ∀ n k, ht u ≤ n → ht u ≤ k → approx code n u = approx code k u from
    fun u => h (ht u) u (Nat.le_refl _)
  intro m
  induction m with
  | zero =>
    intro u hu n k _ _
    simp only [approx, approxEnv]
    congr 1
    unfold ModuleCode.captured
    apply List.map_congr_left
    intro s hm
    rcases hs u s hm with ⟨u', rfl, hlt⟩ | ⟨c, rfl⟩
    · omega
    · rfl
  | succ m ih =>
    intro u hu n k hn hk
    simp only [approx, approxEnv]
    congr 1
    unfold ModuleCode.captured
    apply List.map_congr_left
    intro s hm
    rcases hs u s hm with ⟨u', rfl, hlt⟩ | ⟨c, rfl⟩
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact ih u' (by omega) n' k' (by omega) (by omega)
    · rfl

section
variable {ι : Type}

/-! ## A module row's specification -/

/-- **A module function's code at one of its signatures** (`RowSpec`): code
of `arity`, collecting no rest, whose effect is one module code realizes
(`Effect.belowRow`: below its arity, a postcondition over the result, the
receiver and its parameters admitted), safe, run at every component, from
every frame meeting the signature's, its precondition and the separation
`sep`, at the signature's result and its specification on both exits
(`Exits.exitPostW`). A run's component is ghost
(`HeapObservations.SafePostExcV.goto_comp_iff`), so safety at one component,
as a module closure's code has (`none`: `ModuleCode.closure`), is safety at
every one. `GraphCodeSpec` at no rest spine, at `sep = {}` and with no
postcondition, is one (`rowSpec_of_graphCodeSpec`). -/
def RowSpec (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (row : CallEffects.Arrow (Ty ι)) (sep : HeapSeparation.Separation) : Prop :=
  arity ≤ row.arguments.length ∧ row.effect.belowRow arity = true ∧
  ∀ n W h L comp, EnvOk G (codeFrame arity row Cs none) (envOf L .nul) n W → WorldAdm W →
    HeapOk n W h → RefsOk W (.goto E K start L .nul comp) → CallArguments.Values L →
    PreAt row.effect (none : Option (Ty ι)) L h → HeapSeparation.Holds sep (envOf L .nul) →
    ∀ r args, FrameValues arity (none : Option (Ty ι)) L r args →
      HeapObservations.SafePostExcV (excOf G)
        (row.effect.result (meaning G row.result) (framePromised row.effect (frameOffset (none : Option (Ty ι))) L))
        (row.effect.schema.exitPostW .normal r args W h) (row.effect.schema.exitPostW .exceptional r args W h)
        n W h (.goto E K start L .nul comp)

/-- **Graph code at a signature is module code at it** (proved). -/
theorem rowSpec_of_graphCodeSpec {G : NormalGraph ι} {arity E K start Cs row}
    (hs : GraphCodeSpec G arity E K start Cs row) : RowSpec G arity E K start Cs row {} :=
  ⟨hs.1, hs.2.1,
    fun n W h L comp he hw hh hgo hv hpre _ r args hf => hs.2.2.2 n W h L comp he hw hh hgo hv hpre r args hf⟩

/-- A promise's results meet a plain result admitting them (proved). -/
theorem promiseAdmits_result [DecidableEq ι] {G : NormalGraph ι} {R T : Ty ι} {π : CallEffects.TypePromise}
    (h : promiseAdmits G R π = true) (a : Tm) :
    ∀ k W u, π.result (meaning G T) a k W u → meaning G R k W u := by
  intro k W u hu
  cases π with
  | guards q =>
    simp only [promiseAdmits, Bool.and_eq_true] at h
    rcases hu with ⟨rfl, -⟩ | rfl
    · simpa using BranchRefinement.booleanMember_sound h.1 k W
    · simpa using BranchRefinement.booleanMember_sound h.2 k W
  | asserts q =>
    obtain ⟨rfl, -⟩ := hu
    exact PromiseCalls.admitsUndef_sound h k W

/-- Dropping a promise keeps an effect one module code realizes (proved). -/
theorem belowRow_promise_none {e : CallEffects.Effect} {n : Nat} (h : e.belowRow n = true) :
    ({ e with promise := none } : CallEffects.Effect).belowRow n = true := by
  simp only [CallEffects.Effect.belowRow, CallEffects.Effect.entryBelow, CallEffects.Effect.promiseBelow,
    Bool.and_eq_true] at h ⊢
  exact ⟨⟨trivial, h.1.2⟩, h.2⟩

/-- **A promise row's code meets its plain row** (proved): code meeting a
signature stating the promise `π` as a module row meets, at the same
separation, the plain row beside it (`promisePlain`) whose result admits
the promise's results. The frame, the precondition and both postconditions
read no promise; a run's normal value, `true` or `false` for a guard,
`undefined` for an assertion, is in the plain result. -/
theorem rowSpec_plain_of_promise [DecidableEq ι] {G : NormalGraph ι} {arity E K start Cs}
    {p : CallEffects.Arrow (Ty ι)} {sep : HeapSeparation.Separation} {π : CallEffects.TypePromise} {R : Ty ι}
    (hp : p.effect.promise = some π) (hR : promiseAdmits G R π = true)
    (hs : RowSpec G arity E K start Cs p sep) : RowSpec G arity E K start Cs (promisePlain p R) sep := by
  refine ⟨hs.1, belowRow_promise_none hs.2.1, ?_⟩
  intro n W h L comp he hw hh hgo hv hpre hsep r args hf
  have hrun := hs.2.2 n W h L comp he hw hh hgo hv hpre hsep r args hf
  have hres : ∀ a, p.effect.result (meaning G p.result) a = π.result (meaning G p.result) a := by
    intro a; simp [CallEffects.Effect.result, hp]
  rw [hres] at hrun
  show HeapObservations.SafePostExcV (excOf G) (meaning G R) (p.effect.schema.exitPostW .normal r args W h)
    (p.effect.schema.exitPostW .exceptional r args W h) n W h _
  exact HeapObservations.SafePostExcV.mono_result (fun j W' u hu => promiseAdmits_result hR _ j W' u hu) hrun

/-- **Invoking a module row's code from a frame at the call's own level**
(proved): as `graph_invoke_at`, the frame's separation given, the run at
any component `comp`. -/
theorem row_invoke_at {G : NormalGraph ι} {arity E K start Cs row vs sep} {comp : ComponentTag}
    (hs : RowSpec G arity E K start Cs row sep) {j : Nat} {U : WorldT j}
    (hvs : EnvOk G Cs (envOf vs .nul) j U) (hvalues : CallArguments.Values vs)
    (hu : WorldAdm U) {heap : Heap} (hh : HeapOk j U heap) {r : Tm} (hr : meaning G row.receiver j U r)
    {args : List Tm} (ha : ArgsShort (row.arguments.map (meaning G)) j U args)
    (hq : ∀ F ∈ row.effect.pre, F.HoldsAt ⟨CallEffects.callEnv r args, heap⟩ (CallEffects.callEnv r args) heap)
    (hsep : HeapSeparation.Holds sep (envOf (r :: CallArguments.parameters arity args ++ vs) .nul))
    (hgo : RefsOk U (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul comp)) :
    HeapObservations.SafePostExcV (excOf G) (row.effect.result (meaning G row.result) (row.effect.promised args))
      (row.effect.schema.exitPostW .normal r args U heap) (row.effect.schema.exitPostW .exceptional r args U heap) j U heap
      (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul comp) := by
  have hx : WExt (trunc j (Nat.le_refl j) U) U := by rw [trunc_id]; exact WExt_refl U
  have hb := CallEffects.Effect.belowRow_entry hs.2.1
  have hsafe := hs.2.2 j U heap _ comp (frame_envOk hs.1 hvs (Nat.le_refl j) hx hr ha) hu hh hgo (by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (meaning_value hr).1
    · rcases List.mem_append.mp hv with hv | hv
      · exact CallArguments.parameters_property (P := fun v => isVal v = true) rfl
          (ArgsT_values (fun A hA => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hA); exact meaning_valOnly G a) ha.2.1) v hv
      · exact hvalues v hv)
    (fun _ F hF => (CallEffects.Effect.pre_frame hb (F := F) hF r args vs .nul heap).mp (hq F hF))
    hsep r args ⟨[], vs, rfl, rfl⟩
  have hp := framePromised_params hb [r] args vs
  simp only [List.length_singleton, List.singleton_append] at hp
  have hp' : framePromised row.effect 1 (r :: CallArguments.parameters arity args ++ vs) =
      row.effect.promised args := hp
  rw [show frameOffset (none : Option (Ty ι)) = 1 from rfl, hp'] at hsafe
  exact hsafe

/-- **The signatures a module function's code offers** (`RowOffers`): each
row of its clause (`offerRows`) at the separation `sep`. -/
def RowOffers (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (L : List (CallEffects.Arrow (Ty ι))) (S : List (CallEffects.RestArrow (Ty ι)))
    (sep : HeapSeparation.Separation) : Prop :=
  ∀ p ∈ offerRows L S, RowSpec G arity E K start Cs p sep

/-! ## A closure meets its arrow -/

/-- **A closure meets its arrow from captures meeting theirs below the
budget** (proved): code of fixed arity and of any component `comp`
offering the signatures of `F` as module rows (`RowOffers`) at the
separation `sep`, whose captured values meet
their types at every budget `j` below `n` in every world extending `W`
truncated to `j`, and every frame of whose calls meets `sep`, meets `F` at
`n` in `W`. Every call of the closure runs its code below the budget at
which it is made, in such a world. The induction of `offers_self` with the
self entry replaced by captures given at every smaller budget. -/
theorem closure_meets_below {G : NormalGraph ι} {arity E K start Cs vs} {kind : Invoke} {comp : ComponentTag}
    {F : Ty ι} {L : List (CallEffects.Arrow (Ty ι))} {S : List (CallEffects.RestArrow (Ty ι))} (fs : List (PropKey × Nat)) {oid : Nat}
    {sep : HeapSeparation.Separation}
    (hr : Represents G F (.arrs L S)) (hk : KindOffers G kind L S)
    (ho : RowOffers G arity E K start Cs L S sep)
    (hlen : Cs.length ≤ vs.length) (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs)
    (hsep : ∀ r args more, HeapSeparation.Holds sep (envOf (r :: CallArguments.parameters arity args ++ (vs ++ more)) .nul))
    {n : Nat} (W : WorldT n)
    (hcaps : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U → EnvOk G Cs (envOf vs .nul) j U) :
    meaning G F n W (.objAt fs (.graph arity E K start vs kind false comp) oid) := by
  obtain ⟨hkind, hrows⟩ := hk
  have hbL : ∀ p ∈ L, KindBinds G kind p.receiver :=
    fun p hp => kindOffers_binds (hrows p (List.mem_append_left _ hp))
  have hbS : ∀ s ∈ S, KindBinds G kind s.receiver :=
    fun s hs => kindOffers_binds (hrows _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩)))
  have hself : Scoped 0 (.objAt fs (.graph arity E K start vs kind false comp) oid) := by simpa [Scoped] using hsc
  apply (represents_back hr n W _)
  refine ⟨⟨⟨fs, _, _, rfl, callable_of_kind hkind, hself⟩, ?_⟩, ⟨⟨fs, _, _, rfl, callable_of_kind hkind, hself⟩, ?_⟩⟩
  · intro q hq
    intro j hj U hx hu heap hh hvr r hrv hrr hrref args hvals har ha hreq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    have henv := (hcaps j hj U hx).withSelf hlen hself
    exact ⟨_, .graph hrv hvals (hbL p hp j U r hrr),
      row_invoke_at (ho p (List.mem_append_left _ hp)) henv
        (Values.withSelf hvalues rfl) hu hh hrr ha (fun F hF => hreq.2 F hF) (hsep r args _)
        (goto_entry_refs (graph_code_refs hvr).1 (fun a ha => by
          rcases List.mem_append.mp ha with ha | ha
          · exact (graph_code_refs hvr).2 a ha
          · rw [List.mem_singleton.mp ha]; exact hvr) hrref har)⟩
  · intro q hq
    intro j hj U hx hu heap hh hvr r hrv hrr hrref args hvals har ha hreq
    obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
    have hspec := ho _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, hsm, rfl⟩))
    have hle : arity ≤ s.arguments.1.length := hspec.1
    have hrow : s.fixed.effect.belowRow arity = true := hspec.2.1
    have hbelow := CallEffects.Effect.belowRow_entry hrow
    have henv := (hcaps j hj U hx).withSelf hlen hself
    have hp : CallArguments.parameters arity (args.take s.arguments.1.length) =
        CallArguments.parameters arity args := by
      rw [← CallArguments.parameters_take arity (args.take _), List.take_take,
        Nat.min_eq_left hle, CallArguments.parameters_take]
    have hsafe := row_invoke_at (comp := comp) hspec henv (Values.withSelf hvalues rfl) hu hh
      (args := args.take s.arguments.1.length) hrr
      (by simpa [CallEffects.RestArrow.mapWith, CallEffects.Contract.map, CallEffects.RestArrow.fixed] using ha.1)
      (fun F hF => (CallEffects.Effect.pre_take hbelow hle (F := F) hF r args heap).mpr
        (hreq.2 F (by simpa [CallEffects.RestArrow.mapWith, CallEffects.Contract.map, CallEffects.RestArrow.fixed] using hF)))
      (by rw [hp]; exact hsep r args _)
      (goto_entry_refs (graph_code_refs hvr).1 (fun a ha => by
        rcases List.mem_append.mp ha with ha | ha
        · exact (graph_code_refs hvr).2 a ha
        · rw [List.mem_singleton.mp ha]; exact hvr) hrref (fun a ha => har a (List.mem_of_mem_take ha)))
    have hpr : s.fixed.effect.promised (args.take s.arguments.1.length) = s.fixed.effect.promised args :=
      CallEffects.Effect.promised_take hbelow hle args
    rw [hp, hpr] at hsafe
    -- Module code's signature is about its receiver and its parameters
    -- (`Effect.belowRow`): its exits at the actuals it takes hold at every
    -- longer list of actuals (`Effect.exitPost_take`).
    exact ⟨_, .graph hrv hvals (hbS s hsm j U r hrr), CallEffects.Effect.safe_exits_take hrow hle hu hh hsafe⟩

theorem reassign_env (G : NormalGraph ι) : reassign G G.env = G := by
  cases G; rfl

end

/-! ## A safe unit request is graph code at its signature -/

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **A unit request is a code's**: unqualified, its inputs the code's frame
(receiver, parameters, then the captures), its program the code's node
lists, its start and goal the code's, the code's precondition as its entry
facts, the signature's postcondition as its own (a function declaring
`this` reads each call position at the input slot of the same number), and
its run's bound (`RunBound.ofRequest`) the code's: the bounds of its
signature's exits (`exitBounds`) and its fresh flag. Its entry separation
is the separation of the code's frames (`rowSpec_of_requestSafe`). -/
structure UnitIsCode (r : SourceRequest σ ι) (c : CodeEntry ι) : Prop where
  unqualified : r.qualification = none
  inputs : r.inputs = codeFrame c.arity c.row c.captures c.spine
  exprs : c.exprs = r.program.map (·.expression)
  conts : c.conts = r.program.map fun n => (n.continuation, n.handler)
  start : r.start = c.start
  goal : r.goal = c.goal
  indices : r.entryIndices = GraphCode.codeEntryIndices c
  «ensures» : r.ensures = c.row.effect.schema.normal.facts
  bound : RunBound.ofRequest r.footprint r.onThrow r.fresh = (exitBounds c.row.effect, c.row.effect.schema.normal.freshResult)

omit [Labels ι] [StoreView σ ι] in
/-- **The bound a code's run is given**: the bounds of its signature's
exits and its fresh flag, given only where they are not `⊤` on both exits
without a fresh result. -/
theorem codeRunBound_some {c : CodeEntry ι} {Φ Ψ : Footprints.Closed} {fresh : Bool}
    (h : codeRunBound c = some (⟨Φ, Ψ⟩, fresh)) :
    (⟨Φ, Ψ⟩ : CallEffects.Exits Footprints.Closed) = exitBounds c.row.effect ∧ fresh = c.row.effect.schema.normal.freshResult ∧
      ¬((exitBounds c.row.effect).normal = .top ∧ (exitBounds c.row.effect).exceptional = .top ∧
        c.row.effect.schema.normal.freshResult = false) := by
  unfold codeRunBound runBounds at h
  split at h
  · cases h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, hf⟩ := h
    refine ⟨hb.symm, hf.symm, fun ⟨h1, h2, h3⟩ => hc ?_⟩
    simp [h1, h2, h3]

end

/-- Two postconditions of one run hold together, the throw's kept: its
execution is deterministic (proved). -/
theorem safePostExc_and {Ξ T : Fam} {Q Q' : HeapObservations.Post} {R : Heap → Prop} :
    ∀ {n W W' h t}, HeapObservations.SafePostExc Ξ T Q R n W h t → HeapObservations.SafePost Ξ T Q' n W' h t →
      HeapObservations.SafePostExc Ξ T (fun h' u => Q h' u ∧ Q' h' u) R n W h t := by
  intro n; induction n with
  | zero => intro _ _ _ _ hq _; exact hq
  | succ n ih =>
    intro W W' h t hq hr
    obtain ⟨hrf, hq⟩ := hq
    refine ⟨hrf, ?_⟩
    rcases hq with (⟨hv, ht, hq⟩ | ⟨hth, hR⟩) | ⟨U, h1, t1, hx, hu, st1, hh1, hq1⟩
    · rcases hr.2 with (⟨_, _, hr⟩ | hth') | ⟨_, _, _, _, _, st2, _, _⟩
      · exact .inl (.inl ⟨hv, ht, hq, hr⟩)
      · exact absurd hth' (val_not_thrown hv)
      · exact absurd st2 (value_no_step hv)
    · exact .inl (.inr ⟨hth, hR⟩)
    · rcases hr.2 with (⟨hv', _, _⟩ | hth') | ⟨U2, h2, t2, _, _, st2, _, hr2⟩
      · exact absurd st1 (value_no_step hv')
      · exact absurd st1 hth'.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st1 st2
        exact .inr ⟨U, h1, t1, hx, hu, st1, hh1, ih hq1 hr2⟩

section
variable {ι : Type}

/-- **A code safe from its frame, within its bound and meeting its
postcondition, is module code at its signature** (proved): a code meeting
the row conditions (`rowConditions`) and collecting no rest, whose graph is
safe at every assignment from its frame and the separation `sep`, within its
bound where it has one, and, where its signature states a postcondition,
returns with the postcondition's facts true of the result and its entry
frame, meets its signature as a module row (`RowSpec`) at `sep`: the run
(`codeRun_of_clauses`) with the facts at the call's values
(`Effect.ensures_frame`) establishes every postcondition the signature
exports on both exits (`exportsEstablished_sound`). -/
theorem rowSpec_of_clauses {G : NormalGraph ι} {c : CodeEntry ι} {sep : HeapSeparation.Separation}
    (hcond : rowConditions c = true) (hspine : c.spine = none)
    (hsafeG : ∀ η n W h ρ, EntryHolds (reassign G η) (codeFrame c.arity c.row c.captures c.spine) sep
      (GraphCode.codeEntryIndices c) ρ n W h →
      (∀ node ∈ GraphCode.program c.exprs c.conts, RefsOk W node.expression) → (∀ i, RefsOk W (ρ i)) →
      SafeGraph (excOf (reassign G η)) (GraphCode.program c.exprs c.conts)
        (GoalHolds (reassign G η) c.goal (c.goal.argument ρ)) n W h (.at c.start ρ))
    (hboundG : ∀ Φ Ψ fresh, codeRunBound c = some (⟨Φ, Ψ⟩, fresh) → ∀ η n W h L d,
      EntryHolds (reassign G η) (codeFrame c.arity c.row c.captures c.spine) sep (GraphCode.codeEntryIndices c)
        (envOf L d) n W h → RefsOk W (.goto c.exprs c.conts c.start L d none) →
        (∀ v ∈ L, isVal v = true) → isVal d = true →
      HeapObservations.SafePostExc (excOf (reassign G η))
        (GoalHolds (reassign G η) c.goal (c.goal.argument (envOf L d)))
        (fun h' v => Φ.Holds h h' ∧ (fresh = true → Footprints.FreshAt h.length v))
        (fun h' => Ψ ≠ .top → Ψ.Holds h h') n W h (.goto c.exprs c.conts c.start L d none))
    (hensG : c.row.effect.schema.normal.facts ≠ [] → ∀ η n W h L d,
      EntryHolds (reassign G η) (codeFrame c.arity c.row c.captures c.spine) sep (GraphCode.codeEntryIndices c)
        (envOf L d) n W h → RefsOk W (.goto c.exprs c.conts c.start L d none) →
      HeapObservations.SafePost (excOf (reassign G η))
        (GoalHolds (reassign G η) c.goal (c.goal.argument (envOf L d)))
        (fun h' v => GraphCode.EnsuresAt c.row.effect.schema.normal.facts ⟨envOf L d, h⟩ h' (push v (envOf L d))) n W h
        (.goto c.exprs c.conts c.start L d none)) :
    ∀ η, RowSpec (reassign G η) c.arity c.exprs c.conts c.start c.captures c.row sep := by
  intro η
  simp only [rowConditions, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hcond
  obtain ⟨⟨⟨harity, hrow⟩, _hreq⟩, hx⟩ := hcond
  refine ⟨harity, hrow, ?_⟩
  intro n W heap L comp he hw hh hgo hvalues hpre hsep r args hframe
  -- The premises state the run outside every component (`none`), and a
  -- run's component is ghost (`SafePostExcV.goto_comp_iff`).
  replace hgo := (goto_refsOk_comp_iff comp none).mp hgo
  apply (HeapObservations.SafePostExcV.goto_comp_iff none comp).mp
  have he' : EnvOk (reassign G η) (codeFrame c.arity c.row c.captures c.spine) (envOf L .nul) n W := by
    rw [hspine]; exact he
  have hpre' : PreAt c.row.effect c.spine L heap := by rw [hspine]; exact hpre
  have hentry : EntryHolds (reassign G η) (codeFrame c.arity c.row c.captures c.spine) sep
      (GraphCode.codeEntryIndices c) (envOf L .nul) n W heap :=
    ⟨he', hsep, GraphCode.codeEntryIndices_holds hpre', hw, hh⟩
  have hrun := codeRun_of_clauses hsafeG hboundG η n W heap L .nul hentry hgo hvalues rfl
  rw [code_goal, hspine] at hrun
  obtain ⟨pre, vs, hpl, rfl⟩ := hframe
  have hpre0 : pre = [] := List.eq_nil_of_length_eq_zero (by simpa [frameOffset] using hpl)
  subst hpre0
  refine exportsEstablished_sound hx hw hh ?_
  by_cases hne : c.row.effect.schema.normal.facts = []
  · exact HeapObservations.SafePostExc.weaken (fun _ _ hq => ⟨hq.1, hq.2, by simp [hne]⟩) (fun _ h => h) hrun
  · have hens := hensG hne η n W heap _ .nul hentry hgo
    rw [code_goal, hspine] at hens
    refine HeapObservations.SafePostExc.weaken (fun h' v hq => ?_) (fun _ h => h) (safePostExc_and hrun hens)
    obtain ⟨⟨h1, h2⟩, hq⟩ := hq
    exact ⟨h1, h2, fun F hF =>
      (CallEffects.Effect.ensures_frame (CallEffects.Effect.belowRow_ensures hrow hF).1
        (CallEffects.Effect.belowRow_ensures hrow hF).2 v r args vs .nul heap h').mpr (by simpa using hq F hF)⟩

end

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **A request's footprint clause discharges a code's run bound** (proved):
where the request's bound equals the code's exit bounds and freshness, any
`codeRunBound c = some (⟨Φ, Ψ⟩, fresh)` activates `FootprintClause r`, at
any component (`SafePostExcW.goto_comp_iff`). Shared by `rowSpec_of_requestSafe`
and `receiverDropSound`. -/
private theorem requestBound_of_footprint {r : SourceRequest σ ι} {c : CodeEntry ι} {comp : ComponentTag}
    (hfp : FootprintClause r)
    (hbound : RunBound.ofRequest r.footprint r.onThrow r.fresh =
      (exitBounds c.row.effect, c.row.effect.schema.normal.freshResult))
    (hgoto : ∀ L d, gotoOf r.program r.start L d r.comp = .goto c.exprs c.conts c.start L d r.comp) :
    ∀ Φ Ψ fresh, codeRunBound c = some (⟨Φ, Ψ⟩, fresh) → ∀ η n W h L d,
      EntryHolds (reassign (RequestJson.graph r.toRequest) η) r.inputs r.entrySeparation r.entryIndices
        (envOf L d) n W h → RefsOk W (.goto c.exprs c.conts c.start L d comp) →
      (∀ v ∈ L, isVal v = true) → isVal d = true →
      HeapObservations.SafePostExc (excOf (reassign (RequestJson.graph r.toRequest) η))
        (GoalHolds (reassign (RequestJson.graph r.toRequest) η) r.goal (r.goal.argument (envOf L d)))
        (fun h' v => Φ.Holds h h' ∧ (fresh = true → Footprints.FreshAt h.length v))
        (fun h' => Ψ ≠ .top → Ψ.Holds h h') n W h (.goto c.exprs c.conts c.start L d comp) := by
  intro Φ Ψ fresh hb η n W h L d he hgo hvals hd
  obtain ⟨hbd, rfl, hne⟩ := codeRunBound_some hb
  simp only [RunBound.ofRequest, Prod.mk.injEq] at hbound
  obtain ⟨hex, hfr⟩ := hbound
  rw [← hex] at hbd hne
  have hΦ : Φ = r.footprint := congrArg CallEffects.Exits.normal hbd
  have hΨ : Ψ = if r.onThrow then r.footprint else .top := congrArg CallEffects.Exits.exceptional hbd
  subst hΦ hΨ
  have hpre : r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true := by
    by_cases h1 : r.footprint = .top
    · by_cases h2 : r.onThrow = true
      · exact .inr (.inl h2)
      · right; right
        rw [hfr]
        cases hf : c.row.effect.schema.normal.freshResult
        · exact absurd ⟨h1, by simp [h2], hf⟩ hne
        · rfl
    · exact .inl h1
  have := hfp hpre η n W h L d he (GraphCode.goto_refs hgo).2 hvals hd
  rw [hgoto, hfr] at this
  replace this := (HeapObservations.SafePostExcW.goto_comp_iff r.comp comp).mp this
  refine HeapObservations.SafePostExc.weaken (fun _ _ hq => hq) (fun _ hq ht => ?_) this
  cases hot : r.onThrow
  · simp [hot] at ht
  · simp only [hot, ite_true] at ht ⊢
    exact hq hot

/-- **A safe unit request is module code at its signature** (proved): where
a unit request is a code's (`UnitIsCode`) collecting no rest and the code
meets the row conditions (`rowConditions`), the request's safety
(`RequestSafe`: its safety, footprint and postcondition clauses) makes the
code meet its signature as a module row at the request's entry separation,
at every assignment. -/
theorem rowSpec_of_requestSafe {r : SourceRequest σ ι} {c : CodeEntry ι}
    (hsafe : RequestSafe r) (hu : UnitIsCode r c) (hcond : rowConditions c = true) (hspine : c.spine = none) :
    ∀ η, RowSpec (reassign (RequestJson.graph r.toRequest) η) c.arity c.exprs c.conts c.start c.captures c.row
      r.entrySeparation := by
  have hadm : ∀ η, r.Admits η := fun η => by simp [SourceRequest.Admits, hu.unqualified]
  have hprog : r.program = GraphCode.program c.exprs c.conts := by
    rw [hu.exprs, hu.conts, program_nodes]
  -- The unit's run, at its own component, is the code's at any (`SameRun`).
  have hgoto : ∀ L d, gotoOf r.program r.start L d r.comp = .goto c.exprs c.conts c.start L d r.comp := by
    intro L d; simp only [gotoOf, hu.exprs, hu.conts, hu.start]
  apply rowSpec_of_clauses hcond hspine
  · intro η n W h ρ he hP hρ
    have := hsafe.1 η (hadm η) n W h ρ (by rw [hu.inputs, hu.indices]; exact he) hρ
    rw [hprog, hu.goal, hu.start] at this
    exact this
  · intro Φ Ψ fresh hb η n W h L d he hgo hvals hd
    rw [← hu.goal]
    exact requestBound_of_footprint hsafe.2.1 hu.bound hgoto Φ Ψ fresh hb η n W h L d
      (by rw [hu.inputs, hu.indices]; exact he) hgo hvals hd
  · intro hne η n W h L d he hgo
    have := hsafe.2.2.1 (by rw [hu.ensures]; exact hne) η n W h L d (by rw [hu.inputs, hu.indices]; exact he)
      (GraphCode.goto_refs hgo).2
    rw [hgoto, hu.goal, hu.ensures] at this
    exact (HeapObservations.SafePostW.goto_comp_iff r.comp none).mp this

end

/-! ## A function declared without `this` -/

section
variable {ι : Type}

/-- **The code of a function declared without `this`**: every call of a
closure enters its code with the receiver in slot `0` (`graphEntry`; a
plain call passes `undefined`), and such a function's request has no
receiver slot (its inputs are its parameters and captures). Its module code
is the request's node lists behind one prologue node, appended, at which
the code starts: it evaluates `undefined` and continues at the request's
start with the frame past the receiver (`envMap` keeps slots `1` to
`arity + captures + 1`: the parameters, the captures and the closure
itself). -/
def dropReceiver (c : CodeEntry ι) : CodeEntry ι :=
  { c with
    exprs := c.exprs ++ [.undef]
    conts := c.conts ++
      [(.effect ⟨c.start, some ((List.range (c.arity + c.captures.length + 1)).map (· + 1))⟩, none)]
    start := c.exprs.length }

/-- The goal of a request with no receiver slot: the code's, its promise's
parameter at its place in that request's frame. -/
def receiverlessGoal (c : CodeEntry ι) : ControlFlow.Goal ι :=
  match c.row.effect.promise with
  | some (.guards p) => .guards c.row.result p
  | some (.asserts p) => .asserts c.row.result p
  | none => .plain c.row.result

end

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **A unit request of a function declared without `this` is a code's
behind the receiver's prologue**: unqualified, collecting no rest, its
inputs the code's frame past the receiver (the parameters, then the
captures), its program, start and goal the code's at that frame, its entry
separation scoped to its inputs (every fact's levels below its depth, its
depth within its inputs, as the layout check checks), its entry facts
implied by the code's at every frame with a receiver in front, the
signature's postcondition, which names the receiver in neither state, read
past the receiver as its own (`IndexFact.pastReceiver`: each current and
each entry position one lower, the result kept), and its run's bound the
code's (`UnitIsCode.bound`). -/
structure UnitIsReceiverless (r : SourceRequest σ ι) (c : CodeEntry ι) : Prop where
  unqualified : r.qualification = none
  spine : c.spine = none
  inputs : r.inputs = c.row.arguments.take c.arity ++ c.captures
  exprs : c.exprs = r.program.map (·.expression)
  conts : c.conts = r.program.map fun n => (n.continuation, n.handler)
  start : r.start = c.start
  goal : r.goal = receiverlessGoal c
  separation : ∀ a ∈ r.entrySeparation.facts,
    r.entrySeparation.depth ≤ r.inputs.length ∧ a.slot < r.entrySeparation.depth ∧
    ∀ p ∈ a.partners, p.1 < r.entrySeparation.depth
  indices : ∀ (L : List Tm) (recv d : Tm) h,
    HeapKnowledge.IndexHolds ⟨envOf (recv :: L) d, h⟩ (GraphCode.codeEntryIndices c) (envOf (recv :: L) d) h →
    HeapKnowledge.IndexHolds ⟨envOf L d, h⟩ r.entryIndices (envOf L d) h
  «ensures» : c.row.effect.schema.normal.facts.mapM HeapKnowledge.IndexFact.pastReceiver = some r.ensures
  bound : RunBound.ofRequest r.footprint r.onThrow r.fresh = (exitBounds c.row.effect, c.row.effect.schema.normal.freshResult)

end

/-- The row fact `result = old(receiver)`, as `result - old(receiver) ≤ 0`:
a postcondition of a function's receiver at its entry. -/
def resultIsOldReceiver : HeapKnowledge.IndexFact :=
  .linear (.le [(HeapKnowledge.Term.value 0, 1), ((HeapKnowledge.Term.old .value 0 []), -1)] 0)

/-- Read past the receiver it names nothing: it names the receiver's entry
value (proved by evaluation). -/
theorem resultIsOldReceiver_pastReceiver : resultIsOldReceiver.pastReceiver = none := rfl

/-- Its neighbour `result = old(first parameter)` (entry position `1`) reads
past the receiver as `result = old(slot 0)`, the request's first input. -/
theorem resultIsOldFirst_pastReceiver :
    (HeapKnowledge.IndexFact.linear (.le [(HeapKnowledge.Term.value 0, 1), ((HeapKnowledge.Term.old .value 1 []), -1)] 0)).pastReceiver =
      some (.linear (.le [(HeapKnowledge.Term.value 0, 1), ((HeapKnowledge.Term.old .value 0 []), -1)] 0)) := rfl

theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y ∈ l', f x = some y
  | [], _, _, x, hx => by cases hx
  | a :: t, l', h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, t', ht, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨y, hy, hfy⟩ := mapM_some_mem ht x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- **A row stating `result = old(receiver)` has no receiverless request**
(proved): the mistranslation that read it as `result = old(first parameter)`
is not a request of the row. -/
theorem not_receiverless_of_oldReceiver {σ ι : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι}
    {c : CodeEntry ι} (hm : resultIsOldReceiver ∈ c.row.effect.schema.normal.facts) : ¬ UnitIsReceiverless r c := by
  intro hu
  obtain ⟨y, -, hy⟩ := mapM_some_mem hu.ensures _ hm
  rw [resultIsOldReceiver_pastReceiver] at hy
  cases hy

/-- The slot map from a frame with a receiver in front to the frame past
it: slot `s + 1` to `s`, the receiver's slot to none. -/
def pastReceiver (s : Nat) : Option Nat := if s = 0 then none else some (s - 1)

/-- **Entry facts of a function declared without `this`** (proved): where
each entry fact of the request is a fact of the code's precondition with
each slot one less (`mapIndices pastReceiver`), the code's facts at every
frame with a receiver in front (for any default value) imply the request's
at the frame past it: `UnitIsReceiverless.indices`. -/
theorem receiverless_indices {ι : Type} {c : CodeEntry ι} {facts : List HeapKnowledge.IndexAtom}
    (hsub : ∀ a ∈ facts, a ∈ HeapKnowledge.mapIndices pastReceiver (GraphCode.codeEntryIndices c)) :
    ∀ (L : List Tm) (recv d : Tm) h,
      HeapKnowledge.IndexHolds ε (GraphCode.codeEntryIndices c) (envOf (recv :: L) d) h →
      HeapKnowledge.IndexHolds ε facts (envOf L d) h := by
  intro L recv d h he a ha
  have hf : ∀ s t, pastReceiver s = some t → envOf L d t = envOf (recv :: L) d s := by
    intro s t hs
    unfold pastReceiver at hs
    split at hs
    · cases hs
    · rename_i hne
      cases hs
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
      simp [envOf]
  exact HeapKnowledge.mapIndices_holds hf he a (hsub a ha)

/-- The separation of a request with no receiver slot, read in the frame
with the receiver in front: the same facts at one more depth, since a level
names the same slot with a slot pushed below the parameters. -/
def receiverSeparation (S : HeapSeparation.Separation) : HeapSeparation.Separation :=
  { S with depth := S.depth + 1 }

/-- A term running graph code `E, K`, and the same run in `E ++ E₂, K ++ K₂`. -/
private inductive PrefixTerm (E E₂ : List Tm)
    (K K₂ : List (ControlFlow.Continuation × Option ControlFlow.Target)) (comp : ComponentTag) : Tm → Tm → Prop where
  | goto {l : Nat} {L : List Tm} {d : Tm} :
      PrefixTerm E E₂ K K₂ comp (.goto E K l L d comp) (.goto (E ++ E₂) (K ++ K₂) l L d comp)
  | frame {t : Tm} {L : List Tm} {d : Tm} {k : ControlFlow.Continuation} {x : Option ControlFlow.Target} :
      PrefixTerm E E₂ K K₂ comp (.frame E K t L d k x comp) (.frame (E ++ E₂) (K ++ K₂) t L d k x comp)
  | same (t : Tm) : PrefixTerm E E₂ K K₂ comp t t

private theorem PrefixTerm.refsOk {E E₂ K K₂ comp n} {W : WorldT n} {t t' : Tm}
    (hp : PrefixTerm E E₂ K K₂ comp t t') (hE₂ : ∀ e ∈ E₂, RefsOk W e) (ht : RefsOk W t) : RefsOk W t' := by
  cases hp with
  | same => exact ht
  | goto =>
    intro r hr
    simp only [refs, refsArgs_eq, List.flatMap_append, List.mem_append, List.mem_flatMap] at hr
    rcases hr with ((⟨e, he, h⟩ | ⟨e, he, h⟩) | ⟨a, ha, h⟩) | h
    · exact ht r (by simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inl (.inl ⟨e, he, h⟩))
    · exact hE₂ e he r h
    · exact ht r (by simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inl (.inr ⟨a, ha, h⟩))
    · exact ht r (by simp only [refs, refsArgs_eq, List.mem_append]; exact .inr h)
  | frame =>
    intro r hr
    simp only [refs, refsArgs_eq, List.flatMap_append, List.mem_append, List.mem_flatMap] at hr
    rcases hr with (((⟨e, he, h⟩ | ⟨e, he, h⟩) | h) | ⟨a, ha, h⟩) | h
    · exact ht r (by simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inl (.inl (.inl ⟨e, he, h⟩)))
    · exact hE₂ e he r h
    · exact ht r (by simp only [refs, refsArgs_eq, List.mem_append]; exact .inl (.inl (.inr h)))
    · exact ht r (by simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inl (.inr ⟨a, ha, h⟩))
    · exact ht r (by simp only [refs, refsArgs_eq, List.mem_append]; exact .inr h)

private theorem PrefixTerm.eq_of_val {E E₂ K K₂ comp} {t t' : Tm} (hp : PrefixTerm E E₂ K K₂ comp t t')
    (hv : isVal t = true) : t = t' := by
  cases hp with
  | same => rfl
  | goto => simp [isVal] at hv
  | frame => simp [isVal] at hv

private theorem PrefixTerm.raises {E E₂ K K₂ comp} {t t' v : Tm} (hp : PrefixTerm E E₂ K K₂ comp t t')
    (hr : Raises t v) : Raises t' v := by
  cases hp with
  | same => exact hr
  | goto => cases hr
  | frame => cases hr

private theorem PrefixTerm.step {E E₂ K K₂ comp h h'} {t t' t₁ : Tm} (hp : PrefixTerm E E₂ K K₂ comp t t')
    (s : Step h t h' t₁) : ∃ t₁', Step h t' h' t₁' ∧ PrefixTerm E E₂ K K₂ comp t₁ t₁' := by
  cases hp with
  | same => exact ⟨t₁, s, .same _⟩
  | @goto l _ _ =>
    cases s with
    | gotoEnter he hk =>
      exact ⟨_, .gotoEnter
        (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp he).1]; exact he)
        (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1]; exact hk), .frame⟩
  | frame =>
    cases s with
    | frameC st => exact ⟨_, .frameC st, .frame⟩
    | frameRet hv => exact ⟨_, .frameRet hv, .same _⟩
    | frameBind hv => exact ⟨_, .frameBind hv, .goto⟩
    | frameEffect hv => exact ⟨_, .frameEffect hv, .goto⟩
    | frameYes => exact ⟨_, .frameYes, .goto⟩
    | frameNo => exact ⟨_, .frameNo, .goto⟩
    | frameYesBind => exact ⟨_, .frameYesBind, .goto⟩
    | frameNoBind => exact ⟨_, .frameNoBind, .goto⟩
    | frameTag hv => exact ⟨_, .frameTag hv, .goto⟩
    | frameHandle hr => exact ⟨_, .frameHandle hr, .goto⟩
    | frameRaise hr => exact ⟨_, .frameRaise hr, .same _⟩

/-- **Appending unreachable nodes preserves safety and postconditions**
(proved): any safe run of graph code `E, K` simulates step for step in
`E ++ E₂, K ++ K₂`, since every node it enters has a label in `E, K`. -/
private theorem safePostExc_prefix {Ξ T : Fam} {Q : HeapObservations.Post} {R : Heap → Prop}
    {E E₂ : List Tm} {K K₂ : List (ControlFlow.Continuation × Option ControlFlow.Target)} {comp : ComponentTag} :
    ∀ {n W h t t'}, PrefixTerm E E₂ K K₂ comp t t' → (∀ e ∈ E₂, RefsOk W e) →
      HeapObservations.SafePostExc Ξ T Q R n W h t →
      HeapObservations.SafePostExc Ξ T Q R n W h t' := by
  intro n
  induction n with
  | zero => intro W h t t' hp hE₂ hs; exact hp.refsOk hE₂ hs
  | succ n ih =>
    intro W h t t' hp hE₂ hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hp.refsOk hE₂ hrf, ?_⟩
    rcases hs with (⟨hv, hT, hQ⟩ | ⟨⟨v, hraise, hsc, hΞ⟩, hR⟩) | ⟨U, h', t₁, hx, hu, st, hh, hs₁⟩
    · cases hp.eq_of_val hv
      exact .inl (.inl ⟨hv, hT, hQ⟩)
    · exact .inl (.inr ⟨⟨v, hp.raises hraise, hsc, hΞ⟩, hR⟩)
    · obtain ⟨t₁', st', hp'⟩ := hp.step st
      exact .inr ⟨U, h', t₁', hx, hu, st', hh,
        ih hp' (fun e he => RefsOk_mono hx (RefsOk_trunc _ (hE₂ e he))) hs₁⟩

/-- Appending an unreachable prologue to a graph keeps the graph safe
when entry is at an original label. -/
theorem safePostExc_goto_append {Ξ T : Fam} {Q : HeapObservations.Post} {R : Heap → Prop}
    {E E₂ : List Tm} {K K₂ : List (ControlFlow.Continuation × Option ControlFlow.Target)}
    {n W h label L d comp} (added : ∀ e ∈ E₂, RefsOk W e)
    (safe : HeapObservations.SafePostExc Ξ T Q R n W h (.goto E K label L d comp)) :
    HeapObservations.SafePostExc Ξ T Q R n W h (.goto (E ++ E₂) (K ++ K₂) label L d comp) :=
  safePostExc_prefix .goto added safe

/-- The prologue's mapped frame agrees with `recv :: tail` shifted by one on
every slot below `arity + captures.length + 1`. -/
private theorem dropReceiver_envOf_lt (k : Nat) (recv : Tm) (tail : List Tm) {i : Nat} (hi : i < k) :
    envOf (((List.range k).map (· + 1)).map ((recv :: tail).getD · .nul)) recv i =
      envOf (recv :: tail) .nul (i + 1) := by
  simp only [envOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

/-- **The receiver's prologue keeps a safe request safe** (proved): where a
request with no receiver slot is a code's behind the prologue
(`UnitIsReceiverless`) and the code meets the row conditions, the request's
safety makes the code with the prologue (`dropReceiver`) meet its signature
as a module row at every assignment, at the request's entry separation read
with the receiver in front (`receiverSeparation`). The prologue's two
transitions (`gotoEnter` on `.undef`, then `frameEffect` with the slot map)
leave the heap unchanged and land at the request's start with the shifted
frame and the receiver as default slot value, where every later step is
simulated by the request's program (`safePostExc_prefix`) and the row's
postcondition transfers via `holdsAt_pastReceiver`. -/
theorem receiverDropSound {σ ι : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι} {c : CodeEntry ι}
    (hsafe : RequestSafe r) (hu : UnitIsReceiverless r c) (hcond : rowConditions c = true) :
    ∀ η, RowSpec (reassign (RequestJson.graph r.toRequest) η) (dropReceiver c).arity (dropReceiver c).exprs
      (dropReceiver c).conts (dropReceiver c).start (dropReceiver c).captures (dropReceiver c).row
      (receiverSeparation r.entrySeparation) := by
  have hadm : ∀ η, r.Admits η := fun η => by simp [SourceRequest.Admits, hu.unqualified]
  have hprog : r.program = GraphCode.program c.exprs c.conts := by
    rw [hu.exprs, hu.conts, program_nodes]
  have hclen : c.conts.length = c.exprs.length := by
    rw [hu.exprs, hu.conts]; simp
  have hgoto : ∀ L d, gotoOf r.program r.start L d r.comp = .goto c.exprs c.conts c.start L d r.comp := by
    intro L d; simp only [gotoOf, hu.exprs, hu.conts, hu.start]
  simp only [rowConditions, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hcond
  obtain ⟨⟨⟨harity, hrow⟩, _hreq⟩, hx⟩ := hcond
  have hilen : r.inputs.length = c.arity + c.captures.length := by
    rw [hu.inputs, List.length_append, List.length_take, Nat.min_eq_left harity]
  intro η
  refine ⟨harity, hrow, ?_⟩
  intro n W heap L comp he hw hh hgo hvalues hpre hsep recv args hframe
  obtain ⟨pre, vs, hpl, rfl⟩ := hframe
  have hpre0 : pre = [] := List.eq_nil_of_length_eq_zero (by simpa [frameOffset] using hpl)
  subst hpre0
  simp only [List.nil_append] at he hgo hvalues hpre hsep ⊢
  let tail : List Tm := CallArguments.parameters c.arity args ++ vs
  let kLen : Nat := c.arity + c.captures.length + 1
  let slots : List Nat := (List.range kLen).map (· + 1)
  let kPro : ControlFlow.Continuation × Option ControlFlow.Target := (.effect ⟨c.start, some slots⟩, none)
  let E' : List Tm := c.exprs ++ [.undef]
  let K' : List (ControlFlow.Continuation × Option ControlFlow.Target) := c.conts ++ [kPro]
  let G : NormalGraph ι := reassign (RequestJson.graph r.toRequest) η
  let T : Fam := c.row.effect.result (meaning G c.row.result)
    (framePromised c.row.effect (frameOffset (none : Option (Ty ι))) (recv :: tail))
  have hE' : E' = (dropReceiver c).exprs := rfl
  have hK' : K' = (dropReceiver c).conts := rfl
  refine exportsEstablished_sound hx hw hh ?_
  -- Step through the prologue's two transitions (`gotoEnter`, `frameEffect`).
  have hstep1 : Step heap (.goto E' K' c.exprs.length (recv :: tail) .nul comp)
      heap (.frame E' K' .undef (recv :: tail) .nul (.effect ⟨c.start, some slots⟩) none comp) := by
    have he1 : E'[c.exprs.length]? = some .undef := by
      simp [E']
    have hk1 : K'[c.exprs.length]? = some kPro := by
      simp [K', ← hclen]
    simpa [instantiate] using Step.gotoEnter (h := heap) (L := recv :: tail) (d := .nul) (comp := comp) he1 hk1
  have hframeRefs : ∀ {m : Nat} {U : WorldT m}, RefsOk U (.goto E' K' c.exprs.length (recv :: tail) .nul comp) →
      RefsOk U (.frame E' K' .undef (recv :: tail) .nul (.effect ⟨c.start, some slots⟩) none comp) := by
    intro m U hr r' hr'
    simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap] at hr'
    rcases hr' with ((⟨e, he', h⟩ | h) | ⟨a, ha', h⟩) | h
    · exact hr r' (by simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inl (.inl ⟨e, he', h⟩))
    · simp at h
    · exact hr r' (by simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inl (.inr ⟨a, ha', h⟩))
    · exact hr r' (by simp only [refs, refsArgs_eq, List.mem_append]; exact .inr h)
  cases n with
  | zero => exact hgo
  | succ n1 =>
    refine ⟨hgo, .inr ⟨trunc n1 (Nat.le_succ n1) W, heap, _, WExt_refl _, WorldAdm_trunc _ hw,
      hstep1, HeapOk_trunc n1 W heap hh, ?_⟩⟩
    have hgo1 : RefsOk (trunc n1 (Nat.le_succ n1) W) (.goto E' K' c.exprs.length (recv :: tail) .nul comp) :=
      RefsOk_trunc (Nat.le_succ n1) hgo
    have hfr1 := hframeRefs hgo1
    cases n1 with
    | zero => exact hfr1
    | succ k =>
      let L' : List Tm := slots.map ((recv :: tail).getD · .nul)
      have hmap : envMap (some slots) (recv :: tail) .nul = (L', recv) := rfl
      have hstep2 : Step heap (.frame E' K' .undef (recv :: tail) .nul (.effect ⟨c.start, some slots⟩) none comp)
          heap (.goto E' K' c.start L' recv comp) := by
        simpa [hmap] using Step.frameEffect (h := heap) (E := E') (K := K') (v := .undef)
          (L := recv :: tail) (d := .nul) (l := ⟨c.start, some slots⟩) (x := none) (comp := comp) rfl
      let W₁ : WorldT (k + 1) := trunc (k + 1) (Nat.le_succ (k + 1)) W
      let W₂ : WorldT k := trunc k (Nat.le_succ k) W₁
      have hW₂ : W₂ = trunc k (by omega) W := trunc_trunc (Nat.le_succ k) (Nat.le_succ (k + 1)) W
      have hw₂ : WorldAdm W₂ := WorldAdm_trunc _ (WorldAdm_trunc _ hw)
      have hh₂ : HeapOk k W₂ heap := HeapOk_trunc k W₁ heap (HeapOk_trunc (k + 1) W heap hh)
      refine ⟨hfr1, .inr ⟨W₂, heap, .goto E' K' c.start L' recv comp, WExt_refl _, hw₂, hstep2, hh₂, ?_⟩⟩
      -- Establish the entry premises of the receiverless request `r` at `(k, W₂, heap, envOf L' recv)`.
      have hgo₂ : RefsOk W₂ (.goto E' K' c.exprs.length (recv :: tail) .nul comp) :=
        RefsOk_trunc (Nat.le_succ k) hgo1
      have hrefsE' : ∀ e ∈ E', RefsOk W₂ e := (GraphCode.goto_refs hgo₂).1
      have hrefsE : ∀ e ∈ c.exprs, RefsOk W₂ e := fun e he => hrefsE' e (List.mem_append_left _ he)
      have hrefsE₂ : ∀ e ∈ ([.undef] : List Tm), RefsOk W₂ e := fun e he => hrefsE' e (List.mem_append_right _ he)
      have hrefsL : ∀ a ∈ recv :: tail, RefsOk W₂ a := (GraphCode.envOf_refs (GraphCode.goto_refs hgo₂).2).1
      have hrefsNul : RefsOk W₂ .nul := (GraphCode.envOf_refs (GraphCode.goto_refs hgo₂).2).2
      have hmemL' : ∀ x, (x ∈ L' ∨ x = recv) → x ∈ recv :: tail ∨ x = .nul := fun x hx =>
        envMap_mem (m := some slots) (L := recv :: tail) (d := .nul) hx
      have hvals' : ∀ v ∈ L', isVal v = true := fun v hv => by
        rcases hmemL' v (.inl hv) with hm | rfl
        · exact hvalues v hm
        · rfl
      have hvalRecv : isVal recv = true := hvalues recv List.mem_cons_self
      have hrefsL' : ∀ a ∈ L', RefsOk W₂ a := fun a ha => by
        rcases hmemL' a (.inl ha) with hm | rfl
        · exact hrefsL a hm
        · exact hrefsNul
      have hrefsRecv : RefsOk W₂ recv := hrefsL recv List.mem_cons_self
      have hroots' : RootsOk W₂ (envOf L' recv) := GraphCode.envOf_refs_of hrefsL' hrefsRecv
      have hgoR : RefsOk W₂ (.goto c.exprs c.conts c.start L' recv comp) := by
        intro r' hr'
        simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap] at hr'
        rcases hr' with (⟨e, he', h⟩ | ⟨a, ha', h⟩) | h
        · exact hrefsE e he' r' h
        · exact hrefsL' a ha' r' h
        · exact hrefsRecv r' h
      have heW₂ : EnvOk G (codeFrame c.arity c.row c.captures none) (envOf (recv :: tail) .nul) k W₂ := by
        rw [hW₂]
        exact he.transfer k (by omega) (trunc k (by omega) W) (WExt_refl _)
      have he' : EnvOk G r.inputs (envOf L' recv) k W₂ := by
        refine ⟨fun i => ?_, fun i A hA => ?_⟩
        · have hget : envOf L' recv i ∈ L' ∨ envOf L' recv i = recv := getD_mem_or L' i recv
          rcases hmemL' _ hget with hm | heq
          · obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hm
            have hsc := he.1 idx
            have hsc' : Scoped 0 ((recv :: tail)[idx]?.getD .nul) := hsc
            rw [hidx] at hsc'
            exact hsc'
          · rw [heq]; simp [Scoped]
        · have hi : i < r.inputs.length := (List.getElem?_eq_some_iff.mp hA).1
          have hik : i < kLen := by omega
          rw [dropReceiver_envOf_lt kLen recv tail hik]
          have hcf : (codeFrame c.arity c.row c.captures none)[i + 1]? = some A := by
            simp only [codeFrame, bodyFrame, List.cons_append, List.getElem?_cons_succ]
            rw [← hu.inputs]; exact hA
          exact heW₂.2 (i + 1) A hcf
      have hsep' : HeapSeparation.Holds r.entrySeparation (envOf L' recv) := by
        intro a ha
        obtain ⟨hdle, has, hps⟩ := hu.separation a ha
        have hsa := hsep a ha
        refine ⟨has, fun p hp => ?_⟩
        have hpp := hps p hp
        refine ⟨hpp, fun g hg => ?_⟩
        have hap := (hsa.2 p hp).2 g hg
        have haIdx : r.entrySeparation.depth - 1 - a.slot < kLen := by omega
        have hpIdx : r.entrySeparation.depth - 1 - p.1 < kLen := by omega
        have heqA : envOf L' recv (r.entrySeparation.depth - 1 - a.slot) =
            envOf (recv :: tail) .nul ((receiverSeparation r.entrySeparation).depth - 1 - a.slot) := by
          rw [dropReceiver_envOf_lt kLen recv tail haIdx]
          congr 1; simp only [receiverSeparation]; omega
        have heqP : envOf L' recv (r.entrySeparation.depth - 1 - p.1) =
            envOf (recv :: tail) .nul ((receiverSeparation r.entrySeparation).depth - 1 - p.1) := by
          rw [dropReceiver_envOf_lt kLen recv tail hpIdx]
          congr 1; simp only [receiverSeparation]; omega
        exact hap.congr heqA heqP
      have hidx' : HeapKnowledge.IndexHolds ⟨envOf L' recv, heap⟩ r.entryIndices (envOf L' recv) heap := by
        refine hu.indices L' recv recv heap fun a ha _ => ?_
        unfold GraphCode.codeEntryIndices at ha
        simp only [hu.spine, ↓reduceIte] at ha
        obtain ⟨F, hF, rfl⟩ := List.mem_map.mp ha
        have hF1 : F.toNow.HoldsAt ⟨envOf (recv :: tail) .nul, heap⟩ (envOf (recv :: tail) .nul) heap :=
          (CallEffects.Effect.pre_toNow ⟨envOf (recv :: tail) .nul, heap⟩ _ heap).mp (hpre rfl F hF)
        have hF2 : F.toNow.HoldsAt ⟨envOf (recv :: tail) .nul, heap⟩ (envOf (recv :: L') recv) heap := by
          refine (HeapKnowledge.IndexFact.holdsAt_congr fun s hs => ?_).mp hF1
          have hsl : s ≤ c.arity := CallEffects.Effect.entryBelow_pre (CallEffects.Effect.belowRow_entry hrow) F hF s hs
          cases s with
          | zero => rfl
          | succ j => exact (dropReceiver_envOf_lt kLen recv tail (by omega)).symm
        exact (CallEffects.Effect.pre_toNow ⟨envOf (recv :: tail) .nul, heap⟩ _ heap).mpr hF2
      have hentry' : EntryHolds G r.inputs r.entrySeparation r.entryIndices (envOf L' recv) k W₂ heap :=
        ⟨he', hsep', hidx', hw₂, hh₂⟩
      have hgoal : GoalHolds G r.goal (r.goal.argument (envOf L' recv)) = T := by
        rw [hu.goal]
        simp only [receiverlessGoal, T]
        rcases hpr : c.row.effect.promise with _ | (p | p)
        · rw [CallEffects.Effect.result_none hpr]; rfl
        · have hp : p < c.arity := by
            have := CallEffects.Effect.entryBelow_promise (CallEffects.Effect.belowRow_entry hrow)
            simp only [CallEffects.Effect.promiseBelow, CallEffects.TypePromise.param, hpr] at this
            exact of_decide_eq_true this
          have harg : envOf L' recv p = envOf (recv :: tail) .nul (1 + p) := by
            rw [dropReceiver_envOf_lt kLen recv tail (by omega), Nat.add_comm]
          simp only [GoalHolds, ControlFlow.Goal.argument, ControlFlow.Goal.slot, CallEffects.Effect.result,
            framePromised, frameOffset, hpr, CallEffects.TypePromise.result, CallEffects.TypePromise.param, harg]
        · have hp : p < c.arity := by
            have := CallEffects.Effect.entryBelow_promise (CallEffects.Effect.belowRow_entry hrow)
            simp only [CallEffects.Effect.promiseBelow, CallEffects.TypePromise.param, hpr] at this
            exact of_decide_eq_true this
          have harg : envOf L' recv p = envOf (recv :: tail) .nul (1 + p) := by
            rw [dropReceiver_envOf_lt kLen recv tail (by omega), Nat.add_comm]
          simp only [GoalHolds, ControlFlow.Goal.argument, ControlFlow.Goal.slot, CallEffects.Effect.result,
            framePromised, frameOffset, hpr, CallEffects.TypePromise.result, CallEffects.TypePromise.param, harg]
      -- Run `r` from `(k, W₂, heap, L', recv)` via `codeRun_of_clauses` and `EnsuresClause`.
      have hrunR := codeRun_of_clauses (G := RequestJson.graph r.toRequest) (c := c)
        (inputs := r.inputs) (sep := r.entrySeparation) (indices := r.entryIndices) (goal := r.goal) (comp := comp)
        (fun η' n' W' h' ρ' he' _ hρ' => by
          have := hsafe.1 η' (hadm η') n' W' h' ρ' he' hρ'
          rw [hprog, hu.start] at this
          exact this)
        (requestBound_of_footprint hsafe.2.1 hu.bound hgoto)
        η k W₂ heap L' recv hentry' hgoR hvals' hvalRecv
      rw [hgoal] at hrunR
      have hfullR : HeapObservations.SafePostExc (excOf G) T
          (fun h' v => (exitBounds c.row.effect).normal.Holds heap h' ∧
            (c.row.effect.schema.normal.freshResult = true → Footprints.FreshAt heap.length v) ∧
            ∀ F ∈ c.row.effect.schema.normal.facts,
              F.HoldsAt ⟨CallEffects.callEnv recv args, heap⟩ (CallEffects.ensuresEnv v recv args) h')
          (fun h' => (exitBounds c.row.effect).exceptional.Holds heap h')
          k W₂ heap (.goto c.exprs c.conts c.start L' recv comp) := by
        by_cases hne : c.row.effect.schema.normal.facts = []
        · exact HeapObservations.SafePostExc.weaken (fun _ _ hq => ⟨hq.1, hq.2, by simp [hne]⟩)
            (fun _ h => h) hrunR
        · have hneR : r.ensures ≠ [] := by
            intro he0
            apply hne
            cases hfs : c.row.effect.schema.normal.facts with
            | nil => rfl
            | cons a t =>
              have huens := hu.ensures
              rw [hfs, he0] at huens
              simp [List.mapM_cons, Option.bind_eq_some_iff] at huens
          have hens := hsafe.2.2.1 hneR η k W₂ heap L' recv hentry' hroots'
          rw [hgoto, hgoal] at hens
          replace hens := (HeapObservations.SafePostW.goto_comp_iff r.comp comp).mp hens
          refine HeapObservations.SafePostExc.weaken (fun h' v hq => ?_) (fun _ h => h) (safePostExc_and hrunR hens)
          obtain ⟨⟨h1, h2⟩, hq⟩ := hq
          refine ⟨h1, h2, fun F hF => ?_⟩
          obtain ⟨F', hF'mem, hF'eq⟩ := mapM_some_mem hu.ensures F hF
          have h1' : F.HoldsAt ⟨envOf (recv :: L') recv, heap⟩ (push v (envOf (recv :: L') recv)) h' :=
            (HeapKnowledge.IndexFact.holdsAt_pastReceiver hF'eq L' recv recv v heap h').mp (hq F' hF'mem)
          have h2' : F.HoldsAt ⟨envOf (recv :: tail) .nul, heap⟩ (push v (envOf (recv :: L') recv)) h' := by
            refine (HeapKnowledge.IndexFact.holdsAt_congr_entry (ε := ⟨envOf (recv :: L') recv, heap⟩)
              (ε' := ⟨envOf (recv :: tail) .nul, heap⟩) rfl fun s hs => ?_).mp h1'
            have hsl := (CallEffects.Effect.belowRow_ensures hrow hF).2 s hs
            cases s with
            | zero => rfl
            | succ j => exact dropReceiver_envOf_lt kLen recv tail (by omega)
          have h3' : F.HoldsAt ⟨envOf (recv :: tail) .nul, heap⟩ (push v (envOf (recv :: tail) .nul)) h' := by
            refine (HeapKnowledge.IndexFact.holdsAt_congr fun s hs => ?_).mp h2'
            have hsl := (CallEffects.Effect.belowRow_ensures hrow hF).1 s hs
            rcases s with _ | _ | j
            · rfl
            · rfl
            · exact dropReceiver_envOf_lt kLen recv tail (by omega)
          exact (CallEffects.Effect.ensures_frame (CallEffects.Effect.belowRow_ensures hrow hF).1
            (CallEffects.Effect.belowRow_ensures hrow hF).2 v recv args vs .nul heap h').mpr h3'
      exact safePostExc_prefix .goto hrefsE₂ hfullR

/-! ## The module's environment meets every closed unit's interface -/

section
variable {ι U : Type}

/-- **A function's frames meet its separation** (`CapturesApart`): every
frame a call of its closure enters at any depth of the module's environment,
whatever the receiver, the actuals and what follows the captures, meets the
separation of its code. The separation names the frame's module cells alone
(`moduleCellSeparation`), so it is a fact of the captured values. -/
def CapturesApart (code : U → ModuleCode ι U) (u : U) : Prop :=
  ∀ (f : U → Tm) (i : Nat) (r : Tm) (args more : List Tm),
    HeapSeparation.Holds (code u).sep
      (envOf (r :: CallArguments.parameters (code u).arity args ++ ((code u).captured f i ++ more)) .nul)

/-- **What a unit of the module must meet to be realized**: its interface
`iface u` presents one clause of signatures `L` and variadic signatures `Sg`
which its code offers, kind included (`CodeOffers`, `KindOffers`); each of its
captures is a slot; each linked capture is read at its callee's interface
and its callee is in the set (`S`): the slot agreement; and each outside
capture's value at each depth meets its type at every budget up to that
depth in every world above the base world `W₀` (`Above`): the
contract of the import, host value, stand-in or module value it holds; and
its frames meet its separation (`CapturesApart`). -/
def Realizes (G : NormalGraph ι) (code : U → ModuleCode ι U) (iface : U → Ty ι) (S : U → Prop) {N : Nat}
    (W₀ : WorldT N) (u : U) : Prop :=
  ∃ (L : List (CallEffects.Arrow (Ty ι))) (Sg : List (CallEffects.RestArrow (Ty ι))),
    Represents G (iface u) (.arrs L Sg) ∧ KindOffers G (code u).kind L Sg ∧
    RowOffers G (code u).arity (code u).exprs (code u).conts (code u).start (code u).captures L Sg (code u).sep ∧
    (code u).captures.length = (code u).slots.length ∧
    (∀ (k : Nat) d, (code u).slots[k]? = some (Slot.linked d) → (code u).captures[k]? = some (iface d) ∧ S d) ∧
    (∀ (k : Nat) v A, (code u).slots[k]? = some (Slot.outside v) → (code u).captures[k]? = some A →
      ∀ i, ∀ j ≤ i, ∀ V : WorldT j, Above W₀ V → meaning G A j V (v i)) ∧
    CapturesApart code u

/-- The captures of a realized unit meet their types at `j` in a world
above the base, where every linked function's value, given by `f`, meets
its interface there. -/
theorem captures_envOk {G : NormalGraph ι} {code : U → ModuleCode ι U} {iface : U → Ty ι} {S : U → Prop}
    {N : Nat} {W₀ : WorldT N}
    {u : U} (hr : Realizes G code iface S W₀ u) (ho : OutsideValues code) {f : U → Tm}
    (hf : ∀ d, isVal (f d) = true ∧ Scoped 0 (f d)) {i j : Nat} (hji : j ≤ i) {V : WorldT j} (hV : Above W₀ V)
    (hm : ∀ d, S d → meaning G (iface d) j V (f d)) :
    EnvOk G (code u).captures (envOf ((code u).captured f i) .nul) j V := by
  obtain ⟨L, Sg, -, -, -, hlen, hagree, hout, -⟩ := hr
  apply EnvOk.envOf_nul (fun v hv => (captured_values ho hf u i v hv).2)
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
    exact hout k w A hs hA i j hji V hV

/-- **The module's environment meets every closed unit's interface**
(proved): over a set `S` of units each realized against `S` at the base
world `W₀`, the value of each unit unfolded `n` times meets its interface
at every budget up to `n` in every world above `W₀`. By induction on `n`: a
call at budget `m ≤ n + 1` runs the code below `m`, in a world above `W₀`
(`Above.below`), where the captured values, unfolded `n` times, meet their
interfaces. Recursion and cycles go through, the budget decreasing. -/
theorem approx_meets {G : NormalGraph ι} {code : U → ModuleCode ι U} {iface : U → Ty ι} {S : U → Prop}
    {N : Nat} {W₀ : WorldT N}
    (hreal : ∀ u, S u → Realizes G code iface S W₀ u) (ho : OutsideValues code) :
    ∀ n u, S u → ∀ m ≤ n, ∀ W : WorldT m, Above W₀ W → meaning G (iface u) m W (approx code n u) := by
  intro n
  induction n with
  | zero =>
    intro u hu m hm W _
    obtain ⟨L, Sg, hrep, hk, hoff, hlen, -, -, hsep⟩ := hreal u hu
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    exact closure_meets_below (code u).fields hrep hk hoff (by simp [ModuleCode.captured, hlen])
      (fun v hv => (captured_values ho (approxEnv_value ho 0) u 0 v hv).2)
      (fun v hv => (captured_values ho (approxEnv_value ho 0) u 0 v hv).1)
      (hsep _ 0) W (fun j hj => absurd hj (Nat.not_lt_zero j))
  | succ n ih =>
    intro u hu m hm W hW
    obtain ⟨L, Sg, hrep, hk, hoff, hlen, -, -, hsep⟩ := hreal u hu
    exact closure_meets_below (code u).fields hrep hk hoff (by simp [ModuleCode.captured, hlen])
      (fun v hv => (captured_values ho (approxEnv_value ho (n + 1)) u (n + 1) v hv).2)
      (fun v hv => (captured_values ho (approxEnv_value ho (n + 1)) u (n + 1) v hv).1)
      (hsep _ (n + 1)) W (fun j hj V hx => captures_envOk (hreal u hu) ho (approxEnv_value ho (n + 1)) (by omega)
        (hW.below _ hx) (fun d hd => ih d hd j (by omega) V (hW.below _ hx)))

/-- **Each closed unit's captures are met by the module's environment**
(proved): the values the depth-`n` environment captures for a unit of `S`
meet the unit's capture types at budget `n` in every world above the base
world. With the
receiver and the arguments meeting the unit's parameters, this is the entry
premise of the unit's `RequestSafe` (`envOk_of_linked` states the same for
a caller's input slots). -/
theorem approx_captures_envOk {G : NormalGraph ι} {code : U → ModuleCode ι U} {iface : U → Ty ι}
    {S : U → Prop} {N : Nat} {W₀ : WorldT N} (hreal : ∀ u, S u → Realizes G code iface S W₀ u)
    (ho : OutsideValues code) (n : Nat) {u : U} (hu : S u) (W : WorldT n) (hW : Above W₀ W) :
    EnvOk G (code u).captures (envOf ((code u).captured (approx code n) n) .nul) n W :=
  captures_envOk (hreal u hu) ho (fun d => approxEnv_value ho (n + 1) d) (Nat.le_refl n) hW
    (fun d hd => approx_meets hreal ho n d hd n (Nat.le_refl n) W hW)

/-- **The interfaces as `link` states them** (proved): the realization
premise of the linking induction (`closedUnits_linked`'s `hreal`) holds of
the module's environment, with `Meets u n` the unfolding `n` meeting the
interface at every budget up to `n`. -/
theorem approx_link {G : NormalGraph ι} {code : U → ModuleCode ι U} {iface : U → Ty ι} {S : U → Prop}
    {N : Nat} {W₀ : WorldT N} (hreal : ∀ u, S u → Realizes G code iface S W₀ u) (ho : OutsideValues code) :
    ∀ n u, S u → (fun u n => ∀ m ≤ n, MeetsAt G (iface u) (approx code n u) m W₀) u n :=
  fun n u hu m hm W hW => approx_meets hreal ho n u hu m hm W hW

end

end Verification.SourceClaimJson.PassUnit
