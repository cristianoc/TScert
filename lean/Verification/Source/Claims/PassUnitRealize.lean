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
docs/SINGLE-PASS-THEOREM.md, section 4. -/

namespace Verification.SourceClaimJson.PassUnit
variable {ε : Verification.HeapKnowledge.EntryState}
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

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

/-- What a slot holds at depth `i`, with each linked function's value given
by `f`. -/
def Slot.valueAt {U : Type} (f : U → Tm) (i : Nat) : Slot U → Tm
  | .linked u => f u
  | .outside v => v i

/-- The closure of a module function's code over the captured values `vs`. -/
def ModuleCode.closure {ι U : Type} (c : ModuleCode ι U) (vs : List Tm) : Tm :=
  .objAt c.fields (.graph c.arity c.exprs c.conts c.start vs c.kind false) c.oid

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

section
variable {ι : Type}

/-! ## A module row's specification -/

/-- **A module function's code at one of its signatures** (`RowSpec`): code
of `arity`, collecting no rest, whose effect is one module code realizes
(`Effect.belowRow`: below its arity, a postcondition over the result, the
receiver and its parameters admitted), safe from every frame meeting the
signature's, its precondition and the separation `sep`, at the signature's
result and post. `GraphCodeSpec` at no rest store, at `sep = {}` and with no
postcondition, is one (`rowSpec_of_graphCodeSpec`). -/
def RowSpec (G : NormalGraph ι) (arity : Nat) (E : List Tm)
    (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (Ty ι)) (row : CallEffects.Arrow (Ty ι)) (sep : HeapSeparation.Separation) : Prop :=
  arity ≤ row.arguments.length ∧ row.effect.belowRow arity = true ∧
  ∀ n W h L, EnvOk G (codeFrame arity row Cs none) (envOf L .nul) n W → WorldAdm W →
    HeapOk n W h → CallArguments.Values L → PreAt row.effect (none : Option (Ty ι)) L h →
    HeapSeparation.Holds sep (envOf L .nul) →
    ∀ r args, FrameValues arity (none : Option (Ty ι)) L r args →
      HeapObservations.SafePostExc (excOf G)
        (row.effect.result (meaning G row.result) (framePromised row.effect (frameOffset (none : Option (Ty ι))) L))
        (row.effect.post r args h) (row.effect.excPost r args h)
        n W h (.goto E K start L .nul)

/-- **Graph code at a signature is module code at it** (proved). -/
theorem rowSpec_of_graphCodeSpec {G : NormalGraph ι} {arity E K start Cs row}
    (hs : GraphCodeSpec G arity E K start Cs row) : RowSpec G arity E K start Cs row {} :=
  ⟨hs.1, CallEffects.Effect.belowRow_of_below hs.2.1,
    fun n W h L he hw hh hv hpre _ r args hf => hs.2.2 n W h L he hw hh hv hpre r args hf⟩

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
  simp only [CallEffects.Effect.belowRow, CallEffects.Effect.below, CallEffects.Effect.promiseBelow,
    Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨⟨⟨⟨trivial, h.1.1.1.1.1.2⟩, h.1.1.1.1.2⟩, h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩

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
  intro n W h L he hw hh hv hpre hsep r args hf
  have hrun := hs.2.2 n W h L he hw hh hv hpre hsep r args hf
  have hres : ∀ a, p.effect.result (meaning G p.result) a = π.result (meaning G p.result) a := by
    intro a; simp [CallEffects.Effect.result, hp]
  rw [hres] at hrun
  show HeapObservations.SafePostExc (excOf G) (meaning G R) (p.effect.post r args h) (p.effect.excPost r args h)
    n W h _
  exact HeapObservations.SafePostExc.consequence_below' (fun _ _ _ _ h => h)
    (fun j _ W' u hu => promiseAdmits_result hR _ j W' u hu) (fun _ _ h => h) (fun _ h => h) hrun

/-- **Invoking a module row's code from a frame at the call's own level**
(proved): as `graph_invoke_at`, the frame's separation given. -/
theorem row_invoke_at {G : NormalGraph ι} {arity E K start Cs row vs sep}
    (hs : RowSpec G arity E K start Cs row sep) {j : Nat} {U : WorldT j}
    (hvs : EnvOk G Cs (envOf vs .nul) j U) (hvalues : CallArguments.Values vs)
    (hu : WorldAdm U) {heap : Heap} (hh : HeapOk j U heap) {r : Tm} (hr : meaning G row.receiver j U r)
    {args : List Tm} (ha : ArgsShort (row.arguments.map (meaning G)) j U args)
    (hq : ∀ F ∈ row.effect.pre, F.HoldsAt ⟨CallEffects.callEnv r args, heap⟩ (CallEffects.callEnv r args) heap)
    (hsep : HeapSeparation.Holds sep (envOf (r :: CallArguments.parameters arity args ++ vs) .nul)) :
    HeapObservations.SafePostExc (excOf G) (row.effect.result (meaning G row.result) (row.effect.promised args))
      (row.effect.post r args heap) (row.effect.excPost r args heap) j U heap
      (.goto E K start (r :: CallArguments.parameters arity args ++ vs) .nul) := by
  have hx : WExt (trunc j (Nat.le_refl j) U) U := by rw [trunc_id]; exact WExt_refl U
  have hb := CallEffects.Effect.belowRow_below hs.2.1
  have hsafe := hs.2.2 j U heap _ (frame_envOk hs.1 hvs (Nat.le_refl j) hx hr ha) hu hh (by
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
budget** (proved): code of fixed arity offering the signatures of `F` as
module rows (`RowOffers`) at the separation `sep`, whose captured values meet
their types at every budget below `n`, in every world, and every frame of
whose calls meets `sep`, meets `F` at `n` in every world. Every call of the
closure runs its code below the budget at which it is made. The induction of
`offers_self` with the self entry replaced by captures given at every
smaller budget. -/
theorem closure_meets_below {G : NormalGraph ι} {arity E K start Cs vs} {kind : Invoke}
    {F : Ty ι} {L : List (CallEffects.Arrow (Ty ι))} {S : List (CallEffects.RestArrow (Ty ι))} (fs : List (PropKey × Nat)) {oid : Nat}
    {sep : HeapSeparation.Separation}
    (hr : Represents G F (.arrs L S)) (hk : KindOffers G kind L S)
    (ho : RowOffers G arity E K start Cs L S sep)
    (hlen : Cs.length ≤ vs.length) (hsc : ∀ v ∈ vs, Scoped 0 v) (hvalues : CallArguments.Values vs)
    (hsep : ∀ r args more, HeapSeparation.Holds sep (envOf (r :: CallArguments.parameters arity args ++ (vs ++ more)) .nul))
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
      row_invoke_at (ho p (List.mem_append_left _ hp)) henv
        (Values.withSelf hvalues rfl) hu hh hrr ha (fun F hF => hreq.2 F hF) (hsep r args _)⟩
  · intro q hq j hj U hx hu heap hh r hrv hrr args hvals ha hreq
    obtain ⟨s, hsm, rfl⟩ := List.mem_map.mp hq
    have hspec := ho _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, hsm, rfl⟩))
    have hle : arity ≤ s.arguments.1.length := hspec.1
    have hrow : s.fixed.effect.belowRow arity = true := hspec.2.1
    have hbelow := CallEffects.Effect.belowRow_below hrow
    have henv := (hcaps j hj U).withSelf hlen hself
    have hp : CallArguments.parameters arity (args.take s.arguments.1.length) =
        CallArguments.parameters arity args := by
      rw [← CallArguments.parameters_take arity (args.take _), List.take_take,
        Nat.min_eq_left hle, CallArguments.parameters_take]
    have hsafe := row_invoke_at hspec henv (Values.withSelf hvalues rfl) hu hh
      (args := args.take s.arguments.1.length) hrr
      (by simpa [CallEffects.RestArrow.mapWith, CallEffects.Contract.map, CallEffects.RestArrow.fixed] using ha.1)
      (fun F hF => (CallEffects.Effect.pre_take hbelow hle (F := F) hF r args heap).mpr
        (hreq.2 F (by simpa [CallEffects.RestArrow.mapWith, CallEffects.Contract.map, CallEffects.RestArrow.fixed] using hF)))
      (by rw [hp]; exact hsep r args _)
    have hpr : s.fixed.effect.promised (args.take s.arguments.1.length) = s.fixed.effect.promised args :=
      CallEffects.Effect.promised_take hbelow hle args
    rw [hp, hpr] at hsafe
    exact ⟨_, .graph hrv hvals (hbS s hsm j U r hrr), HeapObservations.SafePostExc.weaken
      (fun _ _ h => CallEffects.Effect.post_take_row hrow hle h)
      (fun _ h => CallEffects.Effect.excPost_args (CallEffects.Effect.below_regions hbelow) h) hsafe⟩

theorem reassign_env (G : NormalGraph ι) : reassign G G.env = G := by
  cases G; rfl

end

/-! ## A safe unit request is graph code at its signature -/

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

omit [Labels ι] [StoreView σ ι] in
/-- A module row's signature conditions, as the layout check asks them of
a member's code (`layoutOwn`): its arity within its arguments, its effect one
module code realizes (`Effect.belowRow`: a postcondition over its call's
values admitted), and no fresh object, precondition on the receiver's
elements, element promise, receiver growth or element write. -/
def rowConditions (c : CodeEntry ι) : Bool :=
  decide (c.arity ≤ c.row.arguments.length) && c.row.effect.belowRow c.arity &&
    !c.row.effect.freshObject && c.row.effect.requires.isNone && c.row.effect.elements.isNone &&
    !c.row.effect.receiverGrows && c.row.effect.elementWrite.isNone

/-- **A unit request is a code's**: unqualified, its inputs the code's frame
(receiver, parameters, then the captures), its program the code's node
lists, its start and goal the code's, the code's precondition as its entry
facts, the signature's postcondition as its own (a function declaring
`this` reads each call position at the input slot of the same number), and
the code's footprint, fresh flag and throw flag as its own. Its entry
separation is the separation of the code's frames (`rowSpec_of_requestSafe`). -/
structure UnitIsCode (r : SourceRequest σ ι) (c : CodeEntry ι) : Prop where
  unqualified : r.qualification = none
  inputs : r.inputs = codeFrame c.arity c.row c.captures c.store
  exprs : c.exprs = r.program.map (·.expression)
  conts : c.conts = r.program.map fun n => (n.continuation, n.handler)
  start : r.start = c.start
  goal : r.goal = c.goal
  indices : r.entryIndices = GraphCode.codeEntryIndices c
  ensures : r.ensures = c.row.effect.ensures
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

end

/-- Two postconditions of one run hold together, the throw's kept: its
execution is deterministic (proved). -/
theorem safePostExc_and {Ξ T : Fam} {Q Q' : HeapObservations.Post} {R : Heap → Prop} :
    ∀ {n W W' h t}, HeapObservations.SafePostExc Ξ T Q R n W h t → HeapObservations.SafePost Ξ T Q' n W' h t →
      HeapObservations.SafePostExc Ξ T (fun h' u => Q h' u ∧ Q' h' u) R n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W W' h t hq hr
    rcases hq with (⟨hv, ht, hq⟩ | ⟨hth, hR⟩) | ⟨U, h1, t1, hx, hu, st1, hh1, hq1⟩
    · rcases hr with (⟨_, _, hr⟩ | hth') | ⟨_, _, _, _, _, st2, _, _⟩
      · exact .inl (.inl ⟨hv, ht, hq, hr⟩)
      · exact absurd hth' (val_not_thrown hv)
      · exact absurd st2 (value_no_step hv)
    · exact .inl (.inr ⟨hth, hR⟩)
    · rcases hr with (⟨hv', _, _⟩ | hth') | ⟨U2, h2, t2, _, _, st2, _, hr2⟩
      · exact absurd st1 (value_no_step hv')
      · exact absurd st1 hth'.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st1 st2
        exact .inr ⟨U, h1, t1, hx, hu, st1, hh1, ih hq1 hr2⟩

section
variable {ι : Type}

/-- **A code safe from its frame, within its bound and meeting its
postcondition, is module code at its signature** (proved): a code meeting
the row conditions and collecting no rest, whose graph is safe at every
assignment from its frame and the separation `sep`, within its bound where
it has one, and, where its signature states a postcondition, returns with
the postcondition's facts true of the result and its entry frame, meets its
signature as a module row (`RowSpec`) at `sep`. The run is
`codeRun_of_clauses`'s; the postcondition's facts at the entry frame are
those at the call's values (`Effect.ensures_frame`). -/
theorem rowSpec_of_clauses {G : NormalGraph ι} {c : CodeEntry ι} {sep : HeapSeparation.Separation}
    (hcond : rowConditions c = true) (hstore : c.store = none)
    (hsafeG : ∀ η n W h ρ, EntryHolds (reassign G η) (codeFrame c.arity c.row c.captures c.store) sep
      (GraphCode.codeEntryIndices c) ρ n W h →
      SafeGraph (excOf (reassign G η)) (GraphCode.program c.exprs c.conts)
        (GoalHolds (reassign G η) c.goal (c.goal.argument ρ)) n W h (.at c.start ρ))
    (hboundG : ∀ Φ fresh onThrow, codeBound c = some (Φ, fresh, onThrow) → ∀ η n W h L d,
      EntryHolds (reassign G η) (codeFrame c.arity c.row c.captures c.store) sep (GraphCode.codeEntryIndices c)
        (envOf L d) n W h → (∀ v ∈ L, isVal v = true) → isVal d = true →
      HeapObservations.SafePostExc (excOf (reassign G η))
        (GoalHolds (reassign G η) c.goal (c.goal.argument (envOf L d)))
        (fun h' v => Φ.Holds h h' ∧ (fresh = true → Footprints.FreshAt h.length v))
        (fun h' => onThrow = true → Φ.Holds h h') n W h (.goto c.exprs c.conts c.start L d))
    (hensG : c.row.effect.ensures ≠ [] → ∀ η n W h L d,
      EntryHolds (reassign G η) (codeFrame c.arity c.row c.captures c.store) sep (GraphCode.codeEntryIndices c)
        (envOf L d) n W h →
      HeapObservations.SafePost (excOf (reassign G η))
        (GoalHolds (reassign G η) c.goal (c.goal.argument (envOf L d)))
        (fun h' v => GraphCode.EnsuresAt c.row.effect.ensures ⟨envOf L d, h⟩ h' (push v (envOf L d))) n W h
        (.goto c.exprs c.conts c.start L d)) :
    ∀ η, RowSpec (reassign G η) c.arity c.exprs c.conts c.start c.captures c.row sep := by
  intro η
  simp only [rowConditions, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hcond
  obtain ⟨⟨⟨⟨⟨⟨harity, hrow⟩, hfo⟩, _hreq⟩, hel⟩, hgr⟩, hew⟩ := hcond
  have hbelow0 := CallEffects.Effect.belowRow_below hrow
  refine ⟨harity, hrow, ?_⟩
  intro n W heap L he hw hh hvalues hpre hsep r args hframe
  have he' : EnvOk (reassign G η) (codeFrame c.arity c.row c.captures c.store) (envOf L .nul) n W := by
    rw [hstore]; exact he
  have hpre' : PreAt c.row.effect c.store L heap := by rw [hstore]; exact hpre
  have hrun := codeRun_of_clauses (sep := sep) hbelow0 hfo hel hgr hew hsafeG hboundG η n W heap L he' hw hh
    hvalues hpre' hsep r args
  rw [hstore] at hrun
  obtain ⟨pre, vs, hpl, rfl⟩ := hframe
  have hpre0 : pre = [] := List.eq_nil_of_length_eq_zero (by simpa [frameOffset] using hpl)
  subst hpre0
  by_cases hne : c.row.effect.ensures = []
  · have he0 : ({ c.row.effect with ensures := [] } : CallEffects.Effect) = c.row.effect := by rw [← hne]
    rw [he0] at hrun
    exact hrun
  · have hentry : EntryHolds (reassign G η) (codeFrame c.arity c.row c.captures c.store) sep
        (GraphCode.codeEntryIndices c) (envOf ([] ++ r :: CallArguments.parameters c.arity args ++ vs) .nul) n W heap :=
      ⟨he', hsep, GraphCode.codeEntryIndices_holds hpre', hw, hh⟩
    have hens := hensG hne η n W heap _ .nul hentry
    rw [code_goal, hstore] at hens
    refine HeapObservations.SafePostExc.weaken (fun h' v hq => ?_) (fun _ h => h) (safePostExc_and hrun hens)
    obtain ⟨⟨h1, h2, h3, h4, -, h6, h7⟩, hq⟩ := hq
    refine ⟨h1, h2, h3, h4, fun F hF => ?_, h6, h7⟩
    exact (CallEffects.Effect.ensures_frame hrow hF v r args vs .nul heap h').mpr (by simpa using hq F hF)

end

section
variable {σ ι : Type} [Labels ι] [StoreView σ ι]

/-- **A safe unit request is module code at its signature** (proved): where
a unit request is a code's (`UnitIsCode`) collecting no rest and the code
meets the row conditions (`rowConditions`), the request's safety
(`RequestSafe`: its safety, footprint and postcondition clauses) makes the
code meet its signature as a module row at the request's entry separation,
at every assignment. -/
theorem rowSpec_of_requestSafe {r : SourceRequest σ ι} {c : CodeEntry ι}
    (hsafe : RequestSafe r) (hu : UnitIsCode r c) (hcond : rowConditions c = true) (hstore : c.store = none) :
    ∀ η, RowSpec (reassign (RequestJson.graph r.toRequest) η) c.arity c.exprs c.conts c.start c.captures c.row
      r.entrySeparation := by
  have hadm : ∀ η, r.Admits η := fun η => by simp [SourceRequest.Admits, hu.unqualified]
  have hprog : r.program = GraphCode.program c.exprs c.conts := by
    rw [hu.exprs, hu.conts, program_nodes]
  have hgoto : ∀ L d, gotoOf r.program r.start L d = .goto c.exprs c.conts c.start L d := by
    intro L d; simp only [gotoOf, hu.exprs, hu.conts, hu.start]
  apply rowSpec_of_clauses hcond hstore
  · intro η n W h ρ he
    have := hsafe.1 η (hadm η) n W h ρ (by rw [hu.inputs, hu.indices]; exact he)
    rw [hprog, hu.goal, hu.start] at this
    exact this
  · intro Φ fresh onThrow hb η n W h L d he hvals hd
    obtain ⟨rfl, rfl, rfl, hne⟩ := codeBound_some hb
    have hpre : r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true := by
      rw [hu.footprint, hu.onThrow, hu.fresh]; exact hne
    have := hsafe.2.1 hpre η n W h L d (by rw [hu.inputs, hu.indices]; exact he) hvals hd
    rw [hgoto, hu.goal, hu.footprint, hu.fresh, hu.onThrow] at this
    exact this
  · intro hne η n W h L d he
    have := hsafe.2.2.1 (by rw [hu.ensures]; exact hne) η n W h L d (by rw [hu.inputs, hu.indices]; exact he)
    rw [hgoto, hu.goal, hu.ensures] at this
    exact this

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
facts implied by the code's at every frame with a receiver in front, the
signature's postcondition, which names the receiver in neither state, read
past the receiver as its own (`IndexFact.pastReceiver`: each current and
each entry position one lower, the result kept), and the code's footprint,
fresh flag and throw flag. -/
structure UnitIsReceiverless (r : SourceRequest σ ι) (c : CodeEntry ι) : Prop where
  unqualified : r.qualification = none
  store : c.store = none
  inputs : r.inputs = c.row.arguments.take c.arity ++ c.captures
  exprs : c.exprs = r.program.map (·.expression)
  conts : c.conts = r.program.map fun n => (n.continuation, n.handler)
  start : r.start = c.start
  goal : r.goal = receiverlessGoal c
  indices : ∀ (L : List Tm) (recv : Tm) h,
    HeapKnowledge.IndexHolds ⟨envOf (recv :: L) .nul, h⟩ (GraphCode.codeEntryIndices c) (envOf (recv :: L) .nul) h →
    HeapKnowledge.IndexHolds ⟨envOf L .nul, h⟩ r.entryIndices (envOf L .nul) h
  ensures : c.row.effect.ensures.mapM HeapKnowledge.IndexFact.pastReceiver = some r.ensures
  footprint : r.footprint = c.row.effect.footprint
  fresh : r.fresh = c.row.effect.fresh
  onThrow : r.onThrow = c.row.effect.onThrow

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
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y, f x = some y
  | [], _, _, x, hx => by cases hx
  | a :: t, l', h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, t', ht, -⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, hb⟩
    · exact mapM_some_mem ht x hx

/-- **A row stating `result = old(receiver)` has no receiverless request**
(proved): the mistranslation that read it as `result = old(first parameter)`
is not a request of the row. -/
theorem not_receiverless_of_oldReceiver {σ ι : Type} [Labels ι] [StoreView σ ι] {r : SourceRequest σ ι}
    {c : CodeEntry ι} (hm : resultIsOldReceiver ∈ c.row.effect.ensures) : ¬ UnitIsReceiverless r c := by
  intro hu
  obtain ⟨y, hy⟩ := mapM_some_mem hu.ensures _ hm
  rw [resultIsOldReceiver_pastReceiver] at hy
  cases hy

/-- The slot map from a frame with a receiver in front to the frame past
it: slot `s + 1` to `s`, the receiver's slot to none. -/
def pastReceiver (s : Nat) : Option Nat := if s = 0 then none else some (s - 1)

/-- **Entry facts of a function declared without `this`** (proved): where
each entry fact of the request is a fact of the code's precondition with
each slot one less (`mapIndices pastReceiver`), the code's facts at every
frame with a receiver in front imply the request's at the frame past it:
`UnitIsReceiverless.indices`. -/
theorem receiverless_indices {ι : Type} {c : CodeEntry ι} {facts : List HeapKnowledge.IndexAtom}
    (hsub : ∀ a ∈ facts, a ∈ HeapKnowledge.mapIndices pastReceiver (GraphCode.codeEntryIndices c)) :
    ∀ (L : List Tm) (recv : Tm) h,
      HeapKnowledge.IndexHolds ε (GraphCode.codeEntryIndices c) (envOf (recv :: L) .nul) h →
      HeapKnowledge.IndexHolds ε facts (envOf L .nul) h := by
  intro L recv h he a ha
  have hf : ∀ s t, pastReceiver s = some t → envOf L .nul t = envOf (recv :: L) .nul s := by
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

/-- **The receiver's prologue keeps a safe request safe** (named hypothesis
`ReceiverDropSound`, a lemma about the graph machine): where a request with
no receiver slot is a code's behind the prologue (`UnitIsReceiverless`) and
the code meets the row conditions, the request's safety makes the code with
the prologue (`dropReceiver`) meet its signature as a module row at every
assignment, at the request's entry separation read with the receiver in
front (`receiverSeparation`). The row's postcondition is the request's read
with the receiver in front in both states (`UnitIsReceiverless.ensures`):
by `holdsAt_pastReceiver` the request's post at its entry `⟨envOf L d, h⟩`
and return `push v (envOf L d)` holds exactly where the row's does at
`⟨envOf (recv :: L) d, h⟩` and `push v (envOf (recv :: L) d)`. The
argument: the prologue's two transitions (entering it, then its `effect`
continuation) lead from the frame `recv :: L ++ [self]` to the request's
start at `L ++ [self]` with the receiver as the default slot value, and
every later transition of the code is one of the request's program, its
labels below the appended node's; the step-indexed safety at budget `n`
then follows from the request's at `n - 2`, the world downcast along. -/
def ReceiverDropSound : Prop :=
  ∀ (σ ι : Type) [Labels ι] [StoreView σ ι] (r : SourceRequest σ ι) (c : CodeEntry ι),
    RequestSafe r → UnitIsReceiverless r c → rowConditions c = true →
    ∀ η, RowSpec (reassign (RequestJson.graph r.toRequest) η) (dropReceiver c).arity (dropReceiver c).exprs
      (dropReceiver c).conts (dropReceiver c).start (dropReceiver c).captures (dropReceiver c).row
      (receiverSeparation r.entrySeparation)

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
depth in every world: the
contract of the import, host value, stand-in or module value it holds; and
its frames meet its separation (`CapturesApart`). -/
def Realizes (G : NormalGraph ι) (code : U → ModuleCode ι U) (iface : U → Ty ι) (S : U → Prop) (u : U) :
    Prop :=
  ∃ (L : List (CallEffects.Arrow (Ty ι))) (Sg : List (CallEffects.RestArrow (Ty ι))),
    Represents G (iface u) (.arrs L Sg) ∧ KindOffers G (code u).kind L Sg ∧
    RowOffers G (code u).arity (code u).exprs (code u).conts (code u).start (code u).captures L Sg (code u).sep ∧
    (code u).captures.length = (code u).slots.length ∧
    (∀ (k : Nat) d, (code u).slots[k]? = some (Slot.linked d) → (code u).captures[k]? = some (iface d) ∧ S d) ∧
    (∀ (k : Nat) v A, (code u).slots[k]? = some (Slot.outside v) → (code u).captures[k]? = some A →
      ∀ i, ∀ j ≤ i, ∀ V : WorldT j, meaning G A j V (v i)) ∧
    CapturesApart code u

/-- The captures of a realized unit meet their types at `j`, where every
linked function's value, given by `f`, meets its interface there. -/
theorem captures_envOk {G : NormalGraph ι} {code : U → ModuleCode ι U} {iface : U → Ty ι} {S : U → Prop}
    {u : U} (hr : Realizes G code iface S u) (ho : OutsideValues code) {f : U → Tm}
    (hf : ∀ d, isVal (f d) = true ∧ Scoped 0 (f d)) {i j : Nat} (hji : j ≤ i) {V : WorldT j}
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
    exact hout k w A hs hA i j hji V

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
    obtain ⟨L, Sg, hrep, hk, hoff, hlen, -, -, hsep⟩ := hreal u hu
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    exact closure_meets_below (code u).fields hrep hk hoff (by simp [ModuleCode.captured, hlen])
      (fun v hv => (captured_values ho (approxEnv_value ho 0) u 0 v hv).2)
      (fun v hv => (captured_values ho (approxEnv_value ho 0) u 0 v hv).1)
      (hsep _ 0) (fun j hj => absurd hj (Nat.not_lt_zero j)) W
  | succ n ih =>
    intro u hu m hm W
    obtain ⟨L, Sg, hrep, hk, hoff, hlen, -, -, hsep⟩ := hreal u hu
    exact closure_meets_below (code u).fields hrep hk hoff (by simp [ModuleCode.captured, hlen])
      (fun v hv => (captured_values ho (approxEnv_value ho (n + 1)) u (n + 1) v hv).2)
      (fun v hv => (captured_values ho (approxEnv_value ho (n + 1)) u (n + 1) v hv).1)
      (hsep _ (n + 1)) (fun j hj V => captures_envOk (hreal u hu) ho (approxEnv_value ho (n + 1)) (by omega)
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
    EnvOk G (code u).captures (envOf ((code u).captured (approx code n) n) .nul) n W :=
  captures_envOk (hreal u hu) ho (fun d => approxEnv_value ho (n + 1) d) (Nat.le_refl n)
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
