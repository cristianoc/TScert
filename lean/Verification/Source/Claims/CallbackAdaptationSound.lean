import Verification.Source.Claims.CallbackAdaptation
import Verification.Source.Claims.CallbackPathClosure

/-! Soundness of the rule Adapt over a closure's runs. The closure's
summaries with its relied calls replaced by the empty footprint compose to
a bound; a support that bound respects, under a query sound at the closure's
entry, is kept by every completed run, given that each relied call keeps
it. The support is read at the closure's entry heap throughout. -/
namespace Verification.SourceClaimJson.CallbackAdaptation
open ControlFlow ProgramTyping RequestJson SourceElaboration
open CallbackEffectInference Footprints CallEffects PositiveGraphs PositiveCertificates HeapObservations

private theorem stepsLength {k before u after t} (run : Steps k before u after t) :
    before.length ≤ after.length := by
  induction run with
  | refl => exact Nat.le_refl _
  | next st _ ih => exact Nat.le_trans (step_length_le st) ih

private theorem renameM_sub {a b : Footprint} {τ : Nat → Option Nat} (hsub : ∀ e ∈ a, e ∈ b) :
    ∀ e ∈ a.renameM τ, e ∈ b.renameM τ := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  exact List.mem_map.mpr ⟨f, hsub f hf, rfl⟩

/-- **The relied-call premise of Adapt**: every completed evaluation of a
relied call in a bounded run keeps `K exit` from its prestate, in the
caller's environment. -/
def ReliedKeeps {ι : Type} [DecidableEq ι] (q : CodeRequest ι) (K : Completion → Footprint)
    (caller entry : Env) (initial : Heap) (limit : Nat) : Prop :=
  let nodes := GraphCode.program q.entry.exprs q.entry.conts
  let inputs := codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine
  let origins := (List.range inputs.length).map fun i => ({ position := i, path := [] } : ArgumentSpineRegion)
  let entries := q.claims.map fun c => ({ sequent := some ⟨c.context, .undef, c.type⟩, edges := [] } : NodeEvidence ι)
  let facts := (certifiedRootTable nodes q.entry.start inputs.length (regionTable nodes entries q.entry.start origins)).toArray
  let firstCapture := q.entry.arity + frameOffset q.entry.spine
  ∀ {l node h ρ k}, Execution nodes k initial (.at q.entry.start entry) h (.at l ρ) →
    nodes[l]? = some node → (reliedAt firstCapture (facts.getD l []) node.expression).isSome →
    ∀ {j h' t}, Steps j h (instantiate 0 ρ node.expression) h' t →
    k + 1 + j + 1 ≤ limit → ∀ exit : Completion, (match exit with
      | .normal => isVal t = true | .exceptional => ∃ v, Raises t v) →
    (finalExit node exit = false → ∀ e ∈ K .normal, e ∈ K exit) ∧ Supported (K exit) caller h h'

/-- **Adapt over a closure's runs.** Let `U` be path-closed and contain each
exit support `S exit`, and let each relied call keep `K exit`, between
`S exit` and `U`, and all of `U` where its exit stays in the closure. A
completed run's exit bound from `inferAdapted`, renamed to a caller's slots,
when it respects `U` under a query sound at entry in the caller's
environment, keeps `S exit` from entry to the run's final heap. -/
theorem inferAdapted_keeps_bounded {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {q : CodeRequest ι}
    {records out relied entry initial final state n} {sep : SepQuery} {U : Footprint}
    {S K : Completion → Footprint}
    (checked : inferAdapted G q records = .ok (out, relied))
    (sound : BoundedRecordedExitSound G q records entry initial n)
    {τ : Nat → Option Nat} {caller : Env} (hτ : ∀ i j, τ i = some j → caller j = entry i)
    (closed : CallbackPathClosure.pathClosed U = true)
    (exits : ∀ exit, (∀ e ∈ S exit, e ∈ K exit) ∧ ∀ e ∈ K exit, e ∈ U)
    (whole : K .normal = U)
    (reliedOK : ReliedKeeps q K caller entry initial n) (hq : sep.Sound caller initial)
    (run : Execution (GraphCode.program q.entry.exprs q.entry.conts) n initial
      (.at q.entry.start entry) final state) (exit : Completion) (v : Val)
    (done : state = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    ∃ bound, out.get exit = some bound ∧
      (respects sep U (bound.renameM τ) = true → Supported (S exit) caller initial final) := by
  unfold inferAdapted localSummaries at checked
  dsimp only at checked
  generalize hf : Array.foldlM (m := Except String) (β := Array (Option Summary)) _ _ records = result at checked
  cases result with
  | error err => contradiction
  | ok locals =>
    cases hc : composeChecked (GraphCode.program q.entry.exprs q.entry.conts) q.entry.start locals with
    | error err => simp [hc, bind, Except.bind] at checked
    | ok summary =>
      have hout : summary = out := by
        simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at checked
        exact checked.1
      subst hout
      have sub {a b : Footprint} {h₀ h₁ : Heap} (hs : ∀ e ∈ a, e ∈ b) (hb : Supported b caller h₀ h₁) :
          Supported a caller h₀ h₁ := fun e he => hb e (hs e he)
      refine composeChecked_keeps_bounded (admit := fun W => respects sep U (W.renameM τ) = true)
        (inside := fun h => initial.length ≤ h.length ∧ Supported U caller initial h)
        (atExit := fun e h => Supported (S e) caller initial h) hc ?_
        (fun hsub ha => respects_sub (renameM_sub hsub) ha)
        ⟨Nat.le_refl _, fun e _ l u _ hu => ⟨u, hu, Change.Holds.refl _ _ _⟩⟩ run exit v done
      intro l node h ρ k reached hn j h' t steps room ex ends
      rw [← Array.foldlM_toList] at hf
      obtain ⟨r,hr,hl,c,w,hcl,hw,-,keepsAt⟩ := sound reached hn steps room ex ends
      subst hl
      have hlen' := stepsLength steps
      cases hrel : reliedAt (q.entry.arity + frameOffset q.entry.spine)
          ((certifiedRootTable (GraphCode.program q.entry.exprs q.entry.conts) q.entry.start
            (codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine).length
            (regionTable (GraphCode.program q.entry.exprs q.entry.conts)
              (q.claims.map fun c => ({ sequent := some ⟨c.context, .undef, c.type⟩, edges := [] } : NodeEvidence ι))
              q.entry.start ((List.range (codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine).length).map
                fun slot => ({ position := slot, path := [] } : ArgumentSpineRegion)))).toArray.getD r.label [])
          node.expression with
      | none =>
        obtain ⟨s,b,hs,hb,hsw⟩ := recordFold_covers (adaptedFrame G _ _) _ _ records.toList _ locals (by simp)
          r.label ex w (.inr ⟨r,hr,rfl,node,c,by simpa using hn,by simpa using hcl,
            by unfold adaptedFrame; rw [hrel]; unfold stepFrame; exact hw⟩) hf
        refine ⟨s,b,hs,hb,fun adm ⟨hlen, kept⟩ => ?_⟩
        have keptU := keepsAt sep U τ caller hτ (respects_sub (renameM_sub hsw) adm) hq hlen kept
        split
        · exact sub (fun e he => (exits ex).2 e ((exits ex).1 e he)) keptU
        · exact ⟨Nat.le_trans hlen hlen', keptU⟩
      | some call =>
        obtain ⟨s,b,hs,hb,-⟩ := recordFold_covers (adaptedFrame G _ _) _ _ records.toList _ locals (by simp)
          r.label ex [] (.inr ⟨r,hr,rfl,node,c,by simpa using hn,by simpa using hcl,
            by unfold adaptedFrame; rw [hrel]; cases ex <;> rfl⟩) hf
        refine ⟨s,b,hs,hb,fun _ ⟨hlen, kept⟩ => ?_⟩
        obtain ⟨stays, keptK⟩ := reliedOK reached hn (by rw [hrel]; rfl) steps room ex ends
        split
        · exact CallbackPathClosure.supported_trans_of_pathClosed closed
            (fun e he => (exits ex).2 e ((exits ex).1 e he)) hlen hlen' kept
            (sub (exits ex).1 keptK)
        · rename_i internal
          have internal : finalExit node ex = false := by simpa using internal
          exact ⟨Nat.le_trans hlen hlen', CallbackPathClosure.supported_trans_of_pathClosed closed
            (fun _ he => he) hlen hlen' kept (sub (fun e he => stays internal e (whole ▸ he)) keptK)⟩

section
open CallbackPreservation CallbackInterfaceCheck CallbackOrigins

private theorem mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {B : List α} {U : List β}, B.mapM f = some U → ∀ a ∈ B, ∃ b, f a = some b ∧ b ∈ U
  | [], _, _, a, ha => by simp at ha
  | x :: B, U, hB, a, ha => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hB
    obtain ⟨b, hb, rest, hrest, rfl⟩ := hB
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, hb, List.mem_cons_self ..⟩
    · obtain ⟨c, hc, hm⟩ := mapM_mem hrest a ha
      exact ⟨c, hc, List.mem_cons_of_mem _ hm⟩

private theorem mapM_sub {α β : Type} {f : α → Option β} {U : List β} :
    ∀ (A : List α), (∀ a ∈ A, ∃ b, f a = some b ∧ b ∈ U) → ∃ S, A.mapM f = some S ∧ ∀ e ∈ S, e ∈ U
  | [], _ => ⟨[], rfl, by simp⟩
  | a :: A, h => by
    obtain ⟨b, hb, hm⟩ := h a (List.mem_cons_self ..)
    obtain ⟨S, hS, sub⟩ := mapM_sub A fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨b :: S, by simp [List.mapM_cons, hb, hS], ?_⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hm
    · exact sub e he

/-- A support inside one that projects projects inside its projection. -/
theorem project_sub {roots : RootMap} {A B U : Footprint} (hB : project roots B = some U)
    (hsub : ∀ e ∈ A, e ∈ B) : ∃ S, project roots A = some S ∧ ∀ e ∈ S, e ∈ U :=
  mapM_sub A fun a ha => mapM_mem hB a (hsub a ha)

/-- **Adapt at a checked call** (the note's Conjecture "Soundness of Adapt").
The caller's demand check with the whole support `U = T^n ++ T^x` on both
exits accepts the literal's adapted callback, `U` read at the caller's slots
is path-closed, and each relied call keeps `K exit`: all of `U` on its
normal exit, and on its exceptional exit at least the exceptional support,
within `U`, and all of `U` where the throw stays in the closure. Then the
completed invocation keeps the producer's support on its exit. -/
theorem checked_literal_adapt_supported {ι : Type} [DecidableEq ι]
    {G : PositiveGraphs.NormalGraph ι} {q : RequestJson.CodeRequest ι}
    {records : Array SinglePass.VisitRecord} {summary : Summary} {relied : List Relied}
    {codes : Array (CheckedCode ι)}
    {nodes : Array Node} {origins : Table} {inputs : Nat} {slots : Slots} {frame : List Tm}
    {d : Demand} {ev : SepEvidence} {callbacks : Nat → Option Callback} {cb : Callback}
    {U : Footprint} {K : Completion → Footprint}
    {argument : Tm} {label : Nat} {node : Node} {caps : List Tm} {kind component fields values}
    {named actual allocation : Env} {pre : List Tm} {recv self : Tm} {args : List Tm}
    {before after : Heap} {n : Nat} {W : WorldT n} {μ} {steps state}
    (exit : Completion) (v : Val)
    (picked : closure codes nodes origins inputs slots
      (invocationArguments d (argumentRoots inputs nodes.size slots frame)) argument = some cb)
    (lookup : callbacks d.parameter = some cb)
    (accept : ({ d with support := ⟨(d.support.normal ++ d.support.exceptional).eraseDups,
      (d.support.normal ++ d.support.exceptional).eraseDups⟩ } : Demand).check
        (argumentRoots inputs nodes.size slots frame) callbacks ev = true)
    (whole : project (argumentRoots inputs nodes.size slots frame)
      (d.support.normal ++ d.support.exceptional).eraseDups = some U)
    (closedU : CallbackPathClosure.pathClosed U = true)
    (site : originOf slots argument = some (.allocated label)) (atSite : nodes[label]? = some node)
    (literal : node.expression = .makeAt (.graph q.entry.arity q.entry.exprs q.entry.conts
      q.entry.start caps kind q.entry.spine.isSome component) fields values)
    (width : caps.length = q.entry.captures.length)
    (member : (⟨q.entry,summary⟩ : CheckedCode ι) ∈ codes)
    (checked : inferAdapted G q records = .ok (summary, relied))
    (layout : pre.length = (if q.entry.spine.isSome then 1 else 0))
    (arguments : NamedOperands inputs nodes.size slots frame named actual)
    (captures : NamedOperands inputs nodes.size (origins.at label) caps named
      (fun k => instantiate 0 allocation (caps.getD k .undef)))
    (invocation : ∀ p x, d.actualRoots[p]? = some (some (x, [])) → actual x = callEnv recv args p)
    (evidenceOK : ev.Holds μ (operandEnv (inputs + nodes.size) named actual) before)
    (heapOK : HeapOk n W before) (namedOK : RootsOk W named) (argsOK : RootsOk W actual)
    (normalK : K .normal = U) (withinU : ∀ e ∈ K .exceptional, e ∈ U)
    (throwK : ∀ S, project (argumentRoots inputs nodes.size slots frame) d.support.exceptional = some S →
      ∀ e ∈ S, e ∈ K .exceptional)
    (visits : BoundedRecordedExitSound G q records
      (literalEntry pre recv q.entry.arity args caps allocation self) before steps)
    (reliedOK : ReliedKeeps q K (operandEnv (inputs + nodes.size) named actual)
      (literalEntry pre recv q.entry.arity args caps allocation self) before steps)
    (run : Execution (GraphCode.program q.entry.exprs q.entry.conts) steps before
      (.at q.entry.start (literalEntry pre recv q.entry.arity args caps allocation self)) after state)
    (done : state = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    Supported (d.support.get exit) actual before after := by
  let roots := argumentRoots inputs nodes.size slots frame
  have rootsOK := argumentRoots_realizes arguments before
  obtain ⟨includes, substitution⟩ := closure_row_spec (row := ⟨q.entry,summary⟩)
    picked site atSite literal width member exit
  have hτ : ∀ i j, cb.actuals i = some j →
      operandEnv (inputs + nodes.size) named actual j = literalEntry pre recv q.entry.arity args caps allocation self i := by
    rw [substitution]
    apply literalActuals_sound layout (fun _ _ => invocationArguments_sound rootsOK invocation)
    intro k t o j ht ho hj
    obtain ⟨below, denotation⟩ := captures k t o j ht ho hj
    simpa [operandEnv,below,List.getD_eq_getElem?_getD,ht] using denotation
  have hq := SepEvidence.query_sound evidenceOK heapOK (operandEnv_rootsOk _ namedOK argsOK)
  obtain ⟨Sn, hSn, subn⟩ := project_sub whole (B := (d.support.normal ++ d.support.exceptional).eraseDups)
    (A := d.support.normal) (fun e he => List.mem_eraseDups.mpr (List.mem_append_left _ he))
  obtain ⟨Sx, hSx, -⟩ := project_sub whole (B := (d.support.normal ++ d.support.exceptional).eraseDups)
    (A := d.support.exceptional) (fun e he => List.mem_eraseDups.mpr (List.mem_append_right _ he))
  let Sf : Completion → Footprint := fun e => match e with | .normal => Sn | .exceptional => Sx
  have exits : ∀ e, (∀ x ∈ Sf e, x ∈ K e) ∧ ∀ x ∈ K e, x ∈ U := by
    intro e
    cases e with
    | normal => exact ⟨fun x hx => normalK ▸ subn x hx, fun x hx => normalK ▸ hx⟩
    | exceptional => exact ⟨throwK Sx hSx, withinU⟩
  obtain ⟨bound, found, keeps⟩ := inferAdapted_keeps_bounded (S := Sf) checked visits hτ closedU exits normalK
    reliedOK hq run exit v done
  have stableAt : stable ev U ((cb.effects.get exit).renameM cb.actuals) = true := by
    simp only [Demand.check, lookup, Bool.and_eq_true] at accept
    cases exit
    · simpa [Exits.get, whole] using accept.1
    · simpa [Exits.get, whole] using accept.2
  have resp : respects ev.query U (bound.renameM cb.actuals) = true :=
    respects_sub (renameM_sub fun e he => includes e (by simpa [found] using he)) stableAt
  have kept := keeps resp
  cases exit
  · exact (project_supported_iff rootsOK _ hSn).mpr kept
  · exact (project_supported_iff rootsOK _ hSx).mpr kept

end

end Verification.SourceClaimJson.CallbackAdaptation
