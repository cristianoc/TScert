import Verification.Source.Claims.CallbackTypicalCaptures
import Verification.Source.Claims.CallbackCallerAccepted
import Verification.Source.Claims.CallbackPublicContract

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackOrigins CallbackPreservation CallbackEffectInference CallbackInferencePlan ControlFlow
open CertificateProducer PositiveCertificates ProgramTyping PositiveRules TolerantFrames PositiveGraphs GraphCode CallEffects Footprints HeapObservations CallArguments LabelStore

/-- Evidence from the caller only. The argument identifies a literal at one
checked allocation. Its selected row, captured types and allocation operands
are determined by the accepted caller's code and prefix. -/
structure FixedLiteral {ι : Type} [Labels ι] (P : Program) (origins : Table)
    (codes : Array (CheckedCode ι)) (label : Nat) (argument : Tm) (slotTypes : List (Option (Ty ι))) where
  site : Nat
  node : Node
  q : RequestJson.CodeRequest ι
  summary : Summary
  caps : List Tm
  comp : ComponentTag
  fields : List PropKey
  vals : List Tm
  origin : originOf (origins.at label) argument = some (.allocated site)
  lookup : P[site]? = some node
  literal : node.expression = .makeAt (.graph q.entry.arity q.entry.exprs q.entry.conts q.entry.start caps .call false comp) fields vals
  width : caps.length = q.entry.captures.length
  member : (⟨q.entry,summary⟩ : CheckedCode _) ∈ codes
  fixed : q.entry.spine = none
  named : checkCaptureSlots (origins.at site) (visibleNames slotTypes (origins.at label))
    (slotTypes.map (·.getD [])) caps q.entry.captures = true

private def inspectedValue (x : α) : {y // x = y} := ⟨x,rfl⟩

private def verified? (p : Prop) [Decidable p] : Option (PLift p) :=
  if h : p then some ⟨h⟩ else none

@[nospecialize] private def compareInput {ι : Type} [Labels ι] [Instantiates ι]
    (G : NormalGraph ι) (images : InstanceImageCheck G) (expected offered : Ty ι) :
    Option (PLift (FamLe (meaning G expected) (meaning G offered))) := do
  let choice ← (subtypeSearch G images expected offered).value
  let ⟨sound⟩ ← verified? (checkUsing G images expected offered choice = true)
  return ⟨acceptedUsing sound⟩

/-- Componentwise ordinary subtyping for a single fixed call signature. -/
@[nospecialize] private def readArgumentComparisons {ι : Type} [Labels ι] [Instantiates ι]
    (G : NormalGraph ι) (images : InstanceImageCheck G) :
    (xs ys : List (Ty ι)) → Option (PLift (ArgsLe (xs.map (meaning G)) (ys.map (meaning G))))
  | [], [] => some ⟨.nil⟩
  | x :: xs, y :: ys => do
    let ⟨checked⟩ ← compareInput G images x y
    let ⟨tail⟩ ← readArgumentComparisons G images xs ys
    return ⟨.cons checked tail⟩
  | _, _ => none

/-- Input variance and precondition entailment needed to call the selected
literal row with the producer's declared inputs. -/
structure LiteralDomain {ι : Type} (G : NormalGraph ι) (expected offered : Arrow (Ty ι)) : Prop where
  receiver : FamLe (meaning G expected.receiver) (meaning G offered.receiver)
  arguments : ArgsLe (expected.arguments.map (meaning G)) (offered.arguments.map (meaning G))
  preconditions : ∀ F ∈ offered.effect.pre, F ∈ expected.effect.pre

theorem LiteralDomain.holds {ι : Type} {G : NormalGraph ι}
    {expected offered : Arrow (Ty ι)} (row : LiteralDomain G expected offered) {s recv args}
    (publicCall : FixedCallbackDomain G expected s recv args) : FixedCallbackDomain G offered s recv args :=
  ⟨row.receiver _ _ _ publicCall.1, ArgsShort_mono row.arguments publicCall.2.1,
    fun F member => publicCall.2.2 F (row.preconditions F member)⟩

/-- Recover the graph and its capture operands at the actual allocation,
then choose a checked fixed row against the public signature. -/
@[nospecialize] def readFixedLiteral {ι : Type} [Labels ι] [Instantiates ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (P : Program) (origins : Table) (codes : Array (CheckedCode ι))
    (requests : List (RequestJson.CodeRequest ι)) (label : Nat) (argument : Tm) (slotTypes : List (Option (Ty ι)))
    (expected : Arrow (Ty ι)) :
    Except String (Σ lit : FixedLiteral P origins codes label argument slotTypes, PLift (LiteralDomain G expected lit.q.entry.row)) := do
  let ⟨some (.allocated site),org⟩ := inspectedValue (originOf (origins.at label) argument)
    | throw (CallbackPreservation.scopeRefusal "readFixedLiteral" "callback has no checked literal allocation")
  let ⟨some node,found⟩ := inspectedValue (P[site]?) | throw "missing callback allocation"
  let ⟨.makeAt (.graph _ _ _ _ caps .call false comp) fs vs,_⟩ := inspectedValue node.expression
    | throw (CallbackPreservation.scopeRefusal "readFixedLiteral" "callback must be a receiverless fixed literal")
  let checkRow := fun (q : RequestJson.CodeRequest ι) => do
    if q.async then none else
      let ⟨code⟩ ← verified? (node.expression = .makeAt (.graph q.entry.arity q.entry.exprs q.entry.conts
        q.entry.start caps .call false comp) fs vs)
      let ⟨width⟩ ← verified? (caps.length = q.entry.captures.length)
      let ⟨fixed⟩ ← verified? (q.entry.spine = none)
      let ⟨visible⟩ ← verified? (checkCaptureSlots (origins.at site) (visibleNames slotTypes (origins.at label))
        (slotTypes.map (·.getD [])) caps q.entry.captures = true)
      let some checked := codes.toList.attach.find? (fun c => c.val.entry == q.entry) | none
      let ⟨eq⟩ ← verified? (checked.val.entry = q.entry)
      let ⟨receiver⟩ ← compareInput G images expected.receiver q.entry.row.receiver
      let ⟨args⟩ ← readArgumentComparisons G images expected.arguments q.entry.row.arguments
      let ⟨pre⟩ ← verified? (q.entry.row.effect.pre.all (expected.effect.pre.contains ·) = true)
      have mem : (⟨q.entry,checked.val.summary⟩ : CheckedCode _) ∈ codes := by
        rw [← eq]
        exact Array.mem_toList_iff.mp checked.property
      let lit : FixedLiteral P origins codes label argument slotTypes :=
        ⟨site,node,q,checked.val.summary,caps,comp,fs,vs,org,found,code,width,mem,fixed,visible⟩
      let domain : LiteralDomain G expected lit.q.entry.row :=
        ⟨receiver,args,fun F h => List.contains_iff_mem.mp (List.all_eq_true.mp pre F h)⟩
      return (⟨lit,⟨domain⟩⟩ : Σ lit : FixedLiteral P origins codes label argument slotTypes, PLift (LiteralDomain G expected lit.q.entry.row))
  let some witness := requests.findSome? checkRow
    | throw (CallbackPreservation.scopeRefusal "readFixedLiteral" "no fixed callback row matches the public signature and capture origins")
  return witness

/-- The public Use rule for a literal, from the checked caller alone. Its
producer may dispatch any number of times at different heaps. Only the
public demand, the actual parameter values and the evaluated call appear. -/
theorem FixedLiteral.satisfies {f caller fuel interfaces forwarded}
    {a : AcceptedCaller f caller fuel interfaces [] forwarded} {l argument slotTypes}
    (lit : FixedLiteral a.request.program a.origins a.codes l argument slotTypes)
    {entry h₀ h ρ k n₀} {W₀ : WorldT n₀}
    (callerValues : ∀ i < a.request.inputs.length, isVal (entry i) = true)
    (callerRoots : RootsOk W₀ entry) (callerHeap : HeapOk n₀ W₀ h₀)
    (reached : Execution a.request.program k h₀ (.at a.request.start entry) h (.at l ρ))
    {frame : List Tm} {d : Demand} {actual : Env}
    (accepted : d.check (argumentRoots a.request.inputs.length a.request.program.length (a.origins.at l) frame)
      (fun p => frame[p]?.bind (closure a.codes a.request.program.toArray a.origins a.request.inputs.length
        (a.origins.at l) (invocationArguments d (argumentRoots a.request.inputs.length a.request.program.length
          (a.origins.at l) frame)))) (separation a.request.inputs.length a.request.program.length (a.origins.at l)) = true)
    (atArg : frame[d.parameter]? = some argument)
    (passed : ∀ i t o j, frame[i]? = some t → originOf (a.origins.at l) t = some o →
      identity a.request.inputs.length o = some j → actual i = instantiate 0 ρ t)
    (s : IndexedHeap) {recv args after v ticks}
    (typed : PartialEnv (RequestJson.graph a.request.toRequest) slotTypes ρ s.n s.W)
    (argsOK : RootsOk s.W actual) (recvRefs : RefsOk s.W recv) (argRefs : ∀ t ∈ args, RefsOk s.W t)
    (domain : FixedCallbackDomain (RequestJson.graph a.request.toRequest) lit.q.entry.row s recv args)
    (values : Values args) (bindings : ∀ p x, d.actualRoots[p]? = some (some (x,[])) → actual x = callEnv recv args p)
    (run : Steps ticks s.h (.invoke (actual d.parameter) recv args) after v)
    (budget : ticks < s.n) (finish : isVal v = true) : Supported d.support.normal actual s.h after := by
  let q := lit.q
  have hist := checkedNames_reached a.names callerValues reached
  have atFrame := passed _ _ _ _ atArg lit.origin
    (show identity a.request.inputs.length (.allocated lit.site) = some (a.request.inputs.length + lit.site) from rfl)
  obtain ⟨slot,term,atSlot⟩ := namedOrigin_slot lit.origin
  have closed : Scoped 0 (instantiate 0 ρ argument) := by simpa [term,instantiate] using typed.1 slot
  have capTypes := reached_partialCaptureTypes hist lit.origin lit.lookup lit.literal
    (checkCaptureSlots_sound lit.named) typed closed
  have member : lit.q.entry ∈ a.codes.toList.map (·.entry) :=
    List.mem_map.mpr ⟨⟨_,_⟩,by simpa using lit.member,rfl⟩
  have spec := inferCodes_table_sound a.codeAnswers _ (List.contains_iff_mem.mpr member)
    (RequestJson.graph a.request.toRequest).env
  have recvVal := (meaning_value domain.1).1
  cases run with
  | refl => contradiction
  | next first rest =>
    rename_i hh target ticks
    apply checkedCaller_literal_supported (q := q) a.names callerValues callerRoots callerHeap reached .normal v
      accepted atArg lit.origin lit.lookup (by simpa [q,lit.fixed] using lit.literal) lit.width lit.member a.codeAnswers
      (pre := []) (by simp [q,lit.fixed]) passed bindings s.ok argsOK s.adm (steps := ticks) (by omega) s.pos
      (self := actual d.parameter) _ rfl
    intro allocation obj
    obtain ⟨fs,oid,obj⟩ := obj
    have concrete := atFrame.trans obj
    simp only [q,lit.fixed,Option.isSome_none] at concrete obj
    let cs := instantiateArgs 0 allocation lit.caps
    let self := actual d.parameter
    let locals := recv :: parameters lit.q.entry.arity args ++ (cs ++ [self])
    have actualStep : Step s.h (.invoke self recv args) s.h
        (.goto lit.q.entry.exprs lit.q.entry.conts lit.q.entry.start locals .nul lit.comp) := by
      dsimp only [locals,cs,self]
      rw [concrete]
      exact Step.callGraph recvVal values rfl
    obtain ⟨rfl,rfl⟩ := Step_det first actualStep
    have exec := execution_of_sim .goto rest finish
    have captures := capTypes fs cs oid obj
    rw [← atFrame] at captures
    have sameWorld : WExt (trunc s.n (Nat.le_refl _) s.W) s.W := by rw [trunc_id]; exact WExt_refl _
    have frameOK := frame_envOk spec.1 captures (Nat.le_refl _) sameWorld domain.1 domain.2.1
    have capRefs := (graph_code_refs (concrete ▸ argsOK d.parameter)).2
    have refs : RootsOk s.W (envOf locals .nul) := by
      apply envOf_refs_of _ RefsOk_nul
      intro t mem
      simp only [locals,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at mem
      rcases mem with (rfl | param) | cap | rfl
      · exact recvRefs
      · exact (Kinds.parameters_mem param).elim (argRefs _) (fun eq => eq ▸ RefsOk_undef)
      · exact capRefs _ cap
      · exact argsOK d.parameter
    have indices : HeapKnowledge.IndexHolds ⟨envOf locals .nul,s.h⟩ (codeEntryIndices lit.q.entry) (envOf locals .nul) s.h := by
      apply codeEntryIndices_holds
      intro _ F hp
      exact (Effect.pre_frame (Effect.belowRow_entry spec.2.1) hp recv args (cs ++ [self]) .nul s.h).mp (domain.2.2 F hp)
    simpa [q,literalEntry,lit.fixed,codeFrame,locals,cs,self,instantiateArgs_eq_map] using
      And.intro frameOK (And.intro refs (And.intro indices exec))

end Verification.SourceClaimJson.CallbackInterfaceCheck
