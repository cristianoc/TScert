import Verification.Source.Claims.CallbackRootPaths
import Verification.Source.Claims.PassProposals
import Verification.Source.Claims.CallbackPreservation
import Verification.Source.Claims.CallbackEffectFlow
import Verification.Semantics.SupportKept

/-! Experimental location-sensitive closure effect proposals. The ordinary
pass checks the code first. This analysis reads its step certificates and
rebases their effects into the closure entry frame, including its captures. -/
namespace Verification.SourceClaimJson.CallbackEffectInference
open Footprints CallEffects ControlFlow ProgramTyping RequestJson SourceElaboration
open PositiveGraphs PositiveCertificates LabelStore CertificateProducer

private def join (old new : Option Footprint) : Option Footprint :=
  match old, new with
  | none, a | a, none => a
  | some a, some b => some ((a ++ b).eraseDups)

private def sequence (before after : Option Footprint) : Option Footprint :=
  match before, after with
  | some a, some b => some ((a ++ b).eraseDups)
  | _, _ => none

/-- Join per-exit effects over the same normal and exceptional edges that the
single pass walks. An absent local summary identifies an unvisited node. -/
private def proposeFlow (nodes : List Node) (start : Nat) (locals : Array (Option Summary)) :
    Option (Entries × Summary) :=
  let graph := (nodes.map (·, ())).zipIdx
  let entry := (Array.replicate nodes.length none).setIfInBounds start (some [])
  let limit := locals.foldl (init := 2) fun n s =>
    n + ((s.bind (·.normal)).getD []).length + ((s.bind (·.exceptional)).getD []).length
  let transfer := fun (((node, _), label) : (Node × Unit) × Nat)
      ((entry, out) : Array (Option Footprint) × Summary) => Id.run do
    let some previous := entry.getD label none | return (entry, out)
    let some localSummary := locals.getD label none | return (entry, out)
    let normal := sequence (some previous) localSummary.normal
    let raised := sequence (some previous) localSummary.exceptional
    let mut entry := entry
    let mut out := out
    if node.continuation == .ret then out := { out with normal := join out.normal normal }
    for target in CertificateProducer.successors node.continuation do
      entry := entry.modify target.label (join · normal)
    match node.handler with
    | some target => entry := entry.modify target.label (join · raised)
    | none => out := { out with exceptional := join out.exceptional raised }
    return (entry, out)
  graphWorklist graph transfer (fun state l => state.1.getD l none)
    limit (entry, ⟨none, none⟩)

/-- Check the proposed node entries and both graph exits. A failed worklist
and a proposed table missing an effect have different diagnostics. -/
def composeChecked (nodes : List Node) (start : Nat) (locals : Array (Option Summary)) : Except String Summary := do
  let some (entries, result) := proposeFlow nodes start locals
    | throw "closure effect inference did not settle"
  if checkFlow nodes start locals entries result then return result
  throw "closure effect flow certificate does not cover every reached node and exit"

/-- A successful composition bounds every concrete evaluation completing at
either exit, given sound local summaries of completed node expressions. -/
theorem composeChecked_execution {P start locals out ρ₀ h₀ h' s' n}
    (hc : composeChecked P start locals = .ok out)
    (sound : LocalExitSound P start locals ρ₀ h₀)
    (run : Execution P n h₀ (.at start ρ₀) h' s') (exit : Completion) (v : Val)
    (done : s' = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    ∃ bound, out.get exit = some bound ∧ Post bound ρ₀ h₀ h' := by
  unfold composeChecked at hc
  cases hp : proposeFlow P start locals with
  | none => simp [hp, throw] at hc
  | some pair =>
    obtain ⟨entries,result⟩ := pair
    cases valid : checkFlow P start locals entries result <;>
      simp [hp, valid, throw, pure, Except.pure] at hc
    subst out
    exact checkFlow_execution valid sound run exit v done

theorem composeChecked_execution_bounded {P start locals out ρ₀ h₀ h' s' n}
    (hc : composeChecked P start locals = .ok out)
    (sound : BoundedLocalExitSound P start locals ρ₀ h₀ n)
    (run : Execution P n h₀ (.at start ρ₀) h' s') (exit : Completion) (v : Val)
    (done : s' = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    ∃ bound, out.get exit = some bound ∧ Post bound ρ₀ h₀ h' := by
  unfold composeChecked at hc
  cases hp : proposeFlow P start locals with
  | none => simp [hp, throw] at hc
  | some pair =>
    obtain ⟨entries,result⟩ := pair
    cases valid : checkFlow P start locals entries result <;>
      simp [hp, valid, throw, pure, Except.pure] at hc
    subst out
    exact checkFlow_execution_bounded valid sound run exit v done

/-- The composed summary of `composeChecked` bounds the same runs. -/
theorem composeChecked_keeps_bounded {P start locals out ρ₀ h₀ h' s' n admit inside atExit}
    (hc : composeChecked P start locals = .ok out)
    (sound : BoundedLocalKeeps P start locals ρ₀ h₀ n admit inside atExit)
    (mono : ∀ {a b : Footprint}, (∀ e ∈ a, e ∈ b) → admit b → admit a)
    (initial : inside h₀)
    (run : Execution P n h₀ (.at start ρ₀) h' s') (exit : Completion) (v : Val)
    (done : s' = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    ∃ bound, out.get exit = some bound ∧ (admit bound → atExit exit h') := by
  unfold composeChecked at hc
  cases hp : proposeFlow P start locals with
  | none => simp [hp, throw] at hc
  | some pair =>
    obtain ⟨entries,result⟩ := pair
    cases valid : checkFlow P start locals entries result <;>
      simp [hp, valid, throw, pure, Except.pure] at hc
    subst out
    exact checkFlow_keeps_bounded valid sound mono initial run exit v done

private def rebaseStep (facts : List GraphCode.ArgumentPathTracking.Fact)
    (slots : Nat → Option Nat) (frame : Footprint) : Footprint :=
  let link := fun p => do
    let slot ← slots p
    let fact ← facts.find? (·.slot == slot)
    return (fact.region.position, fact.region.path)
  rebaseAll { link, agree := fun _ _ => false } (frame.filter (·.2 != .keep))

section
variable {ι : Type} [DecidableEq ι]

/-- Keep the selected signature's location-specific effects for calls. A
typed own-field write uses the existing regional rule for that operation.
All other effects use the certificate's class bounds or an unrestricted bound. -/
def step (G : NormalGraph ι) (node : Node) (claim : PointClaim ι)
    (facts : List GraphCode.ArgumentPathTracking.Fact) (q : SinglePass.StepCertificate) : Summary := Id.run do
  let top := Footprints.Closed.top.fp
  if !q.scope then return ⟨some top, some top⟩
  let frames : Exits Footprint := ⟨(q.normal.head?.map (·.frame)).getD top,
    (q.exceptional.head?.map (·.frame)).getD top⟩
  let slots := PromiseCalls.actualSlot node.expression
  let normal := if ExpressionEffects.emptyType G claim.type then none else
    some (rebaseStep facts slots frames.normal)
  match ExpressionEffects.fieldWriteStep G claim.context node.expression with
  | some (receiver, key) =>
    return ⟨normal.map fun _ => rebaseStep facts some (ExpressionEffects.fieldWriteFrame receiver key), some []⟩
  | none => return ⟨normal, some (rebaseStep facts slots frames.exceptional)⟩

/-- The step summary of a recorded visit, read with the argument-path facts
of its label. -/
def stepFrame (G : NormalGraph ι) (facts : Array (List GraphCode.ArgumentPathTracking.Fact)) (node : Node)
    (claim : PointClaim ι) (record : SinglePass.VisitRecord) : Summary :=
  step G node claim (facts.getD record.label []) record.certificate

/-- Join the local summary of each recorded visit at its label. -/
def localSummaries (frameOf : Node → PointClaim ι → SinglePass.VisitRecord → Summary)
    (ns : Array Node) (claims : Array (PointClaim ι)) (records : Array SinglePass.VisitRecord) :
    Except String (Array (Option Summary)) :=
  records.foldlM (init := Array.replicate ns.size none) fun acc record => do
    let some node := ns[record.label]? | throw "closure effect record has no graph node"
    let some claim := claims[record.label]? | throw "closure effect record has no point claim"
    let frame := frameOf node claim record
    let combined := match acc.getD record.label none with
      | none => frame
      | some old => ⟨join old.normal frame.normal, join old.exceptional frame.exceptional⟩
    return acc.setIfInBounds record.label (some combined)

/-- Infer effects in closure entry slots. The code frame places the receiver
and ordinary arguments before the captures. Two different captures retain
two positions, even if a caller passes aliases for them. -/
def inferChecked (G : NormalGraph ι) (q : CodeRequest ι) (records : Array SinglePass.VisitRecord) : Except String Summary := do
  let nodes := GraphCode.program q.entry.exprs q.entry.conts
  let inputs := codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine
  let origins := (List.range inputs.length).map fun slot =>
    ({ position := slot, path := [] } : ArgumentSpineRegion)
  let entries := q.claims.map fun c => ({ sequent := some ⟨c.context, .undef, c.type⟩, edges := [] } : NodeEvidence ι)
  let facts := certifiedRootTable nodes q.entry.start inputs.length (regionTable nodes entries q.entry.start origins) |>.toArray
  let locals ← localSummaries (stepFrame G facts) nodes.toArray q.claims.toArray records
  composeChecked nodes q.entry.start locals

end

/-- Consume an inferred proposal at the proof-rule boundary. The supplied
actuals map the closure frame's ordinary and captured slots to caller slots. -/
def Summary.callback (summary : Summary) (actuals : Nat → Option Nat) :
    CallbackPreservation.Callback :=
  ⟨summary.map (·.getD []), actuals⟩


structure CheckedCode (ι : Type) where
  entry : CodeEntry ι
  summary : Summary

/-- Process the closure requests in their dependency order, retaining the
same accepted entries, checked rows and summary answers between requests. -/
def inferCodeRows {σ ι : Type} [Labels ι] [StoreView σ ι] [CertificateProducer.Instantiates ι]
    (r : SourceRequest σ ι) (fuel : Nat) (known : List (ProgramCertificates.Evidence ι))
    (accepted : List (CodeEntry ι)) (table : Array (CheckedCode ι))
    (answers : CertificateProducer.Answered (RequestJson.graph r.toRequest)) :
    List (CodeRequest ι × Nat) → Except String (Array (CheckedCode ι) ×
      CertificateProducer.Answered (RequestJson.graph r.toRequest))
  | [] => if summariesChecked r answers.summaries.toList then .ok (table,answers)
    else .error "the closure code table's read summaries did not pass"
  | (q,code) :: rest => do
    let G := RequestJson.graph r.toRequest
    let images := StoreView.images r.types
    let labels := r.searchLabels
    if !codeConditions q.entry || !asyncAdmits q.async q.entry.row.effect then
      throw s!"closure {code} did not meet its signature conditions"
    let rq := q.asRequest r.toRequest
    let hints := (r.codeHints[code]?).getD {}
    let pool := CertificateProducer.vocabulary G labels rq.claims rq.inputs
    let (outcome, counts, next, _) := SinglePass.run G images pool fuel rq.program rq.claims rq.start
      rq.inputs q.entry.goal hints.requirements hints.cuts hints.candidates rq.entryIndices
      [] known (GraphCode.admits accepted) r.aliases .ordinary answers
      (bound := codeBound q.entry) (grading := true)
    let .accepted := outcome | throw s!"closure {code} was refused: {outcome}"
    let summary : Summary ← if q.async then
      pure ⟨some Footprints.Closed.top.fp, some Footprints.Closed.top.fp⟩
      else (inferChecked G q counts.grades).mapError fun msg => s!"closure {code}: {msg}"
    inferCodeRows r fuel known (accepted ++ [q.entry]) (table.push ⟨q.entry,summary⟩) next rest

/-- Check the code requests in their usual dependency order and infer their
effects using the accepted walks. The parent graph can consume these without
walking closure source a second time. -/
def inferCodes {σ ι : Type} [Labels ι] [StoreView σ ι]
    [CertificateProducer.Instantiates ι] (r : SourceRequest σ ι) (fuel : Nat) :
    Except String (Array (CheckedCode ι) × List (ProgramCertificates.Evidence ι) ×
      CertificateProducer.Answered (RequestJson.graph r.toRequest)) := do
  if r.qualification.isSome then throw "regional closure inference needs an ordinary graph"
  let G := RequestJson.graph r.toRequest
  let images := StoreView.images r.types
  let labels := r.searchLabels
  let valid := StoreView.valid r.types
  let (known, answers) ← match ExpressionClaims.produceUsing G images labels valid
      (StoreView.projection r.types) fuel r.obligations {} with
    | .ok result => pure result
    | .error _ => throw "the member's expression obligations did not pass"
  let (rendered, answers) := ExpressionClaims.renderKnownUsing G images labels valid r.nodePlans answers
  let known := known ++ rendered
  let (table,answers) ← inferCodeRows r fuel known [] #[] answers r.codes.zipIdx
  return (table, known, answers)

end Verification.SourceClaimJson.CallbackEffectInference

namespace Verification.SourceClaimJson.CallbackEffectInference
open Footprints GraphCode.ArgumentPathTracking

/-- A reached step's checked frame composes with the effects already incurred
at the closure entry. Each slot link is justified by an argument-path fact
at the step, and entries permitting only identity may be discarded. -/
theorem rebaseStep_post {facts : List GraphCode.ArgumentPathTracking.Fact} {slots : Nat → Option Nat}
    {previous frame : Footprint} {entry node actual : Env} {initial before after : Heap}
    (history : Post previous entry initial before) (localPost : Post frame actual before after)
    (factsOK : Holds facts node entry initial)
    (slotsOK : ∀ i j, slots i = some j → actual i = node j)
    (categories : HeapCategories before) :
    Post (previous ++ rebaseStep facts slots frame).eraseDups entry initial after := by
  let writes := frame.filter (·.2 != .keep)
  have writesOK : Post writes actual before after := by
    refine ⟨localPost.1, fun l v hv => ?_⟩
    obtain ⟨v',hv',allowed⟩ := localPost.2 l v hv
    refine ⟨v',hv',?_⟩
    rcases allowed with same | ⟨e,he,hm,hchange⟩
    · exact .inl same
    · by_cases keep : e.2 = .keep
      · rw [keep] at hchange
        exact .inl hchange
      · exact .inr ⟨e, List.mem_filter.mpr ⟨he, by simpa using keep⟩, hm, hchange⟩
  let link := fun i => do
    let j ← slots i
    let f ← facts.find? (fun (f : GraphCode.ArgumentPathTracking.Fact) => f.slot == j)
    pure (f.region.position, f.region.path)
  let ev : RebaseEvidence := { link, agree := fun _ _ => false }
  have valid : RebaseOk ev actual entry initial before := by
    refine ⟨?_, by intros; contradiction, by intros; contradiction, categories⟩
    intro i x q hx
    cases hi : slots i with
    | none => simp [ev,link,hi] at hx
    | some j =>
      cases hf : facts.find? (·.slot == j) with
      | none => simp [ev,link,hi,hf] at hx
      | some f =>
        simp [ev,link,hi,hf] at hx
        obtain ⟨rfl,rfl⟩ := hx
        have slotEq : f.slot = j := by simpa using List.find?_some hf
        simpa [slotEq, slotsOK _ _ hi] using factsOK f (List.mem_of_find?_eq_some hf)
  exact Post.compose_at (cl := fun _ _ => none) history writesOK valid
    (Footprint.le_of_subset fun _ he => List.mem_eraseDups.mpr he)
    (by intro _ _ _ _ h; contradiction)

/-- The rebased step summary keeps every support it respects, read at the
closure entry, across the step: no prior footprint is needed. -/
theorem rebaseStep_keeps {facts : List GraphCode.ArgumentPathTracking.Fact} {slots : Nat → Option Nat}
    {frame : Footprint} {entry node actual : Env} {initial before after : Heap}
    (localPost : Post frame actual before after)
    (factsOK : Holds facts node entry initial)
    (slotsOK : ∀ i j, slots i = some j → actual i = node j)
    (categories : HeapCategories before) :
    KeepsAt (rebaseStep facts slots frame) entry initial before after := by
  let link := fun i => do
    let j ← slots i
    let f ← facts.find? (fun (f : GraphCode.ArgumentPathTracking.Fact) => f.slot == j)
    pure (f.region.position, f.region.path)
  let ev : RebaseEvidence := { link, agree := fun _ _ => false }
  have valid : RebaseOk ev actual entry initial before := by
    refine ⟨?_, by intros; contradiction, by intros; contradiction, categories⟩
    intro i x q hx
    cases hi : slots i with
    | none => simp [ev,link,hi] at hx
    | some j =>
      cases hf : facts.find? (·.slot == j) with
      | none => simp [ev,link,hi,hf] at hx
      | some f =>
        simp [ev,link,hi,hf] at hx
        obtain ⟨rfl,rfl⟩ := hx
        have slotEq : f.slot = j := by simpa using List.find?_some hf
        simpa [slotEq, slotsOK _ _ hi] using factsOK f (List.mem_of_find?_eq_some hf)
  exact KeepsAt.of_rebase valid localPost

end Verification.SourceClaimJson.CallbackEffectInference

namespace Verification.SourceClaimJson.CallbackEffectInference
open ControlFlow GraphCode Footprints ProgramTyping RequestJson SourceElaboration
open PositiveGraphs CallEffects CertificateProducer HeapObservations

def CoversWrites (locals : Array (Option Summary)) (l : Nat) (exit : Completion)
    (writes : Footprint) : Prop :=
  ∃ s bound, locals.getD l none = some s ∧ s.get exit = some bound ∧ ∀ e ∈ writes, e ∈ bound

private theorem join_covers {a b : Option Footprint} {w : Footprint}
    (h : a = some w ∨ b = some w) :
    ∃ bound, join a b = some bound ∧ ∀ e ∈ w, e ∈ bound := by
  rcases h with rfl | rfl
  · cases b <;> simp [join] <;> grind
  · cases a <;> simp [join] <;> grind

theorem recordFold_covers {ι : Type} (frameOf : Node → PointClaim ι → SinglePass.VisitRecord → Summary)
    (ns : Array Node) (claims : Array (PointClaim ι))
    (records : List SinglePass.VisitRecord) (acc final : Array (Option Summary))
    (size : acc.size = ns.size) (l : Nat) (exit : Completion) (w : Footprint)
    (source : CoversWrites acc l exit w ∨ ∃ r ∈ records, r.label = l ∧
      ∃ node claim, ns[l]? = some node ∧ claims[l]? = some claim ∧
        (frameOf node claim r).get exit = some w)
    (folded : records.foldlM (m := Except String) (fun acc r => do
      let some node := ns[r.label]? | throw "closure effect record has no graph node"
      let some claim := claims[r.label]? | throw "closure effect record has no point claim"
      let s := frameOf node claim r
      let merged := match acc.getD r.label none with
        | none => s
        | some old => ⟨join old.normal s.normal, join old.exceptional s.exceptional⟩
      return acc.setIfInBounds r.label (some merged)) acc = .ok final) :
    CoversWrites final l exit w := by
  induction records generalizing acc with
  | nil =>
    cases folded
    simpa using source
  | cons head tail ih =>
    cases hn : ns[head.label]? with
    | none => simp [List.foldlM_cons, hn, throw, throwThe, bind, Except.bind] at folded
    | some node =>
      cases hc : claims[head.label]? with
      | none => simp [List.foldlM_cons, hn, hc, throw, throwThe, bind, Except.bind] at folded
      | some claim =>
        simp only [List.foldlM_cons, hn, hc, pure_bind] at folded
        apply ih _ (by simpa using size) _ folded
        have inside : head.label < acc.size := size ▸ (Array.getElem?_eq_some_iff.mp hn).1
        rcases source with ⟨old,bound,ho,hb,sub⟩ | ⟨r,hr,hl,n,c,hn',hc',hw⟩
        · left
          by_cases eq : head.label = l
          · subst l
            simp only [CoversWrites, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
              ite_eq_left inside]
            rw [← Array.getD_eq_getD_getElem?, ho]
            obtain ⟨b,hj,hs⟩ := join_covers (b := (frameOf node claim head).get exit) (.inl hb)
            exact ⟨_,b,rfl,by cases exit <;> simpa only [Exits.get, Array.getD_eq_getD_getElem?] using hj, fun e he => hs e (sub e he)⟩
          · exact ⟨old,bound,by simpa [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, eq] using ho,hb,sub⟩
        · rcases List.mem_cons.mp hr with rfl | rest
          · left
            subst l
            cases hn.symm.trans hn'
            cases hc.symm.trans hc'
            simp only [CoversWrites, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
              ite_eq_left inside]
            rw [← Array.getD_eq_getD_getElem?]
            cases h : acc.getD r.label none with
            | none => exact ⟨_,w,rfl,by simpa only [Array.getD_eq_getD_getElem?] using hw,fun _ he => he⟩
            | some old =>
              obtain ⟨b,hj,hs⟩ := join_covers (a := old.get exit) (.inr hw)
              exact ⟨_,b,rfl,by cases exit <;> simpa only [Exits.get, Array.getD_eq_getD_getElem?] using hj,hs⟩
          · exact .inr ⟨r,rest,hl,n,c,hn',hc',hw⟩

/-- Concrete completed node evaluations must be represented by a visit in
the same accepted walk. Its local bound is measured at closure entry. -/
def RecordedExitSound {ι : Type} (G : NormalGraph ι) (q : CodeRequest ι)
    (records : Array SinglePass.VisitRecord) (entry : Env) (initial : Heap) : Prop :=
  let nodes := GraphCode.program q.entry.exprs q.entry.conts
  let inputs := codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine
  let origins := (List.range inputs.length).map fun i => ({ position := i, path := [] } : ArgumentSpineRegion)
  let entries := q.claims.map fun c => ({ sequent := some ⟨c.context, .undef, c.type⟩, edges := [] } : NodeEvidence ι)
  let facts := (certifiedRootTable nodes q.entry.start inputs.length (regionTable nodes entries q.entry.start origins)).toArray
  ∀ {l node h ρ k}, Execution nodes k initial (.at q.entry.start entry) h (.at l ρ) →
    nodes[l]? = some node → ∀ {j h' t}, Steps j h (instantiate 0 ρ node.expression) h' t →
    ∀ exit : Completion, (match exit with
      | .normal => isVal t = true | .exceptional => ∃ v, Raises t v) →
    ∃ r ∈ records.toList, r.label = l ∧ ∃ claim w, q.claims[l]? = some claim ∧
      (step G node claim (facts.getD l []) r.certificate).get exit = some w ∧
      ∀ prior : Footprint, Post prior entry initial h → Post (prior ++ w).eraseDups entry initial h'

/-- Visit validity at every node exit within the graph transition budget. -/
def BoundedRecordedExitSound {ι : Type} (G : NormalGraph ι) (q : CodeRequest ι)
    (records : Array SinglePass.VisitRecord) (entry : Env) (initial : Heap) (limit : Nat) : Prop :=
  let nodes := GraphCode.program q.entry.exprs q.entry.conts
  let inputs := codeFrame q.entry.arity q.entry.row q.entry.captures q.entry.spine
  let origins := (List.range inputs.length).map fun i => ({ position := i, path := [] } : ArgumentSpineRegion)
  let entries := q.claims.map fun c => ({ sequent := some ⟨c.context, .undef, c.type⟩, edges := [] } : NodeEvidence ι)
  let facts := (certifiedRootTable nodes q.entry.start inputs.length (regionTable nodes entries q.entry.start origins)).toArray
  ∀ {l node h ρ k}, Execution nodes k initial (.at q.entry.start entry) h (.at l ρ) →
    nodes[l]? = some node → ∀ {j h' t}, Steps j h (instantiate 0 ρ node.expression) h' t →
    k + 1 + j + 1 ≤ limit → ∀ exit : Completion, (match exit with
      | .normal => isVal t = true | .exceptional => ∃ v, Raises t v) →
    ∃ r ∈ records.toList, r.label = l ∧ ∃ claim w, q.claims[l]? = some claim ∧
      (step G node claim (facts.getD l []) r.certificate).get exit = some w ∧
      (∀ prior : Footprint, Post prior entry initial h → Post (prior ++ w).eraseDups entry initial h') ∧
      KeepsAt w entry initial h h'

/-- Sound recorded visits suffice for the actual inferred closure summary.
Repeated visits to a label may use different local bounds on either exit. -/
theorem inferChecked_execution {ι : Type} {G : NormalGraph ι} {q : CodeRequest ι}
    {records out entry initial final state n}
    (checked : inferChecked G q records = .ok out)
    (sound : RecordedExitSound G q records entry initial)
    (run : Execution (GraphCode.program q.entry.exprs q.entry.conts) n initial
      (.at q.entry.start entry) final state) (exit : Completion) (v : Val)
    (done : state = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    ∃ bound, out.get exit = some bound ∧ Post bound entry initial final := by
  unfold inferChecked localSummaries at checked
  dsimp only at checked
  generalize hf : Array.foldlM (m := Except String) (β := Array (Option Summary)) _ _ records = result at checked
  cases result with
  | error err => contradiction
  | ok locals =>
    apply composeChecked_execution checked _ run exit v done
    intro l node h ρ k reached hn j h' t steps ex ends
    obtain ⟨r,hr,hl,c,w,hc,hw,extendPost⟩ := sound reached hn steps ex ends
    rw [← Array.foldlM_toList] at hf
    subst hl
    obtain ⟨s,b,hs,hb,sub⟩ := recordFold_covers (stepFrame G _) _ _ records.toList _ locals (by simp)
      r.label ex w (.inr ⟨r,hr,rfl,node,c,by simpa using hn,by simpa using hc,by unfold stepFrame; exact hw⟩) hf
    refine ⟨s,b,hs,hb,fun prior post => (extendPost prior post).mono (cl := fun _ _ => none)
      (Footprint.le_of_subset ?_) (by intro _ _ _ _ miss; contradiction)⟩
    intro e member
    apply List.mem_eraseDups.mpr
    rcases List.mem_append.mp (List.mem_eraseDups.mp member) with hp | hw
    · exact List.mem_append_left _ hp
    · exact List.mem_append_right _ (sub e hw)

theorem inferChecked_execution_bounded {ι : Type} {G : NormalGraph ι} {q : CodeRequest ι}
    {records out entry initial final state n}
    (checked : inferChecked G q records = .ok out)
    (sound : BoundedRecordedExitSound G q records entry initial n)
    (run : Execution (GraphCode.program q.entry.exprs q.entry.conts) n initial
      (.at q.entry.start entry) final state) (exit : Completion) (v : Val)
    (done : state = (match exit with | .normal => .done v | .exceptional => .raised v)) :
    ∃ bound, out.get exit = some bound ∧ Post bound entry initial final := by
  unfold inferChecked localSummaries at checked
  dsimp only at checked
  generalize hf : Array.foldlM (m := Except String) (β := Array (Option Summary)) _ _ records = result at checked
  cases result with
  | error err => contradiction
  | ok locals =>
    apply composeChecked_execution_bounded checked _ run exit v done
    intro l node h ρ k reached hn j h' t steps room ex ends
    obtain ⟨r,hr,hl,c,w,hc,hw,extendPost,-⟩ := sound reached hn steps room ex ends
    rw [← Array.foldlM_toList] at hf
    subst hl
    obtain ⟨s,b,hs,hb,sub⟩ := recordFold_covers (stepFrame G _) _ _ records.toList _ locals (by simp)
      r.label ex w (.inr ⟨r,hr,rfl,node,c,by simpa using hn,by simpa using hc,by unfold stepFrame; exact hw⟩) hf
    refine ⟨s,b,hs,hb,fun prior post => (extendPost prior post).mono (cl := fun _ _ => none)
      (Footprint.le_of_subset ?_) (by intro _ _ _ _ miss; contradiction)⟩
    intro e member
    apply List.mem_eraseDups.mpr
    rcases List.mem_append.mp (List.mem_eraseDups.mp member) with hp | hw
    · exact List.mem_append_left _ hp
    · exact List.mem_append_right _ (sub e hw)

end Verification.SourceClaimJson.CallbackEffectInference
