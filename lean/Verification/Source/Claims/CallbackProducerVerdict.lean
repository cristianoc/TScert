import Verification.Source.Claims.CallbackFixedOperands
import Verification.Source.Claims.CallbackPublishedAcceptance
import Verification.Source.Claims.GraphAssertions

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallbackInferencePlan CallbackEffectInference CallbackOrigins TolerantFrames GraphCode ControlFlow
open ProgramTyping PositiveRules PositiveGraphs LabelStore PassUnit HeapObservations

/-- The source graph may be used at any ordinary entry meeting just its
published callback requirement. Its written assertions hold along every
execution from that entry. -/
def ProducerBodySafe {f : FilePlans} (r : Req f) (p : Published) : Prop :=
  ∀ η n (W : WorldT n) h L d (I : ∀ k, WorldT k → Prop),
    let G := reassign (RequestJson.graph r.toRequest) η
    TolerantFrames.Target.EntryHolds G r.inputs r.entrySeparation r.entryIndices (envOf L d) n W h →
    RootsOk W (envOf L d) → (∀ j, isVal (envOf L d j) = true) →
    I n W → (∀ {k} {U : WorldT (k+1)} {V : WorldT k}, I (k+1) U → WExt (trunc k (Nat.le_succ _) U) V → I k V) →
    PublicDemandsWith I (formalDomain G r.inputs) p.interface (envOf L d) →
    SafePostExc (excOf G) (GoalHolds G r.goal (r.goal.argument (envOf L d))) (fun _ _ => True) (fun _ => True)
      n W h (gotoOf r.program r.start L d r.comp) ∧
    (∀ l k, (l,k) ∈ r.assertions → ∀ j h' ρ', j < n → ReachesIn r.program j h (.at r.start (envOf L d)) h' (.at l ρ') →
      HeapKnowledge.Holds k ⟨envOf L d,h⟩ ρ' h') ∧
    (r.footprint ≠ .top ∨ r.onThrow = true ∨ r.fresh = true →
      SafePostExc (excOf G) (GoalHolds G r.goal (r.goal.argument (envOf L d)))
        (fun h' v => r.footprint.Holds h h' ∧ (r.fresh = true → Footprints.FreshAt h.length v))
        (fun h' => r.onThrow = true → r.footprint.Holds h h') n W h (gotoOf r.program r.start L d r.comp)) ∧
    (r.ensures ≠ [] → SafePost (excOf G) (GoalHolds G r.goal (r.goal.argument (envOf L d)))
      (fun h' v => GraphCode.EnsuresAt r.ensures ⟨envOf L d,h⟩ h' (push v (envOf L d)))
      n W h (gotoOf r.program r.start L d r.comp))


def ProducerMemberSafe (f : FilePlans) (i : Nat) (p : Published) : Prop :=
  f.fr.group i = [i] ∧ ∃ name pos, ∃ r : Req f, PlanAt f i name pos r ∧ name = p.name ∧ p.position = some pos ∧
    ProducerBodySafe r p ∧ r.qualification = none ∧ r.async = false ∧ RegionalClause r ∧ CodeAssertionsClause r ∧ declaredEffect r = true

private def observedValue (x : α) : {y // x = y} := ⟨x,rfl⟩

private def producerNeed (message : String) (p : Prop) [Decidable p] : Except String (PLift p) :=
  if ok : p then .ok ⟨ok⟩ else .error message

/-- The successful decision carries the actual publication. Its only
semantic assumption at a runtime entry describes the public callback. -/
def certifyProducer (f : FilePlans) (i fuel : Nat) (dependencies : List Published) :
    Except String {p : Published // PassUnit.OverStore f → ProducerMemberSafe f i p} := do
  let ⟨group⟩ ← producerNeed "producer must be a singleton source unit" (f.fr.group i = [i])
  let ⟨some (decl,_,_),hdecl⟩ := observedValue f.fr.units[i]? | throw "missing producer declaration"
  let ⟨some (.ok (.graph name pos r)),hp⟩ := observedValue f.plans[i]? | throw "missing ordinary producer graph"
  let ⟨identity⟩ ← producerNeed "producer graph and declaration disagree" (name = decl.name ∧ pos = decl.namePos)
  let ⟨stated⟩ ← producerNeed "producer body contract exceeds its declared effect" (declaredEffect r = true)
  let marked := decl.params.zipIdx.filterMap fun (param,slot) => if param.inferPreserves then some slot else none
  let ⟨some origins,ho⟩ := observedValue (CallbackOrigins.infer r.program (r.claims.map (·.context.length)).toArray r.start r.inputs.length)
    | throw "unsettled producer origins"
  match checked : writeInterface f i fuel dependencies with
  | .error why => throw why
  | .ok p =>
    let ⟨sites⟩ ← producerNeed "producer's framed invocation does not establish its declared fixed callback operands"
      (fixedCallsChecked r fuel origins marked p.interface = true)
    return ⟨p,by
      intro over
      obtain ⟨fn,plan,source,own,forwarded,header,inferred,_,publicName,publicPos,_,_,demands⟩ := writeInterface_accepted checked
      cases header.symm.trans hdecl
      obtain ⟨a,readOrigins⟩ := infer_accepted_origins inferred
      have ha : f.plans[i]? = some (.ok (.graph a.name a.position a.request)) := a.plan
      obtain ⟨nameEq,posEq,requestEq⟩ : a.name = name ∧ a.position = pos ∧ a.request = r := by simpa using ha.symm.trans hp
      subst r
      rw [readOrigins] at ho
      cases ho
      have typedCodes := inferCodes_assertions a.checkedCodes
      refine ⟨group,name,pos,a.request,hp,identity.1.trans publicName.symm,publicPos.trans (congrArg some identity.2.symm),?_,
        a.ordinary,a.synchronous,by simp [RegionalClause,a.regions],typedCodes,stated⟩
      intro η n W h L d I G entry refs values initial persist supply
      have sub : ∀ d ∈ own.demands, d ∈ p.interface.demands := fun d h => demands ▸ List.mem_eraseDups.mpr (List.mem_append_left _ h)
      have store := over.graph a.plan
      have graph : RequestJson.graph a.request.toRequest = StoreView.graph f.F.store := by
        change StoreView.graph a.request.types = _; rw [store]
      have entry' := entry
      dsimp only [G] at entry'
      rw [graph] at entry'
      have valid := a.checkedAtTypedPoints over (η := η) (I := I) entry' refs values initial persist (by
        rw [← graph]
        exact publicDemands_supply sub sites (a.framedGuarantee over).1 persist supply)
      have keep : KeepsOn (fun (_ : Unit) _ _ _ _ _ _ => True) (fun _ _ _ _ _ => ()) (fun _ _ _ => True) :=
        fun _ _ _ _ _ _ _ => ⟨fun _ _ => trivial,trivial⟩
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [G,graph] using SafeUnder.erase keep trivial valid.asserted
      · apply asserted_of_reach
        intro j h' t' room steps
        exact SafeUnder.reach keep trivial valid.asserted room steps
      · intro claimed
        have indexed : producerRunBound a.request = some (RunBound.ofRequest a.request.footprint a.request.onThrow a.request.fresh) := by
          rcases claimed with hf | ht | hf <;> simp_all [producerRunBound, bne_iff_ne]
        have bounded := ProgramTyping.SafePostExc.grow (b := h.length) (Nat.le_refl _) (valid.bounded _ _ _ indexed)
        rw [show G = reassign (StoreView.graph f.F.store) η by simp [G,graph]]
        apply HeapObservations.SafePostExc.weaken (fun _ _ hq => hq.1) _ bounded
        intro h' hq ht
        by_cases top : a.request.footprint = .top
        · rw [top]; exact Footprints.Closed.holds_top.mpr hq.2
        · have onThrow := hq.1
          simp only [ht,ite_true,BoundR] at onThrow
          exact onThrow top
      · intro nonempty
        dsimp only [G]
        rw [graph]
        exact (valid.ensured nonempty).post⟩
end Verification.SourceClaimJson.CallbackInterfaceCheck
