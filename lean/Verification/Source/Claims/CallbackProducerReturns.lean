import Verification.Source.Claims.PassUnitSafe
import Verification.Source.Claims.CallbackFramedPrefixes
import Verification.Source.Claims.CallbackCompletedSupply
namespace Verification.SourceClaimJson.CallbackInferencePlan
open ControlFlow CallbackOrigins CallbackPreservation Footprints TolerantFrames TolerantFrames.Reach
open HeapObservations GraphCode

/-- An obligation at a real marked invocation. Its producer entry value,
call operands, call-site roots and exact published demand travel together. -/
def SuppliedDemandsAt (Point : Nat → Env → IndexedHeap → Prop) (I : ∀ n, WorldT n → Prop) (P : Program) (table : Table) (privateRoots params : List Nat) (out : Interface)
    (start : Nat) (entry : Env) (h₀ : Heap) : Prop :=
  ∀ {fn br ba parameter state label node ρ} {ticks after value j} (s : IndexedHeap),
    let slots := table.at label
    I s.n s.W → Point label ρ s → Execution P j h₀ (.at start entry) s.h (.at label ρ) → P[label]? = some node →
    node.expression = .invoke (.var fn) br ba →
    (atCall slots privateRoots parameter state (.invoke (.var fn) br ba)).demand ∈ out.demands →
    parameter ∈ params → slots[fn]? = some [.input parameter] → entry parameter = ρ fn → RealizesRoots (entryRoot slots) ρ entry s.h →
    readCall (.invoke (.var fn) br ba) = true → (∀ i, isVal (ρ i) = true) → RootsOk s.W ρ →
    Steps ticks s.h (instantiate 0 ρ (.invoke (.var fn) br ba)) after value → ticks < s.n →
    isVal value = true → Supported (atCall slots privateRoots parameter state (.invoke (.var fn) br ba)).demand.support.normal entry s.h after

def SuppliedDemandsWith (I : ∀ n, WorldT n → Prop) (P : Program) (table : Table) (privateRoots params : List Nat) (out : Interface)
    (start : Nat) (entry : Env) (h₀ : Heap) : Prop :=
  ∀ {fn br ba parameter state label node ρ} {ticks after value j} (s : IndexedHeap),
    let slots := table.at label
    I s.n s.W → Execution P j h₀ (.at start entry) s.h (.at label ρ) → P[label]? = some node →
    node.expression = .invoke (.var fn) br ba →
    (atCall slots privateRoots parameter state (.invoke (.var fn) br ba)).demand ∈ out.demands →
    parameter ∈ params → entry parameter = ρ fn → RealizesRoots (entryRoot slots) ρ entry s.h →
    readCall (.invoke (.var fn) br ba) = true → (∀ i, isVal (ρ i) = true) → RootsOk s.W ρ →
    Steps ticks s.h (instantiate 0 ρ (.invoke (.var fn) br ba)) after value → ticks < s.n →
    isVal value = true → Supported (atCall slots privateRoots parameter state (.invoke (.var fn) br ba)).demand.support.normal entry s.h after

def SuppliedDemands (P : Program) (table : Table) (privateRoots params : List Nat) (out : Interface)
    (start : Nat) (entry : Env) (h₀ : Heap) : Prop :=
  ∀ {fn br ba parameter state label node ρ} {ticks after value j} (s : IndexedHeap),
    let slots := table.at label
    Execution P j h₀ (.at start entry) s.h (.at label ρ) → P[label]? = some node →
    node.expression = .invoke (.var fn) br ba →
    (atCall slots privateRoots parameter state (.invoke (.var fn) br ba)).demand ∈ out.demands →
    parameter ∈ params → entry parameter = ρ fn → RealizesRoots (entryRoot slots) ρ entry s.h →
    readCall (.invoke (.var fn) br ba) = true → (∀ i, isVal (ρ i) = true) → RootsOk s.W ρ →
    Steps ticks s.h (instantiate 0 ρ (.invoke (.var fn) br ba)) after value → ticks < s.n →
    isVal value = true → Supported (atCall slots privateRoots parameter state (.invoke (.var fn) br ba)).demand.support.normal entry s.h after

theorem rows_normalReturnsAt {Point : Nat → Env → IndexedHeap → Prop} {I : ∀ n, WorldT n → Prop} {P : Program} {table entry start h₀ inputs allowed proposed params}
    (rows : List (Row P.toArray table (certifiedPrivate P.toArray table proposed) params))
    (names : checkNames P.toArray allowed start inputs table = true)
    (source : P.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (supply : SuppliedDemandsAt Point I P table (certifiedPrivate P.toArray table proposed) params (publication rows) start entry h₀) :
    NormalReturnsAt Point I P table start entry h₀ (framedRet (framedSOf (framesOf rows))) := by
  intro label node ρ j ticks h' v s inherited point reached past vals roots atNode steps valRun room value
  cases selected : SinglePass.framedAt (framesOf rows) label with
  | none => simp [framedRet,framedSOf,selected]
  | some supports =>
    have got := selected
    unfold SinglePass.framedAt at got
    obtain ⟨pair,found,rfl⟩ := Option.map_eq_some_iff.mp got
    have atLabel := List.find?_some found
    obtain ⟨row,hr,rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
    simp only [beq_iff_eq] at atLabel
    subst label
    have getNode : P.toArray[row.label]! = node := by simp [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,atNode]
    obtain ⟨param,state,marked,candidate⟩ := row.source
    rw [getNode] at marked candidate
    have ready := row.prepared
    rw [getNode] at ready
    have invoked : ∃ fn br ba, node.expression = .invoke (.var fn) br ba ∧
        ∃ root, (table.at row.label)[fn]? = some [.input root] ∧ root ∈ params ∧ root = param := by
      unfold invocation at marked
      split at marked
      next fn br ba expression =>
        split at marked
        next root hit =>
          split at marked
          next contains => exact ⟨fn,br,ba,expression,root,hit,List.contains_iff_mem.mp contains,Option.some.inj marked⟩
          next => contradiction
        next => contradiction
      next => contradiction
    obtain ⟨fn,br,ba,inv,root,lookup,inParams,rfl⟩ := invoked
    have pp : ∀ i h st, i < j → Execution P i h₀ (.at start entry) h st → GraphMoment table h st :=
      fun i h st hi => past i hi h st
    have namesNow := (producerOrigins_reached names source values reached pp).2
    have eqInput {slot p} (hit : (table.at row.label)[slot]? = some [.input p]) : entry p = ρ slot :=
      (namesNow slot (.input p) (by simp [namedAt,hit])).1.2
    have realized : RealizesRoots (entryRoot (table.at row.label)) ρ entry s.h := by
      intro i p path hi
      unfold entryRoot at hi
      split at hi
      next j lookup => cases hi; simp [HeapKnowledge.readPath,eqInput lookup]
      next => contradiction
    have member : row.candidate.demand ∈ (publication rows).demands :=
      List.mem_eraseDups.mpr (List.mem_map.mpr ⟨row,hr,rfl⟩)
    rw [candidate,inv] at member
    simp only [framedRet,framedSOf,selected,Option.getD_some,candidate]
    apply atCall_supported realized (producerPrivate_supported names source values reached pp atNode inv valRun)
    rw [inv]
    exact supply s inherited point reached atNode inv member inParams lookup (eqInput lookup) realized (inv ▸ ready) vals roots (inv ▸ steps) room value

theorem rows_normalReturnsWith {I : ∀ n, WorldT n → Prop} {P : Program} {table entry start h₀ inputs allowed proposed params}
    (rows : List (Row P.toArray table (certifiedPrivate P.toArray table proposed) params))
    (names : checkNames P.toArray allowed start inputs table = true)
    (source : P.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (supply : SuppliedDemandsWith I P table (certifiedPrivate P.toArray table proposed) params (publication rows) start entry h₀) :
    NormalReturnsWith I P table start entry h₀ (framedRet (framedSOf (framesOf rows))) := by
  intro label node ρ j ticks after t s keep
  apply rows_normalReturnsAt (Point := fun _ _ _ => True) rows names source values _ s keep trivial
  intro fn br ba parameter state l nd env ticks after v j s slots keep _
  intro run loc inv member marked _
  exact supply s keep run loc inv member marked

theorem rows_normalReturns {P : Program} {table entry start h₀ inputs allowed proposed params}
    (rows : List (Row P.toArray table (certifiedPrivate P.toArray table proposed) params))
    (names : checkNames P.toArray allowed start inputs table = true)
    (source : P.all (fun node => ObjectCoherence.sourceTerm node.expression) = true)
    (values : ∀ i < inputs, isVal (entry i) = true)
    (supply : SuppliedDemands P table (certifiedPrivate P.toArray table proposed) params (publication rows) start entry h₀) :
    NormalReturns P table start entry h₀ (framedRet (framedSOf (framesOf rows))) := by
  intro label node ρ j ticks after t s
  apply rows_normalReturnsWith (I := fun _ _ => True) rows names source values _ s trivial
  intro fn br ba parameter state l nd env ticks after v j s slots keep
  exact supply s

/-- Ordinary safety of the exact accepted producer under its published
callback interface. Safety at framed returns and the typed graph prefixes
are supplied by the same ordinary run. -/
theorem AcceptedProducer.safeWith {I : ∀ n, WorldT n → Prop} {f i fuel params out} (a : AcceptedProducer f i fuel params out)
    (over : PassUnit.OverStore f) {L d h n} {W : WorldT n} {η}
    (entry : TolerantFrames.Target.EntryHolds (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η)
      a.request.inputs a.request.entrySeparation a.request.entryIndices (envOf L d) n W h)
    (roots : RootsOk W (envOf L d)) (vals : ∀ i, isVal (envOf L d i) = true)
    (initial : I n W)
    (persist : ∀ {k} {U : WorldT (k+1)} {V : WorldT k}, I (k+1) U → WExt (trunc k (Nat.le_succ _) U) V → I k V)
    (supplied : SuppliedDemandsWith I a.request.program a.origins
      (certifiedPrivate a.request.program.toArray a.origins (privateAllocations a.request.program a.origins))
      params out a.request.start (envOf L d) h) :
    SafePostExcW (PositiveRules.excOf (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η))
      (ControlFlow.GoalHolds (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η) a.request.goal
        (a.request.goal.argument (envOf L d))) (fun _ _ _ _ => True) (fun _ _ _ => True) n W h
      (PassUnit.gotoOf a.request.program a.request.start L d a.request.comp) := by
  obtain ⟨source,guarantee⟩ := a.framedGuarantee over
  obtain ⟨name,pos,request,plan,ordinary,sync,reg,codes,known,before,checked,origins,names,nodes,rfl,rows,rfl,after,replayed,sums⟩ := a
  have term := guarantee.safe _ _ (SourceElaboration.program_nodes _) η trivial n W h L d request.comp entry (PassUnit.gotoOf_refsOk (start := request.start) (comp := request.comp) source roots)
  apply safe_of_normalReturnsWith (table := origins) initial persist _ vals entry.2.2.2.1 entry.2.2.2.2 term
  rw [SourceElaboration.program_nodes]
  exact rows_normalReturnsWith rows names source (fun i _ => vals i) supplied

theorem AcceptedProducer.safe {f i fuel params out} (a : AcceptedProducer f i fuel params out)
    (over : PassUnit.OverStore f) {L d h n} {W : WorldT n} {η}
    (entry : TolerantFrames.Target.EntryHolds (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η)
      a.request.inputs a.request.entrySeparation a.request.entryIndices (envOf L d) n W h)
    (roots : RootsOk W (envOf L d)) (vals : ∀ i, isVal (envOf L d i) = true)
    (supplied : SuppliedDemands a.request.program a.origins
      (certifiedPrivate a.request.program.toArray a.origins (privateAllocations a.request.program a.origins))
      params out a.request.start (envOf L d) h) :
    SafePostExcW (PositiveRules.excOf (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η))
      (ControlFlow.GoalHolds (PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η) a.request.goal
        (a.request.goal.argument (envOf L d))) (fun _ _ _ _ => True) (fun _ _ _ => True) n W h
      (PassUnit.gotoOf a.request.program a.request.start L d a.request.comp) := by
  refine a.safeWith (I := fun _ _ => True) over entry roots vals trivial (fun _ _ => trivial) ?_
  intro fn br ba parameter state l nd env ticks after v j s slots keep
  exact supplied s

end Verification.SourceClaimJson.CallbackInferencePlan
