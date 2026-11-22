import Verification.Source.Claims.LoweredModules
import Verification.Source.Claims.CallbackProducerVerdict
import Verification.Source.Claims.CallbackTypicalDispatch

namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open GraphCode CallbackInferencePlan CallArguments ControlFlow HeapObservations PassUnit TolerantFrames
open ProgramTyping PositiveGraphs PositiveRules Footprints

/-- The receiver-dropping prologue of a receiverless fixed source declaration.
Its descriptor includes the ordinary graph, the captured host bindings and self. -/
@[nospecialize] def sourceClosure {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι] (r : SourceElaboration.SourceRequest σ ι) (arity : Nat)
    (caps : List Tm) (fields : List (PropKey × Nat)) (oid : Nat) : Tm :=
  .objAt fields (.graph arity (realizedCode r).1 (realizedCode r).2 r.program.length caps .call false r.comp) oid

private theorem dropReceiver (xs : List Tm) :
    ((List.range xs.length).map (·+1)).map ((Tm.undef::xs).getD · .nul) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hx
    simp [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hx]

private theorem sourceEntry_prefix {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι] {r : SourceElaboration.SourceRequest σ ι} {arity cap fields oid args n}
    {W : WorldT n} {h : Heap} (width : arity + cap.length = r.inputs.length)
    (len : args.length = arity) (values : Values args) (heap : HeapOk n W h)
    (refs : RefsOk W (.invoke (sourceClosure r arity cap fields oid) .undef args)) :
    let self := sourceClosure r arity cap fields oid
    AdminPrefix W h (.invoke self .undef args)
      (.goto (realizedCode r).1 (realizedCode r).2 r.start (args ++ cap ++ [self]) .undef r.comp) := by
  intro self
  let L := args ++ cap ++ [self]
  let E := (realizedCode r).1
  let K := (realizedCode r).2
  let slots := (List.range (r.inputs.length+1)).map (·+1)
  let cont := Continuation.effect ⟨r.start,some slots⟩
  have normalized : parameters arity args = args := len ▸ parameters_exact args
  have enter : Step h (.invoke self .undef args) h (.goto E K r.program.length (.undef::L) .nul r.comp) := by
    apply CallArguments.call_step_iff.mpr
    apply Or.inr
    refine ⟨rfl,?_⟩
    simpa only [self,sourceClosure,graphEntry,normalized,L,List.cons_append,List.append_assoc,E,K] using
      (CallArguments.Invoke.graph (arity := arity) (E := E) (K := K) (start := r.program.length)
        (caps := cap) (kind := .call) (rest := false) (comp := r.comp) (fs := fields) (oid := oid)
        (r := .undef) rfl values rfl)
  have goto : Step h (.goto E K r.program.length (.undef::L) .nul r.comp) h (.frame E K .undef (.undef::L) .nul cont none r.comp) := by
    apply Step.gotoEnter (e := .undef) <;> simp [E,K,realizedCode,cont,slots]
  have lw : L.length = r.inputs.length+1 := by simp [L,len]; omega
  have mapped : envMap (some slots) (.undef::L) .nul = (L,.undef) := by
    change (slots.map ((Tm.undef::L).getD · .nul),Tm.undef) = _
    rw [show slots = (List.range L.length).map (·+1) by rw [lw]]
    rw [dropReceiver]
  have finish : Step h (.frame E K .undef (.undef::L) .nul cont none r.comp) h (.goto E K r.start L .undef r.comp) := by
    simpa only [cont,mapped] using Step.frameEffect (h := h) (E := E) (K := K) (v := .undef)
      (L := .undef::L) (d := .nul) (l := ⟨r.start,some slots⟩) (x := none) (comp := r.comp) rfl
  have next := Kinds.step_refs enter (by simpa using heap.1.1) heap.2 refs
  exact .next refs enter (.next next goto (.next (Kinds.step_refs goto (by simpa using heap.1.1) heap.2 next) finish .refl))

private theorem public_mem {n ρ ρ' h l} {r : Region} (named : publicRegion n r = true)
    (same : ∀ i < n, ρ i = ρ' i) : r.mem ρ h l = r.mem ρ' h l := by
  induction r <;> simp_all [publicRegion,Region.mem]

/-- A validated interface can see exactly its fixed parameter prefix.
Appending lexical captures or self leaves all of its obligations unchanged. -/
theorem publicDemands_prefix {ι : Type} {G : NormalGraph ι} {p : Published} {formals locals : List (Ty ι)}
    {args extra : List Tm} {I : ∀ n, WorldT n → Prop}
    (valid : p.validate = .ok p) (width : p.formals = formals.length) (len : args.length = formals.length)
    (supply : PublicDemandsWith I (formalDomain G formals) p.interface (envOf args .undef)) :
    PublicDemandsWith I (formalDomain G (formals ++ locals)) p.interface (envOf (args ++ extra) .undef) := by
  have admitted := (validated_demands valid).2
  have same : ∀ i < p.formals, envOf args .undef i = envOf (args ++ extra) .undef i := by
    intro i hi
    have pos : i < args.length := by omega
    simp [envOf,List.getD_eq_getElem?_getD,List.getElem?_append_left pos]
  intro d member s recv actuals keep domain rv av selfRefs rcRefs argRefs roots k after v run room value
  obtain ⟨inside,regions,paths⟩ := admitted d member
  have pf := same d.parameter inside
  have dom : formalDomain G formals d.parameter s recv actuals := by
    intro row atSlot
    apply domain row
    rw [List.getElem?_append_left (width ▸ inside)]
    exact atSlot
  have support := supply d member s recv actuals keep dom rv av (pf.symm ▸ selfRefs) rcRefs argRefs
    (fun i x path hit => by
      have pos := paths (some (x,path)) (List.mem_of_getElem? hit)
      simp at pos
      rw [same x pos]
      exact roots i x path hit) k after v (pf.symm ▸ run) room value
  intro e he l old inRegion before
  exact support e he l old ((public_mem (regions e (List.mem_append_left _ he)) same) ▸ inRegion) before


private theorem atSmallerIndex {I : ∀ n, WorldT n → Prop}
    (persist : ∀ {k} {U : WorldT (k+1)} {V : WorldT k}, I (k+1) U → WExt (trunc k (Nat.le_succ _) U) V → I k V)
    {m n W} (le : m ≤ n) (initial : I n W) : I m (trunc m le W) := by
  induction le with
  | refl => simpa only [trunc_id] using initial
  | step le ih =>
    simpa only [trunc_trunc] using ih (persist initial (WExt_refl _))

private theorem typedPrefix {ι : Type} {G : NormalGraph ι} {types : List (Ty ι)} {args : List Tm}
    {n W} (typed : ArgsT (types.map (meaning G)) n W args) :
    ∀ t ∈ args, isVal t = true ∧ Scoped 0 t := by
  intro t ht
  obtain ⟨i,hit⟩ := List.mem_iff_getElem?.mp ht
  have len : args.length = types.length := by simpa using ArgsT_length typed
  have hi := (List.getElem?_eq_some_iff.mp hit).1
  have small : i < types.length := by omega
  exact meaning_value (ArgsT_getElem? typed (by simp [small] : (types.map (meaning G))[i]? = some (meaning G types[i])) hit)

theorem producerClosure_conditionalCall {f : FilePlans} {r : Req f} {p : Published}
    {formals captures result vals fields oid} (body : ProducerBodySafe r p)
    (valid : p.validate = .ok p) (width : p.formals = formals.length)
    (layout : r.inputs = formals ++ captures) (capSize : vals.length = captures.length)
    (goal : r.goal = .plain result) (indexes : r.entryIndices = []) (separation : r.entrySeparation.facts = []) :
    let G := RequestJson.graph r.toRequest
    ConditionalCall G formals result p.interface (sourceClosure r formals.length vals fields oid)
      (fun n W => EnvOk G captures (envOf vals .undef) n W) := by
  intro G args n W h I persist hosts initial argTypes argRefs selfRefs world heap supply
  let self := sourceClosure r formals.length vals fields oid
  let L := args ++ vals ++ [self]
  have sizes : args.length = formals.length := by simpa using ArgsT_length argTypes
  have capsTyped : ArgsT (captures.map (meaning G)) n W vals := by
    apply ArgsT_of_getElem? (by simpa using capSize.symm)
    intro i A t cap ht
    rw [List.getElem?_map] at cap
    obtain ⟨B,hB,rfl⟩ := Option.map_eq_some_iff.mp cap
    simpa [envOf,List.getD_eq_getElem?_getD,ht] using hosts.2 i B hB
  have allTyped : ArgsT (r.inputs.map (meaning G)) n W (args ++ vals) := by
    simpa only [layout,List.map_append] using ArgsT_append argTypes capsTyped
  have capRefs : ∀ t ∈ vals, RefsOk W t := (graph_code_refs selfRefs).2
  have allRefs : RootsOk W (envOf L .undef) := by
    apply envOf_refs_of _ RefsOk_undef
    intro t ht
    rcases List.mem_append.mp ht with hp | hs
    · rcases List.mem_append.mp hp with ha | hc
      · exact (envOf_roots argRefs).1 t ha
      · exact capRefs t hc
    · exact List.mem_singleton.mp hs ▸ selfRefs
  have selfScoped : Scoped 0 self := (scopedArgs_iff ..).mpr (fun t mem => (typedPrefix capsTyped t mem).2)
  have allValues : ∀ i, isVal (envOf L .undef i) = true ∧ Scoped 0 (envOf L .undef i) := by
    intro i
    rcases getD_mem_or L i .undef with hm | hd
    · rcases List.mem_append.mp hm with hargs | hs
      · exact typedPrefix allTyped _ hargs
      · change isVal (L.getD i .undef) = true ∧ Scoped 0 (L.getD i .undef)
        rw [List.mem_singleton.mp hs]
        exact ⟨rfl,selfScoped⟩
    · change isVal (L.getD i .undef) = true ∧ Scoped 0 (L.getD i .undef)
      rw [hd]; exact ⟨rfl,trivial⟩
  have bodyEntry : Target.EntryHolds G r.inputs r.entrySeparation r.entryIndices (envOf L .undef) n W h := by
    refine ⟨⟨fun i => (allValues i).2,?_⟩,?_,?_,world,heap⟩
    · intro i A hit
      have bound := (List.getElem?_eq_some_iff.mp hit).1
      have actualSize : (args++vals).length = r.inputs.length := by simpa using ArgsT_length allTyped
      have fits : i < (args++vals).length := by omega
      have actual := ArgsT_getElem? allTyped (by simp [hit] : (r.inputs.map (meaning G))[i]? = some (meaning G A)) (List.getElem?_eq_getElem fits)
      simpa only [L,envOf,List.getD_eq_getElem?_getD,List.getElem?_append_left fits,List.getElem?_eq_getElem fits,Option.getD_some] using actual
    · intro fact member; rw [separation] at member; contradiction
    · simp [indexes,HeapKnowledge.IndexHolds]
  have nargs : formals.length + vals.length = r.inputs.length := by simp [layout,capSize]
  have prologue := sourceEntry_prefix (r := r) (h := h) nargs sizes (fun t ht => (typedPrefix argTypes t ht).1)
    heap (RefsOk_invoke.mpr ⟨selfRefs,RefsOk_undef,(envOf_roots argRefs).1⟩)
  apply prologue.safe world heap
  intro k le
  apply safePostExc_goto_append (Q := fun _ _ => True) (R := fun _ => True) (fun e he => by
    simp only [List.mem_singleton] at he; cases he; exact RefsOk_undef)
  have expanded : PublicDemandsWith I (formalDomain G r.inputs) p.interface (envOf L .undef) := by
    simpa only [L,List.append_assoc,layout] using
      (publicDemands_prefix (locals := captures) (extra := vals++[self]) valid width sizes supply)
  have ok := (body G.env k (trunc k le W) h L .undef I (entryAtLower bodyEntry le)
    (fun i => RefsOk_trunc le (allRefs i)) (fun i => (allValues i).1) (atSmallerIndex persist le initial) persist expanded).1
  simpa only [goal,ControlFlow.GoalHolds,show reassign (RequestJson.graph r.toRequest) G.env = G from rfl,L,self,gotoOf] using ok

end Verification.SourceClaimJson.CallbackInterfaceCheck
