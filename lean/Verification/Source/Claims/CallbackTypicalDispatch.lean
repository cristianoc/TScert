import Verification.Source.Claims.CallbackTypicalCursor
import Verification.Source.Claims.CallbackPublishedAcceptance
import Verification.Source.Claims.PassUnitRealize
namespace Verification.SourceClaimJson.CallbackInferencePlan
open ControlFlow GraphCode HeapObservations TolerantFrames Footprints PassUnit
open CallbackInterfaceCheck CallArguments CallbackOrigins

/-- A deterministic fixed-arity call's administrative reductions preserve
the heap. References in each intermediate term are valid at its source. -/
inductive AdminPrefix {n : Nat} (W : WorldT n) (h : Heap) : Tm → Tm → Prop
  | refl : AdminPrefix W h t t
  | next : RefsOk W t → Step h t h u → AdminPrefix W h u v → AdminPrefix W h t v

private theorem AdminPrefix.weaken {n m} {W : WorldT n} {h t u} (r : AdminPrefix W h t u)
    (le : m ≤ n) : AdminPrefix (trunc m le W) h t u := by
  induction r with
  | refl => exact .refl
  | next refs step _ ih => exact .next (RefsOk_trunc le refs) step ih

theorem AdminPrefix.safe {n : Nat} {W : WorldT n} {h t u} (r : AdminPrefix W h t u)
    (adm : WorldAdm W) (heap : HeapOk n W h) {Ξ T Q R}
    (body : ∀ k (le : k ≤ n), SafePostExcW Ξ T Q R k (trunc k le W) h u) :
    SafePostExcW Ξ T Q R n W h t := by
  induction n generalizing t with
  | zero =>
    cases r with
    | refl => exact (trunc_id (Nat.le_refl _) W) ▸ body 0 (Nat.le_refl _)
    | next refs _ _ => exact refs
  | succ n ih =>
    cases r with
    | refl => exact (trunc_id (Nat.le_refl _) W) ▸ body (n+1) (Nat.le_refl _)
    | next refs step tail =>
      let le := Nat.le_succ n
      exact ⟨refs,.inr ⟨trunc n le W,h,_,WExt_refl _,WorldAdm_trunc _ adm,step,
        HeapOk_trunc n W h heap,ih (tail.weaken le) (WorldAdm_trunc _ adm) (HeapOk_trunc n W h heap)
          (fun k hk => by simpa only [trunc_trunc] using body k (by omega))⟩⟩

private theorem dropSlots (xs : List Tm) (recv : Tm) :
    ((List.range xs.length).map (·+1)).map ((recv::xs).getD · .nul) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hx
    simp [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hx]

/-- Native closure for the ordinary receiverless two-argument source layout.
Its appended prologue drops the JavaScript receiver before the body. -/
def nativeWalker (P : Program) (start : Nat) (comp : ComponentTag)
    (captures : List Tm) (fields : List (PropKey × Nat)) (oid : Nat) : Tm :=
  let E := P.map (·.expression)
  let K := P.map fun node => (node.continuation,node.handler)
  .objAt fields (.graph 2 (E ++ [.undef])
    (K ++ [(.effect ⟨start,some ((List.range (2+captures.length+1)).map (·+1))⟩,none)])
    E.length captures .call false comp) oid

private theorem walkerPrefix {P start comp caps fields oid h x cb n} {W : WorldT n}
    (hx : isVal x = true) (hc : isVal cb = true)
    (valid : RefsOk W (.invoke (nativeWalker P start comp caps fields oid) .undef [x,cb])) :
    let self := nativeWalker P start comp caps fields oid
    let L := x :: cb :: (caps ++ [self])
    let E := P.map (·.expression) ++ [.undef]
    let slots := (List.range (2+caps.length+1)).map (·+1)
    let K := (P.map fun node => (node.continuation,node.handler)) ++ [(.effect ⟨start,some slots⟩,none)]
    AdminPrefix W h (.invoke self .undef [x,cb]) (.goto E K start L .undef comp) := by
  intro self L E slots K
  let proto := P.length
  let cont := Continuation.effect ⟨start,some slots⟩
  let locals := .undef :: L
  have enter : Step h (.invoke self .undef [x,cb]) h (.goto E K proto locals .nul comp) := by
    apply CallArguments.call_step_iff.mpr
    apply Or.inr
    refine ⟨rfl,?_⟩
    have vals : Values [x,cb] := by simp [Values,hx,hc]
    simpa [self,nativeWalker,E,K,proto,locals,L,slots,CallArguments.graphEntry,CallArguments.parameters] using
      (CallArguments.Invoke.graph (arity := 2) (E := E) (K := K) (start := proto)
        (caps := caps) (kind := .call) (rest := false) (comp := comp) (fs := fields) (oid := oid)
        (r := .undef) rfl vals rfl)
  have goto : Step h (.goto E K proto locals .nul comp) h (.frame E K .undef locals .nul cont none comp) := by
    apply Step.gotoEnter (e := .undef) <;> simp [proto,E,K,cont,slots]
  have len : L.length = 2+caps.length+1 := by simp [L]; omega
  have mapped : envMap (some slots) locals .nul = (L,.undef) := by
    change (slots.map ((Tm.undef::L).getD · .nul),Tm.undef) = _
    rw [show slots = (List.range L.length).map (·+1) by rw [len]]
    rw [dropSlots]
  have finish : Step h (.frame E K .undef locals .nul cont none comp) h (.goto E K start L .undef comp) := by
    simpa [cont,mapped] using Step.frameEffect (h := h) (E := E) (K := K) (v := .undef)
      (L := locals) (d := .nul) (l := ⟨start,some slots⟩) (x := none) (comp := comp) rfl
  have functions := RefsOk_invoke.mp valid
  have exprRefs : ∀ t ∈ E, RefsOk W t := by
    intro t ht loc hloc
    apply functions.1 loc
    simp only [nativeWalker,refs,refsArgs_eq,List.mem_append,List.mem_flatMap]
    grind
  have localRefs : ∀ t ∈ locals, RefsOk W t := by
    intro t ht loc hloc
    simp only [locals,L,List.mem_cons,List.mem_append] at ht
    rcases ht with rfl | rfl | rfl | hm | rfl | no
    · cases hloc
    · exact functions.2.2 _ (by simp) _ hloc
    · exact functions.2.2 _ (by simp) _ hloc
    · apply functions.1 loc
      simp only [nativeWalker,refs,refsArgs_eq,List.mem_append,List.mem_flatMap]
      grind
    · exact functions.1 loc hloc
    · contradiction
  have gotoRefs : RefsOk W (.goto E K proto locals .nul comp) := by
    intro loc hl
    simp only [refs,refsArgs_eq,List.mem_append,List.mem_flatMap] at hl
    rcases hl with (⟨t,ht,ht'⟩ | ⟨t,ht,ht'⟩) | hl
    · exact exprRefs _ ht _ ht'
    · exact localRefs _ ht _ ht'
    · cases hl
  have frameRefs : RefsOk W (.frame E K .undef locals .nul cont none comp) := by
    simpa [RefsOk,refs] using gotoRefs
  exact .next valid enter (.next gotoRefs goto (.next frameRefs finish .refl))


theorem heapAtLower {n k} {W : WorldT n} {h} (le : k ≤ n) (ok : HeapOk n W h) :
    HeapOk k (trunc k le W) h := by
  induction le with
  | refl => simpa only [trunc_id] using ok
  | step le ih => simpa only [trunc_trunc] using ih (HeapOk_trunc _ _ _ ok)

theorem entryAtLower {ι : Type} {G : PositiveGraphs.NormalGraph ι} {inputs sep idx ρ n}
    {W : WorldT n} {h} (entry : Target.EntryHolds G inputs sep idx ρ n W h) {k} (le : k ≤ n) :
    Target.EntryHolds G inputs sep idx ρ k (trunc k le W) h :=
  ⟨entry.1.transfer k le _ (WExt_refl _),entry.2.1,entry.2.2.1,
    WorldAdm_trunc _ entry.2.2.2.1,heapAtLower le entry.2.2.2.2⟩

/-- At the direct invocation in the reached caller, ordinary declaration
linkage names the actual same-file walker's closure. Its receiver-dropping
prologue is the one emitted for a fixed receiverless function. -/
theorem linkedWalker_native_safe {f caller producer fuel published forwarded own}
    (a : AcceptedCaller f caller fuel [published] [] forwarded)
    (b : AcceptedProducer f producer fuel [1] own)
    {callerEntry k before label ρ h x cb fn input} {node : Node}
    (callerValues : ∀ i < a.request.inputs.length, isVal (callerEntry i) = true)
    (reached : Execution a.request.program k before (.at a.request.start callerEntry) h (.at label ρ))
    (_atNode : a.request.program[label]? = some node)
    (direct : node.expression = .invoke (.var fn) .undef [.var x,.var cb])
    (binding : originOf (a.origins.at label) (.var fn) = some (.input input))
    {captures fields oid} (linked : callerEntry input =
      nativeWalker b.request.program b.request.start b.request.comp captures fields oid)
    {n} {W : WorldT n} {η} :
    let L := ρ x :: ρ cb :: (captures ++ [callerEntry input])
    let G := PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η
    Target.EntryHolds G b.request.inputs b.request.entrySeparation b.request.entryIndices (envOf L .undef) n W h →
    RootsOk W (envOf L .undef) → (∀ i, isVal (envOf L .undef i) = true) →
    (∀ k (le : k ≤ n), SafePostExc (PositiveRules.excOf G) (GoalHolds G b.request.goal (b.request.goal.argument (envOf L .undef)))
      (fun _ _ => True) (fun _ => True) k (trunc k le W) h (gotoOf b.request.program b.request.start L .undef b.request.comp)) →
    SafePostExc (PositiveRules.excOf G) (GoalHolds G b.request.goal (b.request.goal.argument (envOf L .undef)))
      (fun _ _ => True) (fun _ => True) n W h (instantiate 0 ρ node.expression) := by
  intro L G entry roots vals body
  obtain ⟨hist,valid,_,_,_,held⟩ := checkedNames_reached a.names callerValues reached
  obtain ⟨_,hvar,slot⟩ := namedOrigin_slot binding
  cases hvar
  have valueEq := (held fn (.input input) (by simp [namedAt,slot])).1.2
  have atCall : ρ fn = nativeWalker b.request.program b.request.start b.request.comp captures fields oid :=
    valueEq.symm.trans linked
  rw [direct]
  change SafePostExc _ _ _ _ _ _ _ (.invoke (ρ fn) .undef [ρ x,ρ cb])
  rw [atCall]
  have memRefs := (PassUnit.envOf_roots roots).1
  have fv : RefsOk W (nativeWalker b.request.program b.request.start b.request.comp captures fields oid) := by
    rw [← linked]
    exact memRefs _ (by simp [L])
  have xr : RefsOk W (ρ x) := memRefs _ (by simp [L])
  have cr : RefsOk W (ρ cb) := memRefs _ (by simp [L])
  have rr : RefsOk W (.invoke (nativeWalker b.request.program b.request.start b.request.comp captures fields oid)
      .undef [ρ x,ρ cb]) := RefsOk_invoke.mpr ⟨fv,RefsOk_undef,by simpa using And.intro xr cr⟩
  have prologue := walkerPrefix (h := h) (show isVal (ρ x) = true from vals 0)
    (show isVal (ρ cb) = true from vals 1) rr
  apply prologue.safe entry.2.2.2.1 entry.2.2.2.2
  intro m le
  apply safePostExc_goto_append (Q := fun _ _ => True) (R := fun _ => True)
    (fun e he => ?_)
  · rw [← linked]
    exact body m le
  · simp only [List.mem_singleton] at he
    cases he
    exact RefsOk_undef


theorem typicalEmpty_native_safe {f caller producer fuel published forwarded own}
    (a : AcceptedCaller f caller fuel [published] [] forwarded)
    (b : AcceptedProducer f producer fuel [1] own) (over : PassUnit.OverStore f)
    {callerEntry k before label ρ h x cb fn input} {node : Node}
    (callerValues : ∀ i < a.request.inputs.length, isVal (callerEntry i) = true)
    (reached : Execution a.request.program k before (.at a.request.start callerEntry) h (.at label ρ))
    (_atNode : a.request.program[label]? = some node)
    (direct : node.expression = .invoke (.var fn) .undef [.var x,.var cb])
    (binding : originOf (a.origins.at label) (.var fn) = some (.input input))
    (empty : emptyArgumentAt a.request.program a.origins label cb = true)
    {captures fields oid} (linked : callerEntry input =
      nativeWalker b.request.program b.request.start b.request.comp captures fields oid)
    {n} {W : WorldT n} {η} :
    let L := ρ x :: ρ cb :: (captures ++ [callerEntry input])
    let G := PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η
    Target.EntryHolds G b.request.inputs b.request.entrySeparation b.request.entryIndices (envOf L .undef) n W h →
    RootsOk W (envOf L .undef) → (∀ i, isVal (envOf L .undef i) = true) →
    SafePostExc (PositiveRules.excOf G) (GoalHolds G b.request.goal (b.request.goal.argument (envOf L .undef)))
      (fun _ _ => True) (fun _ => True) n W h (instantiate 0 ρ node.expression) := by
  intro L G entry roots vals
  apply linkedWalker_native_safe a b callerValues reached _atNode direct binding linked entry roots vals
  intro m le
  apply b.safe over (entryAtLower entry le) (fun i => RefsOk_trunc le (roots i)) vals
  apply emptySupplies
  intro i hi
  cases List.mem_singleton.mp hi
  change emptyCallback (ρ cb) = true
  exact emptyArgument_reached a.names callerValues reached empty

/-- Return a call's value directly from the caller. Source lowering binds
the call's result in slot zero before entering the return node. -/
theorem returnCall_safe {Ξ T : Fam} (exceptionAdm : Adm Ξ) (resultAdm : Adm T)
    {E K label mapping locals d comp} (returnExpr : E[label]? = some (.var 0 : Tm))
    (returnCont : K[label]? = some (.ret,none))
    {h n} {W : WorldT n} (adm : WorldAdm W) (heap : HeapOk n W h)
    (outer : RefsOk W (.goto E K label locals d comp)) {t}
    (run : SafePostExc Ξ T (fun _ _ => True) (fun _ => True) n W h t) :
    SafePostExc Ξ T (fun _ _ => True) (fun _ => True) n W h
      (.frame E K t locals d (.bind ⟨label,some (0::mapping)⟩) none comp) := by
  let cont : Continuation := .bind ⟨label,some (0::mapping)⟩
  change SafePostExc _ _ _ _ _ _ _ (.frame E K t locals d cont none comp)
  induction n generalizing t h with
  | zero =>
    intro loc hl
    simp only [refs,List.mem_append] at hl
    rcases hl with ((hE | hv) | hL) | hd
    · exact outer loc (by simp only [refs,List.mem_append]; exact .inl (.inl hE))
    · exact run loc hv
    · exact outer loc (by simp only [refs,List.mem_append]; exact .inl (.inr hL))
    · exact outer loc (by simp [refs,hd])
  | succ n ih =>
    obtain ⟨refsT,term⟩ := run
    have refFrame : RefsOk W (.frame E K t locals d cont none comp) := by
      intro loc hl
      simp only [refs,List.mem_append] at hl
      rcases hl with ((hE | hv) | hL) | hd
      · exact outer loc (by simp only [refs,List.mem_append]; exact .inl (.inl hE))
      · exact refsT loc hv
      · exact outer loc (by simp only [refs,List.mem_append]; exact .inl (.inr hL))
      · exact outer loc (by simp [refs,hd])
    rcases term with (⟨hv,ht,_⟩ | ⟨⟨ex,throws,scope,mem⟩,_⟩) | ⟨V,h',next,ext,world,step,typed,more⟩
    · let L' := t :: mapping.map ((t :: locals).getD · d)
      have remap : envMap (some (0::mapping)) (t::locals) d = (L',t) := rfl
      have bind : Step h (.frame E K t locals d cont none comp) h (.goto E K label L' t comp) := by
        simpa [cont,remap] using Step.frameBind (h := h) (E := E) (K := K)
          (L := locals) (d := d) (l := ⟨label,some (0::mapping)⟩) (x := none) (comp := comp) hv
      have enter : Step h (.goto E K label L' t comp) h (.frame E K t L' t .ret none comp) := by
        simpa [instantiate,L',envOf] using Step.gotoEnter (h := h) (L := L') (d := t)
          (comp := comp) returnExpr returnCont
      have nextRefs : RefsOk W (.goto E K label L' t comp) := by
        intro loc hl
        simp only [refs,refsArgs_eq,List.mem_flatMap,List.mem_append] at hl
        rcases hl with (⟨e,he,here⟩ | ⟨a,ha,here⟩) | hit
        · exact outer loc (by simp [refs,refsArgs_eq]; grind)
        · rcases List.mem_cons.mp ha with rfl | hm
          · exact refsT loc here
          · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
            rcases getD_mem_or (t::locals) i d with hlist | eq
            · rcases List.mem_cons.mp hlist with eq | hlist
              · exact refsT loc (eq ▸ here)
              · exact outer loc (by simp [refs,refsArgs_eq]; grind)
            · exact outer loc (by simp [refs,eq ▸ here])
        · exact refsT _ hit
      have finalRefs : RefsOk W (.frame E K t L' t .ret none comp) := by
        intro loc hl
        simp only [refs,List.mem_append] at hl
        rcases hl with ((hE | hv) | hL) | hd
        · exact nextRefs loc (by simp only [refs,List.mem_append]; exact .inl (.inl hE))
        · exact refsT loc hv
        · exact nextRefs loc (by simp only [refs,List.mem_append]; exact .inl (.inr hL))
        · exact refsT loc hd
      have chain : AdminPrefix W h (.frame E K t locals d cont none comp) t :=
        .next refFrame bind (.next nextRefs enter (.next finalRefs (.frameRet hv) .refl))
      exact chain.safe adm heap fun k le => SafePostExc.value hv
        (resultAdm.down_le _ _ le W t ht) trivial (RefsOk_trunc le refsT)
    · have refExc := RefsOk_trunc (Nat.le_succ n) (refsT.sub (Kinds.raises_refs throws))
      refine ⟨refFrame,.inr ⟨_,h,.throw ex,WExt_refl _,WorldAdm_trunc _ adm,.frameRaise throws,
        HeapOk_trunc n W h heap,?_⟩⟩
      cases n with
      | zero => exact refExc
      | succ m => exact ⟨refExc,.inl (.inr ⟨⟨ex,.throwV (raises_val throws) (raises_sourceVal throws),
          scope,exceptionAdm.down _ W _ mem⟩,trivial⟩)⟩
    · exact ⟨refFrame,.inr ⟨V,h',_,ext,world,.frameC step,typed,
        ih world typed (RefsOk_mono ext (RefsOk_trunc _ outer)) more⟩⟩


/-- The accepted producer and caller are from this single same-file
publication. The header identifies the ordinary two-parameter form and
a single marker on its second parameter. -/
structure TypicalPair (f : FilePlans) (caller producer fuel : Nat) (p : Published) (forwarded : List CallbackPreservation.Demand) where
  own : Interface
  callerRun : AcceptedCaller f caller fuel [p] [] forwarded
  producerRun : AcceptedProducer f producer fuel [1] own
  emitted : p.interface.demands = own.demands.eraseDups

theorem typicalPair_of_checks {f : FilePlans} {caller producer fuel p forwarded fn plan src}
    (publication : writeInterface f producer fuel [] = .ok p)
    (checked : check f caller fuel [p] [] = .ok forwarded)
    (header : f.fr.units[producer]? = some (fn,plan,src))
    (marker : (fn.params.zipIdx.filterMap fun (param,slot) =>
      if param.inferPreserves then some slot else none) = [1]) :
    Nonempty (TypicalPair f caller producer fuel p forwarded) := by
  obtain ⟨f',pl',s',own,fd,unit,inf,passes,_,_,_,_,out⟩ := writeInterface_accepted publication
  rw [header] at unit
  cases Option.some.inj unit
  rw [marker] at inf
  change Except.ok [] = Except.ok fd at passes
  cases passes
  obtain ⟨b⟩ := infer_accepted inf
  obtain ⟨a⟩ := check_accepted checked
  exact ⟨⟨own,a,b,by simpa using out⟩⟩

/-- From the reached caller call node through native producer entry,
the private-cursor walk, return of its number and the caller's own return.
The ordinary module linkage and the two source frames carry all runtime
data. The checker supplies the callback obligation internally. -/
theorem TypicalPair.safeReturn {f caller producer fuel p forwarded}
    (pair : TypicalPair f caller producer fuel p forwarded) (over : PassUnit.OverStore f)
    {callerEntry k before label h L d x cb fn input} {node : Node}
    (callerValues : ∀ i < pair.callerRun.request.inputs.length, isVal (callerEntry i) = true)
    (reached : Execution pair.callerRun.request.program k before (.at pair.callerRun.request.start callerEntry)
      h (.at label (envOf L d)))
    (atNode : pair.callerRun.request.program[label]? = some node)
    (direct : node.expression = .invoke (.var fn) .undef [.var x,.var cb])
    (binding : originOf (pair.callerRun.origins.at label) (.var fn) = some (.input input))
    (empty : emptyArgumentAt pair.callerRun.request.program pair.callerRun.origins label cb = true)
    {ret mapping} (cont : node.continuation = .bind ⟨ret,some (0::mapping)⟩) (unhandled : node.handler = none)
    (next : pair.callerRun.request.program[ret]? = some ⟨.var 0,.ret,none⟩)
    {captures fields oid} (linked : callerEntry input =
      nativeWalker pair.producerRun.request.program pair.producerRun.request.start pair.producerRun.request.comp captures fields oid)
    {n} {W : WorldT n} {η} {retTy} (plain : pair.producerRun.request.goal = .plain retTy)
    (source : pair.callerRun.request.program.all (fun nd => ObjectCoherence.sourceTerm nd.expression) = true)
    (callerRoots : RootsOk W (envOf L d)) :
    let ρ := envOf L d
    let args := ρ x :: ρ cb :: (captures ++ [callerEntry input])
    let G := PositiveRules.reassign (LabelStore.StoreView.graph f.F.store) η
    Target.EntryHolds G pair.producerRun.request.inputs pair.producerRun.request.entrySeparation
      pair.producerRun.request.entryIndices (envOf args .undef) n W h →
    RootsOk W (envOf args .undef) → (∀ i, isVal (envOf args .undef i) = true) →
    SafePostExc (PositiveRules.excOf G) (PositiveRules.meaning G retTy) (fun _ _ => True) (fun _ => True)
      n W h (gotoOf pair.callerRun.request.program label L d pair.callerRun.request.comp) := by
  intro ρ args G entry roots vals
  let P := pair.callerRun.request.program
  let E := P.map (·.expression)
  let K := P.map fun nd => (nd.continuation,nd.handler)
  let c := pair.callerRun.request.comp
  have find {i : Nat} {nd : Node} (found : P[i]? = some nd) : E[i]? = some nd.expression ∧ K[i]? = some (nd.continuation,nd.handler) := by
    simp [E,K,List.getElem?_map,found]
  obtain ⟨callExpr,callCont⟩ := find atNode
  obtain ⟨retExpr,retCont⟩ := find next
  rw [cont,unhandled] at callCont
  have initial : Step h (gotoOf P label L d c) h
      (.frame E K (instantiate 0 ρ node.expression) L d (.bind ⟨ret,some (0::mapping)⟩) none c) :=
    .gotoEnter callExpr callCont
  have outer := gotoOf_refsOk (start := label) (comp := c) source callerRoots
  have chain : AdminPrefix W h (gotoOf P label L d c) _ := .next outer initial .refl
  apply chain.safe entry.2.2.2.1 entry.2.2.2.2
  intro j le
  have ent := entryAtLower entry le
  have call := typicalEmpty_native_safe pair.callerRun pair.producerRun over callerValues reached atNode direct
    binding empty linked ent (fun i => RefsOk_trunc le (roots i)) vals
  rw [plain] at call
  apply returnCall_safe (PositiveGraphs.builtinExc_adm G _) (ProgramTyping.meaning_adm G _)
    retExpr retCont ent.2.2.2.1 ent.2.2.2.2 (RefsOk_trunc le outer) call

end Verification.SourceClaimJson.CallbackInferencePlan
