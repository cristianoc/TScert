import Verification.Source.Claims.CallbackTypicalCollector
namespace Verification.SourceClaimJson.CallbackInterfaceCheck
open CallArguments ControlFlow GraphCode ProgramTyping PositiveGraphs PositiveRules HeapObservations
open CallbackOrigins CallbackInferencePlan TolerantFrames PassUnit LabelStore

private inductive SameHeap (h : Heap) : Tm → Tm → Prop
  | refl : SameHeap h t t
  | next : Step h t h u → SameHeap h u v → SameHeap h t v

private theorem SameHeap.admin {h t v n} {W : WorldT n} (run : SameHeap h t v)
    (heap : HeapOk n W h) (refs : RefsOk W t) : AdminPrefix W h t v := by
  induction run with
  | refl => exact .refl
  | next st _ ih => exact .next refs st (ih (Kinds.step_refs st (by simpa using heap.1.1) heap.2 refs))

private theorem collectorTail {E K label ret mapping mapping₂ comp slot locals d h v}
    (middle : E[label]? = some (.nul : Tm)) (middleCont : K[label]? = some (.effect ⟨ret,some (0::mapping₂)⟩,none))
    (endExpr : E[ret]? = some (.var 0 : Tm)) (endCont : K[ret]? = some (.ret,none))
    (value : isVal v = true) (stored : isVal (envOf locals d slot) = true) :
    SameHeap h (.frame E K v locals d (.bind ⟨label,some ((slot+1)::mapping)⟩) none comp) (envOf locals d slot) := by
  let saved := envOf locals d slot
  let L₁ := saved :: mapping.map ((v::locals).getD · d)
  let L₂ := saved :: mapping₂.map (L₁.getD · v)
  have push : envMap (some ((slot+1)::mapping)) (v::locals) d = (L₁,v) := rfl
  have keep : envMap (some (0::mapping₂)) L₁ v = (L₂,saved) := rfl
  have bind : Step h (.frame E K v locals d (.bind ⟨label,some ((slot+1)::mapping)⟩) none comp) h (.goto E K label L₁ v comp) := by
    simpa [push] using Step.frameBind (h := h) (E := E) (K := K) (v := v)
      (L := locals) (d := d) (l := ⟨label,some ((slot+1)::mapping)⟩) (x := none) (comp := comp) value
  have enter : Step h (.goto E K label L₁ v comp) h (.frame E K .nul L₁ v (.effect ⟨ret,some (0::mapping₂)⟩) none comp) := by
    simpa [instantiate] using Step.gotoEnter (h := h) (L := L₁) (d := v) (comp := comp) middle middleCont
  have skip : Step h (.frame E K .nul L₁ v (.effect ⟨ret,some (0::mapping₂)⟩) none comp) h (.goto E K ret L₂ saved comp) := by
    simpa [keep] using Step.frameEffect (h := h) (E := E) (K := K) (v := .nul)
      (L := L₁) (d := v) (l := ⟨ret,some (0::mapping₂)⟩) (x := none) (comp := comp) rfl
  have last : Step h (.goto E K ret L₂ saved comp) h (.frame E K saved L₂ saved .ret none comp) := by
    simpa [envOf,L₂,instantiate] using Step.gotoEnter (h := h) (L := L₂) (d := saved) (comp := comp) endExpr endCont
  exact .next bind (.next enter (.next skip (.next last (.next (.frameRet stored) .refl))))

private theorem frameRefs {n} {W : WorldT n} {E K l L d comp c t}
    (outer : RefsOk W (.goto E K l L d comp)) (inner : RefsOk W t) : RefsOk W (.frame E K t L d c none comp) := by
  intro loc item
  simp only [refs,List.mem_append] at item
  rcases item with ((expr | here) | localRef) | defaultRef
  · exact outer loc (by simp only [refs,List.mem_append]; exact .inl (.inl expr))
  · exact inner loc here
  · exact outer loc (by simp only [refs,List.mem_append]; exact .inl (.inr localRef))
  · exact outer loc (by simp [refs,defaultRef])

theorem returnSaved_safe {Ξ T S : Fam} (excAdm : Adm Ξ) (resultAdm : Adm S)
    {E K label ret mapping mapping₂ comp slot locals d}
    (middle : E[label]? = some (.nul : Tm)) (middleCont : K[label]? = some (.effect ⟨ret,some (0::mapping₂)⟩,none))
    (endExpr : E[ret]? = some (.var 0 : Tm)) (endCont : K[ret]? = some (.ret,none))
    {h n} {W : WorldT n} (adm : WorldAdm W) (heap : HeapOk n W h)
    (saved : S n W (envOf locals d slot)) (valid : isVal (envOf locals d slot) = true)
    (storedRefs : RefsOk W (envOf locals d slot)) (outer : RefsOk W (.goto E K label locals d comp)) {t}
    (run : SafePostExc Ξ T (fun _ _ => True) (fun _ => True) n W h t) :
    SafePostExc Ξ S (fun _ _ => True) (fun _ => True) n W h
      (.frame E K t locals d (.bind ⟨label,some ((slot+1)::mapping)⟩) none comp) := by
  induction n generalizing t h with
  | zero => exact frameRefs outer run
  | succ n ih =>
    have refs := frameRefs (c := .bind ⟨label,some ((slot+1)::mapping)⟩) outer run.1
    rcases run.2 with (⟨hv,_,_⟩ | ⟨⟨ex,throws,scope,mem⟩,_⟩) | ⟨V,h',u,ext,world,step,ok,more⟩
    · have tail := collectorTail (h := h) (comp := comp) (mapping := mapping) middle middleCont endExpr endCont hv valid
      apply (tail.admin heap refs).safe adm heap
      intro j le
      exact SafePostExc.value valid (resultAdm.down_le _ _ le W _ saved) trivial (RefsOk_trunc le storedRefs)
    · have refExc := RefsOk_trunc (Nat.le_succ n) (run.1.sub (Kinds.raises_refs throws))
      refine ⟨refs,.inr ⟨_,h,.throw ex,WExt_refl _,WorldAdm_trunc _ adm,.frameRaise throws,
        HeapOk_trunc n W h heap,?_⟩⟩
      cases n with
      | zero => exact refExc
      | succ m => exact ⟨refExc,.inl (.inr ⟨⟨ex,.throwV (raises_val throws) (raises_sourceVal throws),
          scope,excAdm.down _ W _ mem⟩,trivial⟩)⟩
    · exact ⟨refs,.inr ⟨V,h',(Tm.frame E K u locals d (.bind ⟨label,some ((slot+1)::mapping)⟩) none comp),ext,world,
        .frameC step,ok,ih world ok (resultAdm.mono _ _ _ ext _ (resultAdm.down _ W _ saved))
          (RefsOk_mono ext (RefsOk_trunc _ storedRefs)) (RefsOk_mono ext (RefsOk_trunc _ outer)) more⟩⟩

theorem TypicalPair.collectorReturn {f caller producer fuel p forwarded}
    (pair : TypicalPair f caller producer fuel p forwarded) (over : PassUnit.OverStore f)
    {callerEntry k h₀ label h L d x cb fn input} {node : Node}
    (callerValues : ∀ i < pair.callerRun.request.inputs.length, isVal (callerEntry i) = true)
    {n₀} {W₀ : WorldT n₀} (callerRoots : RootsOk W₀ callerEntry) (callerHeap : HeapOk n₀ W₀ h₀)
    (reached : Execution pair.callerRun.request.program k h₀ (.at pair.callerRun.request.start callerEntry) h (.at label (envOf L d)))
    (loc : pair.callerRun.request.program[label]? = some node)
    (direct : node.expression = .invoke (.var fn) .undef [.var x,.var cb])
    (binding : originOf (pair.callerRun.origins.at label) (.var fn) = some (.input input))
    (selected : (knownSiblings pair.callerRun.request.inputs.length pair.callerRun.request.siblings [p]).find? (·.1 == input) = some (input,p))
    (abi : checkedCallFrame p .undef [.var x,.var cb] = [.var x,.var cb])
    (present : absentCallback pair.callerRun.request label [.var x,.var cb] 1 = false)
    (literal : CollectorLiteral pair.callerRun label cb)
    {captures fields oid} (linked : callerEntry input =
      nativeWalker pair.producerRun.request.program pair.producerRun.request.start pair.producerRun.request.comp captures fields oid)
    {slot mid ret mapping mapping₂ retTy}
    (cont : node.continuation = .bind ⟨mid,some ((slot+1)::mapping)⟩) (unhandled : node.handler = none)
    (middle : pair.callerRun.request.program[mid]? = some ⟨.nul,.effect ⟨ret,some (0::mapping₂)⟩,none⟩)
    (endNode : pair.callerRun.request.program[ret]? = some ⟨.var 0,.ret,none⟩)
    (savedSlot : literal.slotTypes[slot]?.join = some retTy)
    (source : pair.callerRun.request.program.all (fun nd => ObjectCoherence.sourceTerm nd.expression) = true)
     {n} {W : WorldT n} (heapClosed : ∀ v ∈ h, Scoped 0 v)
    (typed : PartialEnv (RequestJson.graph pair.callerRun.request.toRequest) literal.slotTypes (envOf L d) n W)
    (pointShape : ∀ l nd, pair.producerRun.request.program[l]? = some nd →
      ∀ slot br ba, nd.expression = .invoke (.var slot) br ba →
      (pair.producerRun.origins.at l)[slot]? = some [.input 1] →
      numericInvoke (StoreView.graph f.F.store) (((pair.producerRun.request.claims[l]?).map (·.context)).getD []) nd.expression = true) :
    RootsOk W (envOf L d) →
    let ρ := envOf L d
    let args := ρ x :: ρ cb :: (captures ++ [callerEntry input])
    let actual := envOf args .undef
    let G := StoreView.graph f.F.store
    TolerantFrames.Target.EntryHolds G pair.producerRun.request.inputs pair.producerRun.request.entrySeparation
      pair.producerRun.request.entryIndices actual n W h →
    RootsOk W actual → (∀ i, isVal (actual i) = true) →
    SafePostExc (excOf G) (meaning G retTy) (fun _ _ => True) (fun _ => True) n W h
      (gotoOf pair.callerRun.request.program label L d pair.callerRun.request.comp) := by
  intro callRoots ρ args actual G entry roots vals
  have store := over.graph pair.callerRun.plan
  change pair.callerRun.request.types = f.F.store at store
  have typedSaved := typed.2 slot retTy savedSlot
  change meaning (StoreView.graph pair.callerRun.request.types) retTy n W _ at typedSaved
  rw [store] at typedSaved
  have savedVal := (meaning_value typedSaved).1
  let P := pair.callerRun.request.program
  let E := P.map (·.expression)
  let K := P.map fun nd => (nd.continuation,nd.handler)
  let c := pair.callerRun.request.comp
  have find {i : Nat} {nd : Node} (found : P[i]? = some nd) : E[i]? = some nd.expression ∧ K[i]? = some (nd.continuation,nd.handler) := by
    simp [E,K,List.getElem?_map,found]
  obtain ⟨ce,ck⟩ := find loc
  obtain ⟨me,mk⟩ := find middle
  obtain ⟨ee,ek⟩ := find endNode
  rw [cont,unhandled] at ck
  have beginStep : Step h (gotoOf P label L d c) h
      (.frame E K (instantiate 0 ρ node.expression) L d (.bind ⟨mid,some ((slot+1)::mapping)⟩) none c) := .gotoEnter ce ck
  have outer := gotoOf_refsOk (start := label) (comp := c) source callRoots
  have chain : AdminPrefix W h (gotoOf P label L d c) _ := .next outer beginStep .refl
  apply chain.safe entry.2.2.2.1 entry.2.2.2.2
  intro j le
  have ent := entryAtLower entry le
  have rts := fun i => RefsOk_trunc le (roots i)
  apply returnSaved_safe (T := GoalHolds G pair.producerRun.request.goal (pair.producerRun.request.goal.argument actual))
    (PositiveGraphs.builtinExc_adm G _) (meaning_adm G retTy) me mk ee ek
    ent.2.2.2.1 ent.2.2.2.2 ((meaning_adm G _).down_le _ _ le W _ typedSaved) savedVal
    (RefsOk_trunc le (callRoots slot)) (RefsOk_trunc le outer)
  apply linkedWalker_native_safe (η := G.env) pair.callerRun pair.producerRun callerValues reached loc direct binding linked ent rts vals
  intro m small
  have em := entryAtLower ent small
  have tm := (typed.transfer _ le _ (WExt_refl _)).transfer _ small _ (WExt_refl _)
  apply TypicalPair.collectorBody pair over callerValues callerRoots callerHeap reached loc direct binding selected abi present
    literal heapClosed tm pointShape em (fun i => RefsOk_trunc small (rts i)) vals

end Verification.SourceClaimJson.CallbackInterfaceCheck
