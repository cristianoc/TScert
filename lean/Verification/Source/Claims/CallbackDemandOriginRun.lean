import Verification.Source.Claims.CallbackDemandOriginSound

/-! # Soundness of the slot-origin table over a whole run

`originsValid_sound`: when the table `originsValid` checks for a graph `P`
holds of the entry environment and heap, it holds at every node the graph
machine reaches from the entry: at `.at l ρ` on heap `h`, the table has an
entry `env` for `l` and every slot of `ρ` meets its origin in `env` in `h`
(`EnvOriginHolds`). `requestOrigins_sound` and `closureOrigins_sound` state
it for a request's program and for a closure code's, at the origins the
checks compute for them.

A node's step keeps every origin when its expression changes no existing
storage (`isReadOnlyOrAlloc`): its steps extend the heap as a prefix, along
which every path read and every miss stays (`readPath_prefix`,
`pathMiss_prefix`). Any other step keeps the origins that name a value
independently of the heap (`SlotOrigin.dropHeap`, `originValueHolds_dropHeap`).
The result's origin (`exprOrigin`) holds of the value a node's expression
returns (`exprOrigin_sound`, `exprOrigin_dropHeap_sound`), by the expression's
run: a `let` runs its bound term, then its body at the value
(`steps_letE`); an allocation returns an object at fresh locations
(`steps_makeAt`, `steps_arrLit`); a read of a named field reads the object's
own field, or misses it (`steps_readAt`). -/

namespace Verification.SourceClaimJson
open Lean Verification ControlFlow ProgramTyping PositiveGraphs PositiveRules LabelStore
open HeapObservations CallbackDemands

/-! ## Origins degraded across a step that may write -/

theorem SlotOrigin.dropHeapList_eq_map : ∀ os : List SlotOrigin,
    SlotOrigin.dropHeapList os = os.map SlotOrigin.dropHeap
  | [] => by simp [SlotOrigin.dropHeapList]
  | o :: os => by simp [SlotOrigin.dropHeapList, SlotOrigin.dropHeapList_eq_map os]

theorem getD_map_dropHeap (os : List SlotOrigin) (i : Nat) :
    (os.map SlotOrigin.dropHeap).getD i .unknown = (os.getD i .unknown).dropHeap := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases os[i]? <;> simp [SlotOrigin.dropHeap]

theorem originAt_map_dropHeap (env : List SlotOrigin) (s : Nat) :
    originAt (env.map SlotOrigin.dropHeap) s = (originAt env s).dropHeap :=
  getD_map_dropHeap env s

section
variable {ι : Type} {codes : List (RequestJson.CodeRequest ι)} {ρ₀ : Env} {sibVal : String → Tm}
  {bOwn bCaller : Nat}

theorem originValueHolds_unknown_any {h : Heap} {v : Tm} :
    OriginValueHolds codes ρ₀ sibVal bOwn bCaller h .unknown v := by
  rw [OriginValueHolds]; trivial

theorem originValueHolds_prim_any {h : Heap} {v : Tm} :
    OriginValueHolds codes ρ₀ sibVal bOwn bCaller h .prim v := by
  rw [OriginValueHolds]; trivial

/-- **Holding transfers along any relation of heaps that keeps paths**: an
origin's meaning reads the heap only through its paths. -/
theorem originValueHolds_transfer {h h' : Heap}
    (hpath : ∀ (base : Val) (fs : List String) (v : Tm),
      (HeapKnowledge.readPath h base fs = some v ∨ PathMiss h base fs) →
        (HeapKnowledge.readPath h' base fs = some v ∨ PathMiss h' base fs)) :
    ∀ (o : SlotOrigin) (v : Tm), OriginValueHolds codes ρ₀ sibVal bOwn bCaller h o v →
      OriginValueHolds codes ρ₀ sibVal bOwn bCaller h' o v
  | .path p fs, v, ho => by
    rw [OriginValueHolds] at ho ⊢; exact hpath _ _ _ ho
  | .closure ci caps, v, ho => by
    rw [OriginValueHolds] at ho ⊢
    obtain ⟨q, fs, ar, E, K, s, capVals, kind, rest, comp, oid, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ho
    exact ⟨q, fs, ar, E, K, s, capVals, kind, rest, comp, oid, h1, h2, h3, h4, h5, h6, h7, fun i hi =>
      originValueHolds_transfer hpath (caps.getD i .unknown) (capVals.getD i .nul) (h8 i hi)⟩
  | .param _, _, ho | .fresh _, _, ho | .callerFresh _, _, ho | .sibling _, _, ho | .prim, _, ho
  | .unknown, _, ho => by rw [OriginValueHolds] at ho ⊢; exact ho
termination_by o => sizeOf o
decreasing_by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have := List.sizeOf_lt_of_mem (List.getElem_mem hi)
  simp only [SlotOrigin.closure.sizeOf_spec]
  omega

/-- **A degraded origin holds in every heap where its origin held in one.** -/
theorem originValueHolds_dropHeap {h h' : Heap} :
    ∀ (o : SlotOrigin) (v : Tm), OriginValueHolds codes ρ₀ sibVal bOwn bCaller h o v →
      OriginValueHolds codes ρ₀ sibVal bOwn bCaller h' o.dropHeap v
  | .path _ _, _, _ => by rw [SlotOrigin.dropHeap]; exact originValueHolds_unknown_any
  | .closure ci caps, v, ho => by
    rw [SlotOrigin.dropHeap, SlotOrigin.dropHeapList_eq_map]
    rw [OriginValueHolds] at ho ⊢
    obtain ⟨q, fs, ar, E, K, s, capVals, kind, rest, comp, oid, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ho
    refine ⟨q, fs, ar, E, K, s, capVals, kind, rest, comp, oid, h1, h2, h3, h4, h5, h6,
      by simpa using h7, fun i hi => ?_⟩
    have hi' : i < caps.length := by simpa using hi
    rw [getD_map_dropHeap]
    exact originValueHolds_dropHeap (caps.getD i .unknown) (capVals.getD i .nul) (h8 i hi')
  | .param _, _, ho | .fresh _, _, ho | .callerFresh _, _, ho | .sibling _, _, ho | .prim, _, ho
  | .unknown, _, ho => by rw [SlotOrigin.dropHeap]; rw [OriginValueHolds] at ho ⊢; exact ho
termination_by o => sizeOf o
decreasing_by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  have := List.sizeOf_lt_of_mem (List.getElem_mem hi')
  simp only [SlotOrigin.closure.sizeOf_spec]
  omega

/-- **A degraded origin's meaning reads no heap.** -/
theorem originValueHolds_dropHeap_any {h h' : Heap} :
    ∀ (o : SlotOrigin) (v : Tm), OriginValueHolds codes ρ₀ sibVal bOwn bCaller h o.dropHeap v →
      OriginValueHolds codes ρ₀ sibVal bOwn bCaller h' o.dropHeap v
  | .path _ _, _, _ => by rw [SlotOrigin.dropHeap]; exact originValueHolds_unknown_any
  | .closure ci caps, v, ho => by
    rw [SlotOrigin.dropHeap, SlotOrigin.dropHeapList_eq_map] at ho ⊢
    rw [OriginValueHolds] at ho ⊢
    obtain ⟨q, fs, ar, E, K, s, capVals, kind, rest, comp, oid, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ho
    refine ⟨q, fs, ar, E, K, s, capVals, kind, rest, comp, oid, h1, h2, h3, h4, h5, h6, h7, fun i hi => ?_⟩
    have hi' : i < caps.length := by simpa using hi
    have := h8 i hi
    rw [getD_map_dropHeap] at this ⊢
    exact originValueHolds_dropHeap_any (caps.getD i .unknown) (capVals.getD i .nul) this
  | .param _, _, ho | .fresh _, _, ho | .callerFresh _, _, ho | .sibling _, _, ho | .prim, _, ho
  | .unknown, _, ho => by rw [SlotOrigin.dropHeap] at ho ⊢; rw [OriginValueHolds] at ho ⊢; exact ho
termination_by o => sizeOf o
decreasing_by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  have := List.sizeOf_lt_of_mem (List.getElem_mem hi')
  simp only [SlotOrigin.closure.sizeOf_spec]
  omega

end

/-! ## Paths along a growing heap -/

theorem prefix_getElem? {h h' : Heap} (hp : h.IsPrefix h') {l : Nat} {v : Val} (hv : h[l]? = some v) :
    h'[l]? = some v := by
  obtain ⟨t, rfl⟩ := hp
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]
  exact hv

theorem readPath_prefix {h h' : Heap} (hp : h.IsPrefix h') :
    ∀ (v : Val) (fs : List String) (w : Val), HeapKnowledge.readPath h v fs = some w →
      HeapKnowledge.readPath h' v fs = some w
  | _, [], _, hr => hr
  | .objAt fs' c oid, f :: p, w, hr => by
    simp only [HeapKnowledge.readPath] at hr ⊢
    cases hlu : fs'.lookup (.str f) with
    | none => simp [hlu] at hr
    | some l =>
      simp only [hlu] at hr ⊢
      cases hget : h[l]? with
      | none => simp [hget] at hr
      | some u =>
        simp only [hget] at hr
        simp only [prefix_getElem? hp hget]
        exact readPath_prefix hp u p w hr
  | .nul, _ :: _, _, hr | .undef, _ :: _, _, hr | .tru, _ :: _, _, hr | .fls, _ :: _, _, hr
  | .num _, _ :: _, _, hr | .str _, _ :: _, _, hr | .bigint _, _ :: _, _, hr | .sym _, _ :: _, _, hr
  | .arr _, _ :: _, _, hr | .viewSpine .., _ :: _, _, hr | .var _, _ :: _, _, hr
  | .invoke .., _ :: _, _, hr | .construct .., _ :: _, _, hr | .letE .., _ :: _, _, hr
  | .makeAt .., _ :: _, _, hr | .readAt .., _ :: _, _, hr | .indexAt .., _ :: _, _, hr
  | .writeAt .., _ :: _, _, hr | .test .., _ :: _, _, hr | .ite .., _ :: _, _, hr
  | .arith .., _ :: _, _, hr | .arrLit _, _ :: _, _, hr | .elemAt .., _ :: _, _, hr
  | .setElem .., _ :: _, _, hr | .lenOf _, _ :: _, _, hr | .spread _, _ :: _, _, hr
  | .throw _, _ :: _, _, hr | .merge .., _ :: _, _, hr | .makeKey .., _ :: _, _, hr
  | .goto .., _ :: _, _, hr | .frame .., _ :: _, _, hr => by simp [HeapKnowledge.readPath] at hr

theorem pathMiss_prefix {h h' : Heap} (hp : h.IsPrefix h') :
    ∀ (v : Val) (fs : List String), PathMiss h v fs → PathMiss h' v fs
  | _, [], hm => by simp [PathMiss] at hm
  | .objAt fs' c oid, f :: p, hm => by
    simp only [PathMiss] at hm ⊢
    cases hlu : fs'.lookup (.str f) with
    | none => simp
    | some l =>
      simp only [hlu] at hm ⊢
      cases hget : h[l]? with
      | none => simp [hget] at hm
      | some u =>
        simp only [hget] at hm
        simp only [prefix_getElem? hp hget]
        exact pathMiss_prefix hp u p hm
  | .nul, _ :: _, hm | .undef, _ :: _, hm | .tru, _ :: _, hm | .fls, _ :: _, hm
  | .num _, _ :: _, hm | .str _, _ :: _, hm | .bigint _, _ :: _, hm | .sym _, _ :: _, hm
  | .arr _, _ :: _, hm | .viewSpine .., _ :: _, hm | .var _, _ :: _, hm
  | .invoke .., _ :: _, hm | .construct .., _ :: _, hm | .letE .., _ :: _, hm
  | .makeAt .., _ :: _, hm | .readAt .., _ :: _, hm | .indexAt .., _ :: _, hm
  | .writeAt .., _ :: _, hm | .test .., _ :: _, hm | .ite .., _ :: _, hm
  | .arith .., _ :: _, hm | .arrLit _, _ :: _, hm | .elemAt .., _ :: _, hm
  | .setElem .., _ :: _, hm | .lenOf _, _ :: _, hm | .spread _, _ :: _, hm
  | .throw _, _ :: _, hm | .merge .., _ :: _, hm | .makeKey .., _ :: _, hm
  | .goto .., _ :: _, hm | .frame .., _ :: _, hm => by simp [PathMiss] at hm

/-- A miss stays a miss past any further fields. -/
theorem pathMiss_append {h : Heap} :
    ∀ (v : Val) (fs gs : List String), PathMiss h v fs → PathMiss h v (fs ++ gs)
  | _, [], _, hm => by simp [PathMiss] at hm
  | .objAt fs' c oid, f :: p, gs, hm => by
    simp only [PathMiss, List.cons_append] at hm ⊢
    cases hlu : fs'.lookup (.str f) with
    | none => simp
    | some l =>
      simp only [hlu] at hm ⊢
      cases hget : h[l]? with
      | none => simp [hget] at hm
      | some u =>
        simp only [hget] at hm ⊢
        exact pathMiss_append u p gs hm
  | .nul, _ :: _, _, hm | .undef, _ :: _, _, hm | .tru, _ :: _, _, hm | .fls, _ :: _, _, hm
  | .num _, _ :: _, _, hm | .str _, _ :: _, _, hm | .bigint _, _ :: _, _, hm | .sym _, _ :: _, _, hm
  | .arr _, _ :: _, _, hm | .viewSpine .., _ :: _, _, hm | .var _, _ :: _, _, hm
  | .invoke .., _ :: _, _, hm | .construct .., _ :: _, _, hm | .letE .., _ :: _, _, hm
  | .makeAt .., _ :: _, _, hm | .readAt .., _ :: _, _, hm | .indexAt .., _ :: _, _, hm
  | .writeAt .., _ :: _, _, hm | .test .., _ :: _, _, hm | .ite .., _ :: _, _, hm
  | .arith .., _ :: _, _, hm | .arrLit _, _ :: _, _, hm | .elemAt .., _ :: _, _, hm
  | .setElem .., _ :: _, _, hm | .lenOf _, _ :: _, _, hm | .spread _, _ :: _, _, hm
  | .throw _, _ :: _, _, hm | .merge .., _ :: _, _, hm | .makeKey .., _ :: _, _, hm
  | .goto .., _ :: _, _, hm | .frame .., _ :: _, _, hm => by simp [PathMiss] at hm

/-- One more field past a path read: the object's own field, or a miss. -/
theorem readPath_snoc {h : Heap} :
    ∀ (v : Val) (fs : List String) (fs' : List (PropKey × Nat)) (c : CallCode) (oid : Nat) (f : String),
      HeapKnowledge.readPath h v fs = some (.objAt fs' c oid) →
        (∀ l u, fs'.lookup (.str f) = some l → h[l]? = some u → HeapKnowledge.readPath h v (fs ++ [f]) = some u) ∧
        (fs'.lookup (.str f) = none → PathMiss h v (fs ++ [f]))
  | v, [], fs', c, oid, f, hr => by
    simp only [HeapKnowledge.readPath, Option.some.injEq] at hr
    subst hr
    refine ⟨fun l u hl hu => ?_, fun hl => ?_⟩
    · simp [HeapKnowledge.readPath, hl, hu]
    · simp [PathMiss, hl]
  | .objAt gs c' oid', g :: p, fs', c, oid, f, hr => by
    simp only [HeapKnowledge.readPath] at hr
    cases hlu : gs.lookup (.str g) with
    | none => simp [hlu] at hr
    | some l =>
      simp only [hlu] at hr
      cases hget : h[l]? with
      | none => simp [hget] at hr
      | some u =>
        simp only [hget] at hr
        obtain ⟨h1, h2⟩ := readPath_snoc u p fs' c oid f hr
        refine ⟨fun l' u' hl hu => ?_, fun hl => ?_⟩
        · simp only [List.cons_append, HeapKnowledge.readPath, hlu, hget]; exact h1 l' u' hl hu
        · simp only [List.cons_append, PathMiss, hlu, hget]; exact h2 hl
  | .nul, _ :: _, _, _, _, _, hr | .undef, _ :: _, _, _, _, _, hr | .tru, _ :: _, _, _, _, _, hr
  | .fls, _ :: _, _, _, _, _, hr | .num _, _ :: _, _, _, _, _, hr | .str _, _ :: _, _, _, _, _, hr
  | .bigint _, _ :: _, _, _, _, _, hr | .sym _, _ :: _, _, _, _, _, hr | .arr _, _ :: _, _, _, _, _, hr
  | .viewSpine .., _ :: _, _, _, _, _, hr | .var _, _ :: _, _, _, _, _, hr
  | .invoke .., _ :: _, _, _, _, _, hr | .construct .., _ :: _, _, _, _, _, hr
  | .letE .., _ :: _, _, _, _, _, hr | .makeAt .., _ :: _, _, _, _, _, hr
  | .readAt .., _ :: _, _, _, _, _, hr | .indexAt .., _ :: _, _, _, _, _, hr
  | .writeAt .., _ :: _, _, _, _, _, hr | .test .., _ :: _, _, _, _, _, hr
  | .ite .., _ :: _, _, _, _, _, hr | .arith .., _ :: _, _, _, _, _, hr
  | .arrLit _, _ :: _, _, _, _, _, hr | .elemAt .., _ :: _, _, _, _, _, hr
  | .setElem .., _ :: _, _, _, _, _, hr | .lenOf _, _ :: _, _, _, _, _, hr
  | .spread _, _ :: _, _, _, _, _, hr | .throw _, _ :: _, _, _, _, _, hr
  | .merge .., _ :: _, _, _, _, _, hr | .makeKey .., _ :: _, _, _, _, _, hr
  | .goto .., _ :: _, _, _, _, _, hr | .frame .., _ :: _, _, _, _, _, hr => by
    simp [HeapKnowledge.readPath] at hr

theorem pathValue_prefix {h h' : Heap} (hp : h.IsPrefix h') (base : Val) (fs : List String) (v : Tm)
    (hv : HeapKnowledge.readPath h base fs = some v ∨ PathMiss h base fs) :
    HeapKnowledge.readPath h' base fs = some v ∨ PathMiss h' base fs :=
  hv.imp (readPath_prefix hp base fs v) (pathMiss_prefix hp base fs)

/-! ## Runs of the expression machine -/

theorem steps_of_val {n : Nat} {h h' : Heap} {w t : Tm} (hw : isVal w = true) (hs : Steps n h w h' t) :
    t = w ∧ h' = h := by
  cases hs with
  | refl => exact ⟨rfl, rfl⟩
  | next st _ => exact absurd st (value_no_step hw)

theorem steps_snoc {n : Nat} {h h' h'' : Heap} {t t' t'' : Tm} (hs : Steps n h t h' t')
    (st : Step h' t' h'' t'') : Steps (n + 1) h t h'' t'' := by
  induction hs with
  | refl => exact .next st .refl
  | next st₀ _ ih => exact .next st₀ (ih st)

theorem steps_length_le {n : Nat} {h h' : Heap} {t t' : Tm} (hs : Steps n h t h' t') :
    h.length ≤ h'.length := by
  induction hs with
  | refl => exact Nat.le_refl _
  | next st _ ih => exact Nat.le_trans (Footprints.step_length_le st) ih

theorem step_heapVals {h h' : Heap} {t t' : Tm} (st : Step h t h' t') (hh : ∀ u ∈ h, isVal u = true) :
    ∀ u ∈ h', isVal u = true := by
  induction st with
  | writeField hv _ _ | setPresent hv _ _ =>
    intro u hu
    rcases List.mem_or_eq_of_mem_set hu with hu | rfl
    · exact hh u hu
    · exact hv
  | makeFields hvs _ =>
    intro u hu
    simp only [List.mem_append, List.mem_singleton] at hu
    rcases hu with (hu | hu) | rfl
    · exact hh u hu
    · exact hvs u hu
    · rfl
  | arrAlloc hvs _ =>
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hh u hu
    · exact hvs u hu
  | setGrow hv _ _ =>
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hh u hu
    · rw [List.mem_singleton.mp hu]; exact hv
  | arrAllocThrow _ _ | arithThrow _ | lenStrThrow _ =>
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hh u hu
    · rw [List.mem_singleton.mp hu]; rfl
  | _ => simp_all

/-- What a run keeps of its start: closed terms and heap, a heap of values,
and a heap at least as long. -/
theorem steps_wf {n : Nat} {h h' : Heap} {t t' : Tm} (hs : Steps n h t h' t') (ht : Scoped 0 t)
    (hv : ∀ u ∈ h, isVal u = true) (hsc : ∀ u ∈ h, Scoped 0 u) :
    Scoped 0 t' ∧ (∀ u ∈ h', isVal u = true) ∧ (∀ u ∈ h', Scoped 0 u) ∧ h.length ≤ h'.length := by
  induction hs with
  | refl => exact ⟨ht, hv, hsc, Nat.le_refl _⟩
  | next st _ ih =>
    obtain ⟨ht1, hsc1⟩ := TolerantFrames.ReadOnly.step_scoped st ht hsc
    obtain ⟨ht2, hv2, hsc2, hle⟩ := ih ht1 (step_heapVals st hv) hsc1
    exact ⟨ht2, hv2, hsc2, Nat.le_trans (Footprints.step_length_le st) hle⟩

theorem steps_throw_val {n : Nat} {h h' : Heap} {w v : Tm} (hw : isVal w = true)
    (hs : Steps n h (.throw w) h' v) (hv : isVal v = true) : False := by
  cases hs with
  | refl => simp [isVal] at hv
  | next st _ =>
    cases st with
    | throwC st' => exact absurd st' (value_no_step hw)

/-- **A `let` returns through its bound term's value.** -/
theorem steps_letE {n : Nat} {h h' : Heap} {t v : Tm} (hs : Steps n h t h' v) :
    ∀ {a b : Tm}, t = .letE a b → isVal v = true →
      ∃ n₁ n₂ hm u, Steps n₁ h a hm u ∧ isVal u = true ∧ Steps n₂ hm (subst 0 u b) h' v := by
  induction hs with
  | refl => intro a b ht hv; subst ht; simp [isVal] at hv
  | next st rest ih =>
    intro a b ht hv
    subst ht
    cases st with
    | letC st' =>
      obtain ⟨n₁, n₂, hm, u, h1, h2, h3⟩ := ih rfl hv
      exact ⟨n₁ + 1, n₂, hm, u, .next st' h1, h2, h3⟩
    | letV ha => exact ⟨0, _, _, a, .refl, ha, rest⟩

/-- **An allocation returns an object at fresh locations.** -/
theorem steps_makeAt {n : Nat} {h h' : Heap} {t v : Tm} (hs : Steps n h t h' v) :
    ∀ {c : CallCode} {ns : List PropKey} {xs : List Tm}, t = .makeAt c ns xs → isVal v = true →
      ∃ (hm : Heap) (oid : Nat), h.length ≤ hm.length ∧ v = .objAt (slots hm.length ns) c oid := by
  induction hs with
  | refl => intro c ns xs ht hv; subst ht; simp [isVal] at hv
  | next st rest ih =>
    intro c ns xs ht hv
    subst ht
    cases st with
    | makeArg _ _ st' =>
      obtain ⟨hm, oid, hle, rfl⟩ := ih rfl hv
      exact ⟨hm, oid, Nat.le_trans (Footprints.step_length_le st') hle, rfl⟩
    | makeFields _ _ =>
      obtain ⟨rfl, rfl⟩ := steps_of_val rfl rest
      exact ⟨_, _, Nat.le_refl _, rfl⟩

/-- **An array literal returns a spine at fresh locations.** -/
theorem steps_arrLit {n : Nat} {h h' : Heap} {t v : Tm} (hs : Steps n h t h' v) :
    ∀ {xs : List Tm}, t = .arrLit xs → isVal v = true →
      ∃ (hm : Heap) (k : Nat), h.length ≤ hm.length ∧ v = .arr (elemSlots hm.length k) := by
  induction hs with
  | refl => intro xs ht hv; subst ht; simp [isVal] at hv
  | next st rest ih =>
    intro xs ht hv
    subst ht
    cases st with
    | arrArg _ _ st' =>
      obtain ⟨hm, k, hle, rfl⟩ := ih rfl hv
      exact ⟨hm, k, Nat.le_trans (Footprints.step_length_le st') hle, rfl⟩
    | arrSpread _ _ _ => exact ih rfl hv
    | arrAlloc _ _ =>
      obtain ⟨rfl, rfl⟩ := steps_of_val rfl rest
      exact ⟨_, _, Nat.le_refl _, rfl⟩
    | arrAllocThrow _ _ => exact (steps_throw_val (by simp [thrownError, isVal]) rest hv).elim

/-- **A read of a named field of a value reads the object's own field, or
misses it.** -/
theorem steps_readAt {n : Nat} {h h' : Heap} {f : PropKey} {w v : Tm} (hh : ∀ u ∈ h, isVal u = true)
    (hw : isVal w = true) (hs : Steps n h (.readAt f w) h' v) (hv : isVal v = true) :
    ∃ fs c oid, w = .objAt fs c oid ∧
      ((∃ l, fs.lookup f = some l ∧ h[l]? = some v ∧ h' = h) ∨ fs.lookup f = none) := by
  cases hs with
  | refl => simp [isVal] at hv
  | next st rest =>
    cases st with
    | readC st' => exact absurd st' (value_no_step hw)
    | readField hl hget =>
      obtain ⟨rfl, rfl⟩ := steps_of_val (hh _ (List.mem_of_getElem? hget)) rest
      exact ⟨_, _, _, rfl, .inl ⟨_, hl, hget, rfl⟩⟩
    | readProto hl _ _ => exact ⟨_, _, _, rfl, .inr hl⟩
    | readMissing hl _ => exact ⟨_, _, _, rfl, .inr hl⟩

theorem raises_isVal {t v : Tm} (hr : Raises t v) : isVal v = true := by
  induction hr <;> simp_all

/-! ## The origin of a node's result -/

theorem matchCodeIdx_some {ι : Type} {codes : List (RequestJson.CodeRequest ι)} {ar : Nat} {E : List Tm}
    {K : List (Continuation × Option Target)} {s ci : Nat} (h : matchCodeIdx codes ar E K s = some ci) :
    ∃ q, codes[ci]? = some q ∧ q.entry.arity = ar ∧ q.entry.exprs = E ∧ q.entry.conts = K ∧
      q.entry.start = s := by
  unfold matchCodeIdx at h
  obtain ⟨⟨q, j⟩, hf, hj⟩ := Option.map_eq_some_iff.mp h
  simp only at hj
  subst hj
  have hp := List.find?_some hf
  obtain ⟨_, hlt, hq⟩ := List.mem_zipIdx (List.mem_of_find?_eq_some hf)
  simp only [Nat.sub_zero, Nat.zero_add] at hlt hq
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨q, by rw [hq]; exact List.getElem?_eq_getElem hlt, hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩

theorem slots_ge (base : Nat) : ∀ (ns : List PropKey) k l, (k, l) ∈ slots base ns → base ≤ l
  | [], _, _, hm => by cases hm
  | _ :: ns, k, l, hm => by
    rcases List.mem_cons.mp hm with h | h
    · cases h; exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ base) (slots_ge (base + 1) ns k l h)

theorem elemSlots_ge (base n : Nat) {l : Nat} (hm : some l ∈ elemSlots base n) : base ≤ l := by
  simp only [elemSlots, List.mem_map, Option.some.injEq] at hm
  obtain ⟨i, _, rfl⟩ := hm
  omega

/-- The forms of expression `exprOrigin` reads; it gives every other one a
primitive or an unknown origin. -/
theorem exprOrigin_cases {ι : Type} (codes : List (RequestJson.CodeRequest ι)) (l : Nat)
    (env : List SlotOrigin) (e : Tm) :
    (∃ s, e = .var s) ∨ (∃ a b, e = .letE a b) ∨ (∃ f s, e = .readAt (.str f) (.var s)) ∨
      (∃ ar E K s caps kd cm cp ns xs, e = .makeAt (.graph ar E K s caps kd cm cp) ns xs) ∨
      (∃ ns xs, e = .makeAt .absent ns xs) ∨ (∃ xs, e = .arrLit xs) ∨
      exprOrigin codes l env e = .prim ∨ exprOrigin codes l env e = .unknown := by
  cases e with
  | var s => exact .inl ⟨s, rfl⟩
  | letE a b => exact .inr (.inl ⟨a, b, rfl⟩)
  | readAt k a =>
    cases k with
    | str f =>
      cases a with
      | var s => exact .inr (.inr (.inl ⟨f, s, rfl⟩))
      | _ => simp [exprOrigin, isPrimExpr]
    | sym _ => simp [exprOrigin, isPrimExpr]
  | makeAt c ns xs =>
    cases c with
    | graph ar E K s caps kd cm cp => exact .inr (.inr (.inr (.inl ⟨ar, E, K, s, caps, kd, cm, cp, ns, xs, rfl⟩)))
    | absent => exact .inr (.inr (.inr (.inr (.inl ⟨ns, xs, rfl⟩))))
    | _ => simp [exprOrigin, isPrimExpr]
  | arrLit xs => exact .inr (.inr (.inr (.inr (.inr (.inl ⟨xs, rfl⟩)))))
  | _ => simp [exprOrigin, isPrimExpr]

section
variable {ι : Type} {codes : List (RequestJson.CodeRequest ι)} {ρ₀ : Env} {sibVal : String → Tm}
  {bOwn bCaller : Nat}

/-- What a node's environment and heap meet for its expression's run: closed
values in the slots and the heap, and the heap at least `bOwn` long. -/
def RunWf (bOwn : Nat) (h : Heap) (ρ : Env) : Prop :=
  (∀ i, isVal (ρ i) = true) ∧ (∀ i, Scoped 0 (ρ i)) ∧ (∀ u ∈ h, isVal u = true) ∧
    (∀ u ∈ h, Scoped 0 u) ∧ bOwn ≤ h.length

theorem RunWf.push {h : Heap} {ρ : Env} {v : Tm} (hw : RunWf bOwn h ρ) (hv : isVal v = true)
    (hs : Scoped 0 v) : RunWf bOwn h (push v ρ) :=
  ⟨fun i => by cases i with | zero => exact hv | succ k => exact hw.1 k,
    fun i => by cases i with | zero => exact hs | succ k => exact hw.2.1 k,
    hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩

theorem RunWf.mapEnv {h : Heap} {ρ : Env} (hw : RunWf bOwn h ρ) (m : PointClaims.Mapping) :
    RunWf bOwn h (PointClaims.mapEnv m ρ) :=
  ⟨fun _ => hw.1 _, fun _ => hw.2.1 _, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩

/-- The value a closure literal allocates meets the origin `exprOrigin`
gives it, where each slot meets `orig`'s origin in `h'`. -/
theorem closure_origin_holds {h' : Heap} {env : List SlotOrigin} {ρ : Env} {l : Nat}
    {ar : Nat} {E : List Tm} {K : List (Continuation × Option Target)} {s : Nat} {caps : List Tm}
    {kd : Invoke} {cm : Bool} {cp : ComponentTag} {ns : List PropKey} {xs : List Tm} {v : Tm}
    (orig : SlotOrigin → SlotOrigin) (horig_unknown : orig .unknown = .unknown)
    (horig_prim : orig .prim = .prim)
    (horig_closure : ∀ ci cs, orig (.closure ci cs) = .closure ci (cs.map orig))
    (hslot : ∀ j, OriginValueHolds codes ρ₀ sibVal bOwn bCaller h' (orig (originAt env j)) (ρ j))
    (hv : ∃ fs oid, v = .objAt fs (.graph ar E K s (caps.map (instantiate 0 ρ)) kd cm cp) oid) :
    OriginValueHolds codes ρ₀ sibVal bOwn bCaller h'
      (orig (exprOrigin codes l env (.makeAt (.graph ar E K s caps kd cm cp) ns xs))) v := by
  obtain ⟨fs, oid, rfl⟩ := hv
  simp only [exprOrigin]
  cases hm : matchCodeIdx codes ar E K s with
  | none => simp only [horig_unknown]; exact originValueHolds_unknown_any
  | some ci =>
    obtain ⟨q, hq, h1, h2, h3, h4⟩ := matchCodeIdx_some hm
    rw [horig_closure, OriginValueHolds]
    refine ⟨q, fs, ar, E, K, s, caps.map (instantiate 0 ρ), kd, cm, cp, oid, hq, h1, h2, h3, h4, rfl,
      by simp, fun i hi => ?_⟩
    have hi' : i < caps.length := by simpa using hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi',
      Option.map_some, Option.getD_some]
    generalize caps[i] = c
    cases c with
    | var j => simpa [instantiate] using hslot j
    | _ =>
      simp only [isPrimExpr, Bool.false_eq_true, ite_true, ite_false, horig_prim, horig_unknown]
      first | exact originValueHolds_prim_any | exact originValueHolds_unknown_any

/-- **The result's origin, degraded, holds of the value any node expression
returns**, wherever the slots' degraded origins held at its start. -/
theorem exprOrigin_dropHeap_sound (l : Nat) : ∀ (e : Tm) (env : List SlotOrigin) (ρ : Env)
    (h₁ h₂ h' : Heap) (n : Nat) (v : Tm), RunWf bOwn h₁ ρ →
    (∀ s, OriginValueHolds codes ρ₀ sibVal bOwn bCaller h₁ (originAt env s).dropHeap (ρ s)) →
    Steps n h₁ (instantiate 0 ρ e) h₂ v → isVal v = true →
    OriginValueHolds codes ρ₀ sibVal bOwn bCaller h' (exprOrigin codes l env e).dropHeap v
  | e, env, ρ, h₁, h₂, h', n, v, hw, henv, hs, hv => by
    rcases exprOrigin_cases codes l env e with ⟨s, rfl⟩ | ⟨a, b, rfl⟩ | ⟨f, s, rfl⟩ |
        ⟨ar, E, K, s, caps, kd, cm, cp, ns, xs, rfl⟩ | ⟨ns, xs, rfl⟩ | ⟨xs, rfl⟩ | he | he
    · simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at hs
      obtain ⟨rfl, rfl⟩ := steps_of_val (hw.1 s) hs
      simp only [exprOrigin]
      exact originValueHolds_dropHeap_any _ _ (henv s)
    · simp only [instantiate] at hs
      obtain ⟨n₁, n₂, hm, u, ha, hu, hb⟩ := steps_letE hs rfl hv
      have hbeta := instantiate_beta ρ hw.2.1 u b 0
      simp only [Nat.zero_add] at hbeta
      rw [hbeta] at hb
      have hwa := steps_wf ha (TolerantFrames.ReadOnly.instantiate_scoped hw.2.1 a 0) hw.2.2.1 hw.2.2.2.1
      have iha := exprOrigin_dropHeap_sound l a env ρ h₁ hm hm n₁ u hw henv ha hu
      have hw' : RunWf bOwn hm (push u ρ) :=
        RunWf.push ⟨hw.1, hw.2.1, hwa.2.1, hwa.2.2.1, Nat.le_trans hw.2.2.2.2 hwa.2.2.2⟩ hu hwa.1
      have henv' : ∀ s, OriginValueHolds codes ρ₀ sibVal bOwn bCaller hm
          (originAt (exprOrigin codes l env a :: env) s).dropHeap (push u ρ s) := by
        intro s
        cases s with
        | zero => exact iha
        | succ k => exact originValueHolds_dropHeap_any _ _ (henv k)
      simp only [exprOrigin]
      exact exprOrigin_dropHeap_sound l b _ (push u ρ) hm h₂ h' n₂ v hw' henv' hb hv
    · simp only [exprOrigin]
      split <;> (simp only [SlotOrigin.dropHeap]; exact originValueHolds_unknown_any)
    · simp only [instantiate, instantiateArgs_eq_map] at hs
      obtain ⟨hm, oid, _, rfl⟩ := steps_makeAt hs rfl hv
      exact closure_origin_holds SlotOrigin.dropHeap rfl rfl
        (fun ci cs => by rw [SlotOrigin.dropHeap, SlotOrigin.dropHeapList_eq_map])
        (fun j => originValueHolds_dropHeap_any _ _ (henv j)) ⟨_, _, rfl⟩
    · simp only [instantiate, instantiateArgs_eq_map] at hs
      obtain ⟨hm, oid, hle, rfl⟩ := steps_makeAt hs rfl hv
      simp only [exprOrigin, SlotOrigin.dropHeap]
      rw [OriginValueHolds]
      exact fun k l' hk => Nat.le_trans (Nat.le_trans hw.2.2.2.2 hle) (slots_ge _ ns k l' hk)
    · simp only [instantiate, instantiateArgs_eq_map] at hs
      obtain ⟨hm, k, hle, rfl⟩ := steps_arrLit hs rfl hv
      simp only [exprOrigin, SlotOrigin.dropHeap]
      rw [OriginValueHolds]
      exact fun l' hl' => Nat.le_trans (Nat.le_trans hw.2.2.2.2 hle) (elemSlots_ge _ k hl')
    · rw [he, SlotOrigin.dropHeap]; exact originValueHolds_prim_any
    · rw [he, SlotOrigin.dropHeap]; exact originValueHolds_unknown_any
termination_by e => sizeOf e

theorem heapVals_index {h : Heap} (hh : ∀ u ∈ h, isVal u = true) :
    ∀ (l : Nat) (v : Val), h[l]? = some v → isVal v = true :=
  fun _ v hv => hh v (List.mem_of_getElem? hv)

/-- **The result's origin holds of the value a node expression that changes
no existing storage returns**, in the heap it ends in, wherever the slots
met their origins at its start. -/
theorem exprOrigin_sound (l : Nat) : ∀ (e : Tm) (env : List SlotOrigin) (ρ : Env)
    (h₁ h₂ : Heap) (n : Nat) (v : Tm), RunWf bOwn h₁ ρ → isReadOnlyOrAlloc e = true →
    EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h₁ env ρ →
    Steps n h₁ (instantiate 0 ρ e) h₂ v → isVal v = true →
    OriginValueHolds codes ρ₀ sibVal bOwn bCaller h₂ (exprOrigin codes l env e) v
  | e, env, ρ, h₁, h₂, n, v, hw, hro, henv, hs, hv => by
    have hρro : ∀ i, isReadOnlyOrAlloc (ρ i) = true := fun i => isReadOnlyOrAlloc_of_isVal (hw.1 i)
    have hpre : h₁.IsPrefix h₂ :=
      (isReadOnlyOrAlloc_steps (heapVals_index hw.2.2.1)
        (isReadOnlyOrAlloc_instantiate hρro e 0 hro) hs).1
    rcases exprOrigin_cases codes l env e with ⟨s, rfl⟩ | ⟨a, b, rfl⟩ | ⟨f, s, rfl⟩ |
        ⟨ar, E, K, s, caps, kd, cm, cp, ns, xs, rfl⟩ | ⟨ns, xs, rfl⟩ | ⟨xs, rfl⟩ | he | he
    · simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at hs
      obtain ⟨rfl, rfl⟩ := steps_of_val (hw.1 s) hs
      simp only [exprOrigin]
      exact henv s
    · simp only [isReadOnlyOrAlloc, Bool.and_eq_true] at hro
      simp only [instantiate] at hs
      obtain ⟨n₁, n₂, hm, u, ha, hu, hb⟩ := steps_letE hs rfl hv
      have hbeta := instantiate_beta ρ hw.2.1 u b 0
      simp only [Nat.zero_add] at hbeta
      rw [hbeta] at hb
      have hwa := steps_wf ha (TolerantFrames.ReadOnly.instantiate_scoped hw.2.1 a 0) hw.2.2.1 hw.2.2.2.1
      have hprea : h₁.IsPrefix hm :=
        (isReadOnlyOrAlloc_steps (heapVals_index hw.2.2.1)
          (isReadOnlyOrAlloc_instantiate hρro a 0 hro.1) ha).1
      have iha := exprOrigin_sound l a env ρ h₁ hm n₁ u hw hro.1 henv ha hu
      have hw' : RunWf bOwn hm (push u ρ) :=
        RunWf.push ⟨hw.1, hw.2.1, hwa.2.1, hwa.2.2.1, Nat.le_trans hw.2.2.2.2 hwa.2.2.2⟩ hu hwa.1
      have henv' : EnvOriginHolds codes ρ₀ sibVal bOwn bCaller hm (exprOrigin codes l env a :: env)
          (push u ρ) := by
        intro s
        cases s with
        | zero => exact iha
        | succ k => exact originValueHolds_transfer (pathValue_prefix hprea) _ _ (henv k)
      simp only [exprOrigin]
      exact exprOrigin_sound l b _ (push u ρ) hm h₂ n₂ v hw' hro.2 henv' hb hv
    · simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero] at hs
      obtain ⟨fs, c, oid, hρs, hcase⟩ := steps_readAt hw.2.2.1 (hw.1 s) hs hv
      have hx := henv s
      simp only [exprOrigin]
      cases ho : originAt env s with
      | param p =>
        rw [ho, OriginValueHolds] at hx
        rw [OriginValueHolds, ← hx, hρs]
        rcases hcase with ⟨l', hl, hget, rfl⟩ | hl
        · left; simp [HeapKnowledge.readPath, hl, hget]
        · right; simp [PathMiss, hl]
      | path p gs =>
        rw [ho, OriginValueHolds, hρs] at hx
        rw [OriginValueHolds]
        rcases hx with hx | hx
        · obtain ⟨h1, h2⟩ := readPath_snoc _ gs fs c oid f hx
          rcases hcase with ⟨l', hl, hget, rfl⟩ | hl
          · exact .inl (h1 l' v hl hget)
          · exact .inr (pathMiss_prefix hpre _ _ (h2 hl))
        · exact .inr (pathMiss_prefix hpre _ _ (pathMiss_append _ _ _ hx))
      | _ => exact originValueHolds_unknown_any
    · simp only [instantiate, instantiateArgs_eq_map] at hs
      obtain ⟨hm, oid, _, rfl⟩ := steps_makeAt hs rfl hv
      exact closure_origin_holds (fun o => o) rfl rfl (fun ci cs => by simp)
        (fun j => originValueHolds_transfer (pathValue_prefix hpre) _ _ (henv j)) ⟨_, _, rfl⟩
    · simp only [instantiate, instantiateArgs_eq_map] at hs
      obtain ⟨hm, oid, hle, rfl⟩ := steps_makeAt hs rfl hv
      simp only [exprOrigin]
      rw [OriginValueHolds]
      exact fun k l' hk => Nat.le_trans (Nat.le_trans hw.2.2.2.2 hle) (slots_ge _ ns k l' hk)
    · simp only [instantiate, instantiateArgs_eq_map] at hs
      obtain ⟨hm, k, hle, rfl⟩ := steps_arrLit hs rfl hv
      simp only [exprOrigin]
      rw [OriginValueHolds]
      exact fun l' hl' => Nat.le_trans (Nat.le_trans hw.2.2.2.2 hle) (elemSlots_ge _ k hl')
    · rw [he]; exact originValueHolds_prim_any
    · rw [he]; exact originValueHolds_unknown_any
termination_by e => sizeOf e

/-- **A node's step leaves the origins `nodeOrigins` gives**: the slots'
in the heap the expression's run reaches, and the result's of the value it
returns. -/
theorem nodeOrigins_sound {l : Nat} {env : List SlotOrigin} {e : Tm} {ρ : Env} {h₁ h₂ : Heap} {n : Nat}
    {t : Tm} (hw : RunWf bOwn h₁ ρ) (henv : EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h₁ env ρ)
    (hs : Steps n h₁ (instantiate 0 ρ e) h₂ t) :
    EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h₂ (nodeOrigins codes l env e).2 ρ ∧
      (isVal t = true → OriginValueHolds codes ρ₀ sibVal bOwn bCaller h₂ (nodeOrigins codes l env e).1 t) := by
  by_cases hro : isReadOnlyOrAlloc e = true
  · simp only [nodeOrigins, hro, ↓reduceIte]
    have hρro : ∀ i, isReadOnlyOrAlloc (ρ i) = true := fun i => isReadOnlyOrAlloc_of_isVal (hw.1 i)
    have hpre : h₁.IsPrefix h₂ :=
      (isReadOnlyOrAlloc_steps (heapVals_index hw.2.2.1)
        (isReadOnlyOrAlloc_instantiate hρro e 0 hro) hs).1
    exact ⟨fun s => originValueHolds_transfer (pathValue_prefix hpre) _ _ (henv s),
      fun hv => exprOrigin_sound l e env ρ h₁ h₂ n t hw hro henv hs hv⟩
  · simp only [nodeOrigins, hro, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun s => ?_, fun hv => exprOrigin_dropHeap_sound l e env ρ h₁ h₂ h₂ n t hw
      (fun s => originValueHolds_dropHeap _ _ (henv s)) hs hv⟩
    rw [originAt_map_dropHeap]
    exact originValueHolds_dropHeap _ _ (henv s)

/-! ## The whole run -/

/-- **Where a run of `P` stands for the origin table `table`**: at a node,
its table entry holds of the slots in the heap; while a node's expression
runs, its table entry held of the slots when the node was entered, and the
expression's run since then. -/
@[nospecialize] def OriginRunInv (codes : List (RequestJson.CodeRequest ι)) (P : Program)
    (table : Array (Option (List SlotOrigin))) (ρ₀ : Env) (sibVal : String → Tm) (bOwn bCaller : Nat) :
    Heap → State → Prop
  | h, .at l ρ => RunWf bOwn h ρ ∧ ∃ env, table[l]?.join = some env ∧
      EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h env ρ
  | h, .eval t ρ k x => ∃ (l : Nat) (node : Node) (env : List SlotOrigin) (h₁ : Heap) (n : Nat),
      P[l]? = some node ∧ table[l]?.join = some env ∧
      node.continuation = k ∧ node.handler = x ∧ RunWf bOwn h₁ ρ ∧
      EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h₁ env ρ ∧
      Steps n h₁ (instantiate 0 ρ node.expression) h t
  | _, .done _ => True
  | _, .raised _ => True

theorem originsValid_start {P : Program} {start : Nat} {initEnv : List SlotOrigin}
    {table : Array (Option (List SlotOrigin))} (hv : originsValid codes P start initEnv table = true) :
    ∃ env, table[start]?.join = some env ∧ originsLe env initEnv = true := by
  simp only [originsValid, Bool.and_eq_true] at hv
  have h1 := hv.1
  split at h1
  · exact ⟨_, ‹_›, h1⟩
  · cases h1

theorem originsValid_edge {P : Program} {start : Nat} {initEnv : List SlotOrigin}
    {table : Array (Option (List SlotOrigin))} (hv : originsValid codes P start initEnv table = true)
    {l : Nat} {node : Node} {env : List SlotOrigin} (hP : P[l]? = some node) (ht : table[l]?.join = some env)
    {tgt : Nat} {next : List SlotOrigin} (hm : (tgt, next) ∈ nodeEdges codes l node env) :
    ∃ tgtEnv, table[tgt]?.join = some tgtEnv ∧ originsLe tgtEnv next = true := by
  simp only [originsValid, Bool.and_eq_true, List.all_eq_true] at hv
  have hl : l < P.length := (List.getElem?_eq_some_iff.mp hP).1
  have h2 := hv.2 l (List.mem_range.mpr hl)
  simp only [hP, ht, List.all_eq_true] at h2
  have h3 := h2 (tgt, next) hm
  split at h3
  · exact ⟨_, ‹_›, h3⟩
  · cases h3

/-- **Leaving a node along one of its edges keeps the invariant.** -/
theorem originRunInv_exit {P : Program} {start : Nat} {initEnv : List SlotOrigin}
    {table : Array (Option (List SlotOrigin))} (hvalid : originsValid codes P start initEnv table = true)
    {l : Nat} {node : Node} {env : List SlotOrigin} {h₁ h : Heap} {n : Nat} {ρ : Env} {t : Tm}
    (hP : P[l]? = some node) (ht : table[l]?.join = some env) (hw : RunWf bOwn h₁ ρ)
    (henv : EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h₁ env ρ)
    (hs : Steps n h₁ (instantiate 0 ρ node.expression) h t)
    {tg : Target} {pushed : Option SlotOrigin} {w : Tm}
    (hmem : (tg.label, applyTargetMap (nodeOrigins codes l env node.expression).2 pushed tg) ∈
      nodeEdges codes l node env)
    (hpush : ∀ o, pushed = some o → OriginValueHolds codes ρ₀ sibVal bOwn bCaller h o w)
    (hwv : isVal w = true) (hws : Scoped 0 w) :
    OriginRunInv codes P table ρ₀ sibVal bOwn bCaller h
      (.at tg.label (PointClaims.mapEnv tg.mapping (match pushed with | some _ => push w ρ | none => ρ))) := by
  have hwf := steps_wf hs (TolerantFrames.ReadOnly.instantiate_scoped hw.2.1 _ 0) hw.2.2.1 hw.2.2.2.1
  have hwh : RunWf bOwn h ρ := ⟨hw.1, hw.2.1, hwf.2.1, hwf.2.2.1, Nat.le_trans hw.2.2.2.2 hwf.2.2.2⟩
  obtain ⟨henv', _⟩ := nodeOrigins_sound (l := l) hw henv hs
  obtain ⟨tgtEnv, htgt, hle⟩ := originsValid_edge hvalid hP ht hmem
  have hmap := applyTargetMap_sound (tgt := tg) henv' hpush
  cases pushed with
  | none => exact ⟨hwh.mapEnv _, tgtEnv, htgt, originsLe_sound hle hmap⟩
  | some _ => exact ⟨(hwh.push hwv hws).mapEnv _, tgtEnv, htgt, originsLe_sound hle hmap⟩

/-- **Every transition keeps the invariant.** -/
theorem originRunInv_step {P : Program} {start : Nat} {initEnv : List SlotOrigin}
    {table : Array (Option (List SlotOrigin))} (hvalid : originsValid codes P start initEnv table = true)
    {h h' : Heap} {s s' : State} (tr : Transition P h s h' s')
    (hi : OriginRunInv codes P table ρ₀ sibVal bOwn bCaller h s) :
    OriginRunInv codes P table ρ₀ sibVal bOwn bCaller h' s' := by
  cases tr with
  | enter hP =>
    obtain ⟨hw, env, ht, henv⟩ := hi
    exact ⟨_, _, env, _, 0, hP, ht, rfl, rfl, hw, henv, .refl⟩
  | expr st =>
    obtain ⟨l, node, env, h₁, n, hP, ht, hk, hx, hw, henv, hs⟩ := hi
    exact ⟨l, node, env, h₁, n + 1, hP, ht, hk, hx, hw, henv, steps_snoc hs st⟩
  | ret _ => simp [OriginRunInv]
  | raise _ => simp [OriginRunInv]
  | bind hv =>
    obtain ⟨l, node, env, h₁, n, hP, ht, hk, hx, hw, henv, hs⟩ := hi
    have hres := (nodeOrigins_sound (l := l) hw henv hs).2 hv
    have hwf := steps_wf hs (TolerantFrames.ReadOnly.instantiate_scoped hw.2.1 _ 0) hw.2.2.1 hw.2.2.2.1
    exact originRunInv_exit (pushed := some (nodeOrigins codes l env node.expression).1) hvalid hP ht hw henv hs
      (by simp [nodeEdges, nodeSuccessors, hk]) (fun o ho => by cases ho; exact hres) hv hwf.1
  | effect hv =>
    obtain ⟨l, node, env, h₁, n, hP, ht, hk, hx, hw, henv, hs⟩ := hi
    have hwf := steps_wf hs (TolerantFrames.ReadOnly.instantiate_scoped hw.2.1 _ 0) hw.2.2.1 hw.2.2.2.1
    exact originRunInv_exit (pushed := none) hvalid hP ht hw henv hs
      (by simp [nodeEdges, nodeSuccessors, hk]) (fun o ho => by cases ho) hv hwf.1
  | yes =>
    obtain ⟨l, node, env, h₁, n, hP, ht, hk, hx, hw, henv, hs⟩ := hi
    exact originRunInv_exit (pushed := none) (w := .tru) hvalid hP ht hw henv hs
      (by simp [nodeEdges, nodeSuccessors, hk]) (fun o ho => by cases ho) rfl trivial
  | no =>
    obtain ⟨l, node, env, h₁, n, hP, ht, hk, hx, hw, henv, hs⟩ := hi
    exact originRunInv_exit (pushed := none) (w := .fls) hvalid hP ht hw henv hs
      (by simp [nodeEdges, nodeSuccessors, hk]) (fun o ho => by cases ho) rfl trivial
  | yesBind =>
    obtain ⟨l, node, env, h₁, n, hP, ht, hk, hx, hw, henv, hs⟩ := hi
    exact originRunInv_exit (pushed := some .prim) (w := .tru) hvalid hP ht hw henv hs
      (by simp [nodeEdges, nodeSuccessors, hk])
      (fun o ho => by cases ho; exact originValueHolds_prim_any) rfl trivial
  | noBind =>
    obtain ⟨l, node, env, h₁, n, hP, ht, hk, hx, hw, henv, hs⟩ := hi
    exact originRunInv_exit (pushed := some .prim) (w := .fls) hvalid hP ht hw henv hs
      (by simp [nodeEdges, nodeSuccessors, hk])
      (fun o ho => by cases ho; exact originValueHolds_prim_any) rfl trivial
  | tagBind hv =>
    obtain ⟨l, node, env, h₁, n, hP, ht, hk, hx, hw, henv, hs⟩ := hi
    have hres := (nodeOrigins_sound (l := l) hw henv hs).2 hv
    have hwf := steps_wf hs (TolerantFrames.ReadOnly.instantiate_scoped hw.2.1 _ 0) hw.2.2.1 hw.2.2.2.1
    exact originRunInv_exit (pushed := some (nodeOrigins codes l env node.expression).1) hvalid hP ht hw henv hs
      (by split <;> simp [nodeEdges, nodeSuccessors, hk]) (fun o ho => by cases ho; exact hres) hv hwf.1
  | handle hr =>
    obtain ⟨l, node, env, h₁, n, hP, ht, hk, hx, hw, henv, hs⟩ := hi
    have hwf := steps_wf hs (TolerantFrames.ReadOnly.instantiate_scoped hw.2.1 _ 0) hw.2.2.1 hw.2.2.2.1
    exact originRunInv_exit (pushed := some .unknown) hvalid hP ht hw henv hs
      (by simp [nodeEdges, nodeSuccessors, hx])
      (fun o ho => by cases ho; exact originValueHolds_unknown_any) (raises_isVal hr)
      (TolerantFrames.ReadOnly.raises_scoped hr hwf.1)

theorem originRunInv_reaches {P : Program} {start : Nat} {initEnv : List SlotOrigin}
    {table : Array (Option (List SlotOrigin))} (hvalid : originsValid codes P start initEnv table = true)
    {k : Nat} {h h' : Heap} {s s' : State} (hr : TolerantFrames.Target.ReachesIn P k h s h' s')
    (hi : OriginRunInv codes P table ρ₀ sibVal bOwn bCaller h s) :
    OriginRunInv codes P table ρ₀ sibVal bOwn bCaller h' s' := by
  induction hr with
  | refl => exact hi
  | step tr _ ih => exact ih (originRunInv_step hvalid tr hi)

/-- **The origin table is sound over a whole run** (proved): when the
table `originsValid` checks for `P` from `(start, initEnv)` holds of the
entry environment `ρₑ` and heap `h₀` (closed values in the slots and the
heap, which is at least `bOwn` long), then at every node `.at l ρ` the graph
machine reaches on heap `h`, the table has an entry `env` for `l` and every
slot of `ρ` meets its origin in `env` in `h`. -/
theorem originsValid_sound {P : Program} {start : Nat} {initEnv : List SlotOrigin}
    {table : Array (Option (List SlotOrigin))} (hvalid : originsValid codes P start initEnv table = true)
    {h₀ : Heap} {ρₑ : Env} (hwf : RunWf bOwn h₀ ρₑ)
    (hentry : EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h₀ initEnv ρₑ)
    {j : Nat} {h : Heap} {l : Nat} {ρ : Env} (hr : TolerantFrames.Target.ReachesIn P j h₀ (.at start ρₑ) h (.at l ρ)) :
    ∃ env, table[l]?.join = some env ∧ EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h env ρ := by
  obtain ⟨env₀, ht₀, hle₀⟩ := originsValid_start hvalid
  have hi := originRunInv_reaches (ρ₀ := ρ₀) (sibVal := sibVal) (bOwn := bOwn) (bCaller := bCaller) hvalid hr
    ⟨hwf, env₀, ht₀, originsLe_sound hle₀ hentry⟩
  simp only [OriginRunInv] at hi
  exact hi.2

end

/-- **The origins a request's checks compute are sound over its runs**
(`originsValid_sound` at `requestOrigins`): `checkProducer` and
`checkCallerDemands` accept only where `originsValid` holds of them. -/
theorem requestOrigins_sound {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceElaboration.SourceRequest σ ι)
    (hvalid : originsValid r.codes r.program r.start (requestInitOrigins r) (requestOrigins r) = true)
    {ρ₀ : Env} {sibVal : String → Tm} {bOwn bCaller : Nat} {h₀ : Heap} {ρₑ : Env}
    (hwf : RunWf bOwn h₀ ρₑ)
    (hentry : EnvOriginHolds r.codes ρ₀ sibVal bOwn bCaller h₀ (requestInitOrigins r) ρₑ)
    {j : Nat} {h : Heap} {l : Nat} {ρ : Env} (hr : TolerantFrames.Target.ReachesIn r.program j h₀ (.at r.start ρₑ) h (.at l ρ)) :
    ∃ env, (requestOrigins r)[l]?.join = some env ∧ EnvOriginHolds r.codes ρ₀ sibVal bOwn bCaller h env ρ :=
  originsValid_sound hvalid hwf hentry hr

/-- **The origins a closure code's checks compute are sound over its runs**
(`originsValid_sound` at the entry origins `checkClosureAgainstDemand` and
`programConfines` give it: the receiver and the parameters unknown, then the
captures' origins `caps`). -/
theorem closureOrigins_sound {ι : Type} (codes : List (RequestJson.CodeRequest ι)) (q : RequestJson.CodeRequest ι)
    (caps : List SlotOrigin)
    (hvalid : originsValid codes (GraphCode.program q.entry.exprs q.entry.conts) q.entry.start
      (.unknown :: List.replicate q.entry.arity .unknown ++ caps)
      (computeOrigins codes (GraphCode.program q.entry.exprs q.entry.conts) q.entry.start
        (.unknown :: List.replicate q.entry.arity .unknown ++ caps)) = true)
    {ρ₀ : Env} {sibVal : String → Tm} {bOwn bCaller : Nat} {h₀ : Heap} {ρₑ : Env}
    (hwf : RunWf bOwn h₀ ρₑ)
    (hentry : EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h₀
      (.unknown :: List.replicate q.entry.arity .unknown ++ caps) ρₑ)
    {j : Nat} {h : Heap} {l : Nat} {ρ : Env}
    (hr : TolerantFrames.Target.ReachesIn (GraphCode.program q.entry.exprs q.entry.conts) j h₀ (.at q.entry.start ρₑ) h (.at l ρ)) :
    ∃ env, (computeOrigins codes (GraphCode.program q.entry.exprs q.entry.conts) q.entry.start
        (.unknown :: List.replicate q.entry.arity .unknown ++ caps))[l]?.join = some env ∧
      EnvOriginHolds codes ρ₀ sibVal bOwn bCaller h env ρ :=
  originsValid_sound hvalid hwf hentry hr

end Verification.SourceClaimJson
