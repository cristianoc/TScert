import Verification.Programs.ArgumentRegionGraph

/-! Executable regional graph checks. Candidate provenance is checked at the
entry and on every edge. A node is a provenance step (a slot copy, a stable
read) or a step whose local effect the common check includes in the stated
frame (`stepWithin`): a step within the closed bound, a call at its
signature's frame, an element write. -/
namespace Verification.GraphCode.ArgumentRegionGraph
variable {ε : Verification.HeapKnowledge.EntryState}
open ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules Footprints
open PositiveCertificates (InstanceImageCheck)
open ArgumentRegionFresh

/-- A node covered by the existing closed-footprint rules. -/
@[nospecialize] def checkClosedNode [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (c : NodeEvidence ι) (t : Tm) (thr : Bool) : Bool :=
  ProgramCertificates.checkScope (entry c).length t &&
    (!thr || throwsWithin G images sums Φ [] c t) &&
    (((ExpressionEffects.check G (entry c) t || writeWithinAt G Φ c t) ||
      (decide ((ProgramCertificates.claim c.expression).term = t) &&
        (ProgramCertificates.checkTreeUsing G images c.expression (sums := sums) ||
          PromiseCalls.requiresTree G images (entryFacts G c) (fun _ => false) sums c.expression) &&
        selectedWithinAt Φ [] c.expression)) || ExpressionEffects.emptyType G (result c))

/-- A heap within a closed bound on its own locations is within it. -/
theorem holdsOn_length {c : Footprints.Closed} {h h' : Heap}
    (hp : c.HoldsOn (· < h.length) h h') : c.Holds h h' := by
  rw [Footprints.Closed.holds_iff]
  exact ⟨hp.1, fun l v hv => hp.2 l v (List.getElem?_eq_some_iff.mp hv).1 hv⟩

/-- A step within the closed bound: its frame is the bound's. -/
def closedStep (Φ : Footprints.Closed) : StepEffect := ⟨fun _ => none, Φ.fp, Φ.fp⟩

theorem closedStep_ok [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {c : NodeEvidence ι} {t : Tm} {thr : Bool}
    (hc : checkClosedNode G images sums Φ c t thr = true)
    (ht : ExpressionOk G c t) (hsums : ProgramCertificates.SummariesSound G images sums) :
    StepOk G c t (closedStep Φ) thr := by
  simp only [checkClosedNode, Bool.and_eq_true] at hc
  have hn := nodeWithin_of_checked (F := []) (thr := thr) hc.1.1 hc.2 (fun hthr => by
    have hx := hc.1.2; rw [hthr] at hx; simpa using hx) ht hsums
  intro ε n W h ρ he hi hk hw hh
  refine ⟨ρ, ?_, ?_⟩
  · intro p s hs; simp [closedStep] at hs
  apply HeapObservations.SafePostExc.weaken _ _
    (hn ε n W h ρ h.length (Nat.le_refl _) (fun _ hi => nomatch hi) he hi hk hw hh)
  · intro h' _ hq
    exact Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp (holdsOn_length hq.1))
  · intro h' hq hthr
    exact Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp (holdsOn_length (hq hthr)))

/-- A call's positions' slots: the receiver's, and each actual's that is a
slot. -/
def callSlots (r : Tm) (args : List Tm) (p : Nat) : Option Nat :=
  if p = 0 then (match r with
    | .var j => some j
    | _ => none) else match args[p - 1]? with
    | some (.var j) => some j
    | _ => none

/-- The frame `ReceiverGrows` states: every old location but the receiver's
store kept, which holds a store. -/
def grownFrame : Footprint := [((Region.field 0 arrayStoreKey).inCls .store, .any)]

theorem grown_post {e : CallEffects.Effect} {r : Tm} {args : List Tm} {h h' : Heap}
    (hw : e.within r args h h') (hg : CallEffects.ReceiverGrows r h h') :
    Post grownFrame (CallEffects.callEnv r args) h h' := by
  refine ⟨hw.1, fun l v hv => ?_⟩
  rcases hg l v hv with hs | ⟨hs, ls, ls', rfl, hl', -⟩
  · exact ⟨v, hs, .inl rfl⟩
  · refine ⟨.arr ls', hl', .inr ⟨((Region.field 0 arrayStoreKey).inCls .store, .any), by simp [grownFrame], ?_,
      trivial⟩⟩
    simp only [Region.mem, hv, Bool.and_eq_true]
    exact ⟨by simpa [CallEffects.callEnv, Footprints.storeOf] using hs, rfl⟩

/-- A call at its selected signature: its frame at the call's positions, on
normal return the narrower `grownFrame` where the signature states
`receiverGrows`; on a throw its frame, which it must state then. -/
@[nospecialize] def callStep [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (c : NodeEvidence ι) (t : Tm) (thr : Bool) : Option StepEffect :=
  if decide ((ProgramCertificates.claim c.expression).term = t) &&
      (ProgramCertificates.checkTreeUsing G images c.expression (sums := sums) ||
        PromiseCalls.requiresTree G images (entryFacts G c) (fun _ => false) sums c.expression) &&
      ExpressionEffects.selectedOperands c.expression && (!thr || ExpressionEffects.selectedThrows c.expression) then
    match t, ExpressionEffects.selectedEffect c.expression with
    | .invoke _ r args, some eff =>
      if !thr || eff.onThrow then
        some ⟨callSlots r args, if eff.receiverGrows then grownFrame else eff.frame, eff.frame⟩
      else none
    | _, _ => none
  else none

theorem callStep_ok [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {c : NodeEvidence ι} {t : Tm} {thr : Bool} {se : StepEffect}
    (hc : callStep G images sums c t thr = some se)
    (hsums : ProgramCertificates.SummariesSound G images sums) :
    StepOk G c t se thr := by
  intro ε n W h ρ he _ hk hw hh
  unfold callStep at hc
  split at hc
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨hterm0, htree⟩, hops⟩, hthrows⟩ := hcond
    subst hterm0
    split at hc
    · rename_i fn receiver args eff hterm heff
      split at hc
      · rename_i hthrow
        cases hc
        have hs : HeapObservations.SafePostExc (excOf G)
            (meaning G (ProgramCertificates.claim c.expression).type)
            (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term))
              (ExpressionEffects.actualsOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term)) h)
            (fun h' => thr = true → eff.excPost
              (ExpressionEffects.receiverOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term))
              (ExpressionEffects.actualsOf (instantiate 0 ρ (ProgramCertificates.claim c.expression).term)) h h')
            n W h (instantiate 0 ρ (ProgramCertificates.claim c.expression).term) := by
          rcases Bool.or_eq_true_iff.mp htree with htree | hreq
          · cases ht : thr
            · apply HeapObservations.SafePostExc.of_post (fun _ hf => by cases hf)
              exact ExpressionEffects.selected_sound c.expression htree hops heff
                (ProgramCertificates.codesSound_none _) hsums he hw hh
            · have hx : ExpressionEffects.selectedThrows c.expression = true := by
                simpa [ht] using hthrows
              exact HeapObservations.SafePostExc.weaken (fun _ _ h => h) (fun _ h _ => h)
                (ExpressionEffects.selected_sound_exc c.expression htree hops hx heff
                  (ProgramCertificates.codesSound_none _) hsums he hw hh)
          · obtain ⟨eff', heff', hs⟩ := PromiseCalls.requiresTree_sound_exc
              (ProgramCertificates.codesSound_none _) hsums c.expression hreq
            rw [heff] at heff'; cases heff'
            exact HeapObservations.SafePostExc.weaken (fun _ _ h => h) (fun _ h _ => h)
              (hs he hk hw hh)
        rw [hterm] at hs ⊢
        refine ⟨CallEffects.callEnv (instantiate 0 ρ receiver) (args.map (instantiate 0 ρ)), ?_, ?_⟩
        · intro p s hp
          simp only [callSlots] at hp
          split at hp
          · rename_i hp0
            split at hp
            · cases hp; simp [CallEffects.callEnv, hp0, instantiate]
            · cases hp
          · rename_i hp0
            split at hp
            · rename_i j hj
              cases hp
              simp [CallEffects.callEnv, hp0, List.getD, List.getElem?_map, hj, instantiate]
            · cases hp
        · simp only [ExpressionEffects.receiverOf, ExpressionEffects.actualsOf, instantiate,
            instantiateArgs_eq_map] at hs ⊢
          apply HeapObservations.SafePostExc.weaken _ _ hs
          · intro h' v hp
            cases hg : eff.receiverGrows
            · simp only [Bool.false_eq_true, ↓reduceIte]; exact hp.1
            · simp only [↓reduceIte]; exact grown_post hp.1 (hp.2.2.2.2.2.1 hg).1
          · intro h' hp hthr
            have hon : eff.onThrow = true := by
              simp only [Bool.or_eq_true, Bool.not_eq_true'] at hthrow
              rcases hthrow with ht | ht
              · rw [hthr] at ht; cases ht
              · exact ht
            exact hp hthr hon
      · cases hc
    · cases hc
  · cases hc

/-- An element write: its frame at the node's slots (`writeFrame`). -/
def writeStepEffect (i : Nat) : StepEffect := ⟨some, ExpressionEffects.writeFrame i, ExpressionEffects.writeFrame i⟩

theorem writeStep_ok [DecidableEq ι] {G : NormalGraph ι} {c : NodeEvidence ι} {t : Tm} {thr : Bool} {i : Nat}
    (hc : ExpressionEffects.writeStep G (entry c) t = some i) (ht : ExpressionOk G c t) :
    StepOk G c t (writeStepEffect i) thr := by
  intro ε n W h ρ he hi hk hw hh
  refine ⟨ρ, fun p s hp => by cases hp; rfl, ?_⟩
  have hs := HeapObservations.erase (HeapObservations.consequence
    (fun _ _ _ hu => hu.1) (fun _ _ h => h) (ht ε n W h ρ he hi hk hw hh))
  exact HeapObservations.SafePostExc.weaken (fun _ _ h => h) (fun _ h _ => h)
    (ExpressionEffects.writeStep_sound hc he hh hs)

/-- A node's local effects: within the closed bound, a call's, an element
write's. -/
@[nospecialize] def stepEffects [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (c : NodeEvidence ι) (t : Tm) (thr : Bool) : List StepEffect :=
  (if checkClosedNode G images sums Φ c t thr then [closedStep Φ] else []) ++
    (callStep G images sums c t thr).toList ++
    ((ExpressionEffects.writeStep G (entry c) t).map writeStepEffect).toList

theorem stepEffects_ok [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {c : NodeEvidence ι} {t : Tm} {thr : Bool} {se : StepEffect}
    (hm : se ∈ stepEffects G images sums Φ c t thr)
    (ht : ExpressionOk G c t) (hsums : ProgramCertificates.SummariesSound G images sums) :
    StepOk G c t se thr := by
  simp only [stepEffects, List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · split at hm
    · rename_i hc
      cases List.mem_singleton.mp hm
      exact closedStep_ok hc ht hsums
    · cases hm
  · exact callStep_ok (Option.mem_toList.mp hm) hsums
  · obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp (Option.mem_toList.mp hm)
    exact writeStep_ok hi ht

/-! ## Fresh facts of a node

A node's value is fresh (`freshOut`): a slot copy of a fresh slot, a
constant, an allocation of an object with a store field, a read of a fresh
cell, or a call at a signature stating a fresh result. It is a fresh cell
(`cellOut`): a copy of a fresh cell, or an allocation holding a fresh slot's
value in its cell field. It keeps the node's fresh cells (`cellsKept`): an
inspection, a write of a fresh slot's value, or a step whose frames keep
every location of class value. -/

/-- A value with no field. -/
def constTerm : Tm → Bool
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => true
  | _ => false

/-- An allocation of an object with a store field. -/
def allocStore : Tm → Bool
  | .makeAt _ ns _ => ns.contains arrayStoreKey
  | .letE _ (.makeAt _ ns _) => ns.contains arrayStoreKey
  | _ => false

/-- A read of the cell field of a slot holding a fresh cell. -/
def cellRead (C : List Nat) : Tm → Bool
  | .readAt k (.var i) => k == cellKey && C.contains i
  | _ => false

@[nospecialize] def freshOut [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι)) (F C : List Nat) (c : NodeEvidence ι) (t : Tm) : Bool :=
  varFresh F t || constTerm t || allocStore t || cellRead C t || callFresh G images sums c t

/-- A plain object allocated from slots, the slot its cell field holds
fresh. -/
def cellAlloc (F : List Nat) (t : Tm) : Bool :=
  match t, HeapExpressionRules.allocationSlots t with
  | .makeAt .absent _ _, some parts => decide (parts.map Prod.fst).Nodup && match parts.lookup cellKey with
    | some j => F.contains j
    | none => false
  | _, _ => false

def cellOut (F C : List Nat) (t : Tm) : Bool := varFresh C t || cellAlloc F t

/-- A write of a fresh slot's value. -/
def freshWrite (F : List Nat) : Tm → Bool
  | .writeAt _ (.var _) (.var j) => F.contains j
  | _ => false

@[nospecialize] def cellsKept [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι)) (Φ : Footprints.Closed) (F C : List Nat)
    (c : NodeEvidence ι) (t : Tm) (thr : Bool) : Bool :=
  C.isEmpty || ExpressionEffects.check G (entry c) t || freshWrite F t ||
    (stepEffects G images sums Φ c t thr).any fun se => keepsValues se.normal && (!thr || keepsValues se.raised)

/-- **A node's freshness check.** -/
@[nospecialize] def checkFresh [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sums : List (ProgramCertificates.ReadSummary ι)) (Φ : Footprints.Closed) (F C : List Nat)
    (c : NodeEvidence ι) (t : Tm) (thr : Bool) : Bool :=
  ProgramCertificates.checkScope (entry c).length t && cellsKept G images sums Φ F C c t thr

/-- A run every state of which meets nothing. -/
theorem trivial_run {Ξ T : Fam} {n W h t} (hs : Safe Ξ T n W h t) :
    HeapObservations.SafePostExc Ξ T (fun _ _ => True) (fun _ => True) n W h t :=
  safePostExc_invariant (I := fun _ _ => True) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
    trivial hs

theorem instantiate_makeAt (d : Nat) (ρ : Env) (c : CallCode) (ns : List PropKey) (xs : List Tm) :
    ∃ c' xs', instantiate d ρ (.makeAt c ns xs) = .makeAt c' ns xs' := by
  cases c <;> simp only [instantiate] <;> exact ⟨_, _, rfl⟩

theorem allocStore_shape {t : Tm} (ha : allocStore t = true) (ρ : Env) :
    AllocShape (instantiate 0 ρ t) := by
  unfold allocStore at ha
  split at ha
  · rename_i c ns inits
    obtain ⟨c', xs', he⟩ := instantiate_makeAt 0 ρ c ns inits
    exact .inl ⟨c', ns, xs', he, List.contains_iff_mem.mp ha⟩
  · rename_i a c ns inits
    obtain ⟨c', xs', he⟩ := instantiate_makeAt 1 ρ c ns inits
    exact .inr ⟨instantiate 0 ρ a, c', ns, xs', by simp only [instantiate, he], List.contains_iff_mem.mp ha⟩
  · cases ha

/-- A slot in scope holds a value. -/
theorem slot_value [DecidableEq ι] {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat} {W : WorldT n}
    {i : Nat} (he : EnvOk G Γ ρ n W) (hi : i < Γ.length) : isVal (ρ i) = true :=
  (meaning_value (he.2 i Γ[i] (List.getElem?_eq_getElem hi))).1

theorem freshOut_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {sums : List (ProgramCertificates.ReadSummary ι)} {F C : List Nat} {c : NodeEvidence ι} {t : Tm}
    (hf : freshOut G images sums F C c t = true) (hscope : ProgramCertificates.checkScope (entry c).length t = true)
    (hsums : ProgramCertificates.SummariesSound G images sums)
    {n W h ρ} {b : Nat} (hb : b ≤ h.length) (hF : FreshHold F C b ρ h) (he : EnvOk G (entry c) ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : Safe (excOf G) (meaning G (result c)) n W h (instantiate 0 ρ t)) :
    HeapObservations.SafePostExc (excOf G) (meaning G (result c)) (fun _ v => FreshValue b v) (fun _ => True)
      n W h (instantiate 0 ρ t) := by
  simp only [freshOut, Bool.or_eq_true] at hf
  rcases hf with ((((hv | hc) | ha) | hr) | hcall)
  · cases t <;> simp only [varFresh, Bool.false_eq_true] at hv
    rename_i i
    simp only [ProgramCertificates.checkScope, decide_eq_true_eq] at hscope
    simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
    exact value_run (slot_value he hscope) (hF.values i (List.contains_iff_mem.mp hv)) hs
  · cases t <;> simp only [constTerm, Bool.false_eq_true] at hc <;> simp only [instantiate] at hs ⊢ <;>
      exact value_run rfl (freshValue_of_fields rfl rfl) hs
  · exact HeapObservations.SafePostExc.weaken (fun _ _ hq => freshAt_value hq) (fun _ h => h)
      (alloc_fresh hb (allocStore_shape ha ρ) hs)
  · cases t <;> simp only [cellRead, Bool.false_eq_true] at hr
    rename_i k x
    cases x <;> simp only [Bool.false_eq_true] at hr
    rename_i i
    simp only [Bool.and_eq_true, beq_iff_eq] at hr
    obtain ⟨rfl, hi⟩ := hr
    simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
    cases n with
    | zero => trivial
    | succ n =>
      exact HeapObservations.SafePostExc.weaken (fun _ _ hq => hq.2) (fun _ _ => trivial)
        (cellRead_fresh (hF.cells i (List.contains_iff_mem.mp hi)) (HeapExpressionRules.heap_values hw hh) hs)
  · simp only [callFresh, Bool.and_eq_true, decide_eq_true_eq] at hcall
    obtain ⟨⟨⟨hfr, hops⟩, hterm'⟩, htree⟩ := hcall
    split at hfr
    · rename_i eff heff
      have hsel := ExpressionEffects.selected_sound c.expression htree hops heff
        (ProgramCertificates.codesSound_none _) hsums (by simpa only [ControlFlow.entry] using he) hw hh
      rw [hterm'] at hsel
      have hboth := HeapObservations.cross_upto n (fun _ _ _ _ _ _ _ _ hu _ => hu) W W h _ hh hh
        (trivial_run hs).post hsel
      exact HeapObservations.SafePostExc.of_post (fun _ => trivial)
        (HeapObservations.weaken (Q := fun h' v => True ∧ eff.post _ _ h h' v)
          (fun _ _ hq => freshAt_value ((hq.2.2.1 hfr).lower hb)) hboth)
    · cases hfr

theorem lookup_parts {k : PropKey} {j : Nat} :
    ∀ {parts : List (PropKey × Nat)}, parts.lookup k = some j →
      ∃ i, ∃ hi : i < parts.length, parts[i].1 = k ∧ parts[i].2 = j
  | [], h => by simp at h
  | p :: ps, h => by
    by_cases he : k = p.1
    · subst he
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      exact ⟨0, by simp, rfl, h⟩
    · have hne : (k == p.1) = false := by simpa using he
      simp only [List.lookup, hne] at h
      obtain ⟨i, hi, h1, h2⟩ := lookup_parts h
      exact ⟨i + 1, by simp; omega, by simpa using h1, by simpa using h2⟩

theorem cellOut_sound [DecidableEq ι] {G : NormalGraph ι} {F C : List Nat} {c : NodeEvidence ι} {t : Tm}
    (hf : cellOut F C t = true) (hscope : ProgramCertificates.checkScope (entry c).length t = true)
    {n W h ρ} {b : Nat} (hF : FreshHold F C b ρ h) (he : EnvOk G (entry c) ρ n W)
    (hs : Safe (excOf G) (meaning G (result c)) n W h (instantiate 0 ρ t)) :
    HeapObservations.SafePostExc (excOf G) (meaning G (result c)) (fun h' v => CellFresh b h' v) (fun _ => True)
      n W h (instantiate 0 ρ t) := by
  simp only [cellOut, Bool.or_eq_true] at hf
  rcases hf with hv | ha
  · cases t <;> simp only [varFresh, Bool.false_eq_true] at hv
    rename_i i
    simp only [ProgramCertificates.checkScope, decide_eq_true_eq] at hscope
    simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
    exact value_run (slot_value he hscope) (hF.cells i (List.contains_iff_mem.mp hv)) hs
  · unfold cellAlloc at ha
    split at ha
    · rename_i ns inits parts hparts
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
      obtain ⟨hnd, hj⟩ := ha
      split at hj
      · rename_i j hl
        obtain ⟨hns, hinits⟩ := HeapExpressionRules.allocationParts_eq (by simpa [HeapExpressionRules.allocationSlots] using hparts)
        subst hns; subst hinits
        obtain ⟨i, hi, hk, hjv⟩ := lookup_parts hl
        simp only [ProgramCertificates.checkScope, ProgramCertificates.checkScopes_iff, List.mem_map] at hscope
        have hin : ∀ p ∈ parts, p.2 < (entry c).length := fun p hp => by
          have := hscope _ ⟨p, hp, rfl⟩
          simpa [ProgramCertificates.checkScope] using this
        simp only [instantiate, instantiateArgs_eq_map, List.map_map] at hs ⊢
        have hfun : (instantiate 0 ρ ∘ fun p : PropKey × Nat => Tm.var p.2) = fun p => ρ p.2 := by
          funext p; simp [instantiate]
        rw [hfun] at hs ⊢
        refine HeapObservations.SafePostExc.weaken (Q := fun h' v => CellFresh b h' v ∧ h.IsPrefix h')
          (fun _ _ hq => hq.1) (fun _ h => h) ?_
        refine cellAlloc_fresh (i := i) hnd (by simpa using hi) (by simpa using hk) (by simp)
          (fun v hv => ?_) (fun v hv => ?_) hs
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
          exact slot_value he (hin p hp)
        · simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at hv
          subst hv
          rw [hjv]
          exact hF.values j (List.contains_iff_mem.mp hj)
      · cases hj
    · cases ha

theorem cellsKept_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {sums : List (ProgramCertificates.ReadSummary ι)} {Φ : Footprints.Closed} {F C : List Nat}
    {c : NodeEvidence ι} {t : Tm} {thr : Bool}
    (hk : cellsKept G images sums Φ F C c t thr = true)
    (hscope : ProgramCertificates.checkScope (entry c).length t = true)
    (ht : ExpressionOk G c t) (hsums : ProgramCertificates.SummariesSound G images sums)
    {n W h ρ} {b : Nat} (hF : FreshHold F C b ρ h) (he : EnvOk G (entry c) ρ n W)
    (hi : PromiseCalls.ImpliesOk G c.implies ρ n W) (hkn : HeapKnowledge.Holds (entryFacts G c) ε ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : Safe (excOf G) (meaning G (result c)) n W h (instantiate 0 ρ t)) :
    HeapObservations.SafePostExc (excOf G) (meaning G (result c)) (fun h' _ => CellsHold C b ρ h')
      (fun h' => thr = true → CellsHold C b ρ h') n W h (instantiate 0 ρ t) := by
  simp only [cellsKept, Bool.or_eq_true] at hk
  rcases hk with ((hnil | hins) | hwr) | hstep
  · simp only [List.isEmpty_iff] at hnil
    subst hnil
    exact HeapObservations.SafePostExc.weaken (fun _ _ _ i hi => nomatch hi) (fun _ _ _ i hi => nomatch hi)
      (trivial_run hs)
  · have hkeep : keepsValues Footprints.Closed.empty.fp = true := rfl
    exact HeapObservations.SafePostExc.weaken
      (fun _ _ hq => hF.cells.post (σ := ρ) hkeep (Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp hq)))
      (fun _ hq _ => hF.cells.post (σ := ρ) hkeep (Footprints.Closed.post_iff.mpr (Footprints.Closed.holds_iff.mp hq)))
      (ExpressionEffects.sound_exc hins hscope he hw hh hs)
  · obtain ⟨f, i, j, rfl, hwr⟩ : ∃ f i j, t = .writeAt f (.var i) (.var j) ∧ F.contains j = true := by
      unfold freshWrite at hwr
      split at hwr
      · exact ⟨_, _, _, rfl, hwr⟩
      · cases hwr
    simp only [ProgramCertificates.checkScope, Bool.and_eq_true, decide_eq_true_eq] at hscope
    simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
    exact HeapObservations.SafePostExc.weaken (fun _ _ h => h) (fun _ h _ => h)
      (freshWrite_cells (slot_value he hscope.1) (slot_value he hscope.2)
        (hF.values j (List.contains_iff_mem.mp hwr)) hF.cells hs)
  · obtain ⟨se, hse, hkv⟩ := List.any_eq_true.mp hstep
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hkv
    obtain ⟨σ, -, hrun⟩ := stepEffects_ok hse ht hsums ε n W h ρ he hi hkn hw hh
    exact HeapObservations.SafePostExc.weaken (fun _ _ hq => hF.cells.post hkv.1 hq)
      (fun _ hq hthr => hF.cells.post (by rcases hkv.2 with h | h; · rw [hthr] at h; cases h
                                          · exact h) (hq hthr)) hrun

/-- **A node passing the freshness check meets its freshness obligation**,
its value fresh where `freshOut` says so and a fresh cell where `cellOut`
does. -/
theorem checkFresh_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {sums : List (ProgramCertificates.ReadSummary ι)} {Φ : Footprints.Closed} {F C : List Nat}
    {c : NodeEvidence ι} {t : Tm} {thr : Bool}
    (hc : checkFresh G images sums Φ F C c t thr = true)
    (ht : ExpressionOk G c t) (hsums : ProgramCertificates.SummariesSound G images sums) :
    FreshWithin G c t F C (freshOut G images sums F C c t) (cellOut F C t) thr := by
  intro ε n W h ρ b hb hF he hi hk hw hh
  simp only [checkFresh, Bool.and_eq_true] at hc
  obtain ⟨hscope, hkept⟩ := hc
  have hs := HeapObservations.erase (HeapObservations.consequence
    (fun _ _ _ hu => hu.1) (fun _ _ h => h) (ht ε n W h ρ he hi hk hw hh))
  have hv : HeapObservations.SafePostExc (excOf G) (meaning G (result c))
      (fun _ v => freshOut G images sums F C c t = true → FreshValue b v) (fun _ => True) n W h (instantiate 0 ρ t) := by
    cases hf : freshOut G images sums F C c t
    · exact HeapObservations.SafePostExc.weaken (fun _ _ _ h => nomatch h) (fun _ h => h) (trivial_run hs)
    · exact HeapObservations.SafePostExc.weaken (fun _ _ hq _ => hq) (fun _ h => h)
        (freshOut_sound hf hscope hsums hb hF he hw hh hs)
  have hcell : HeapObservations.SafePostExc (excOf G) (meaning G (result c))
      (fun h' v => cellOut F C t = true → CellFresh b h' v) (fun _ => True) n W h (instantiate 0 ρ t) := by
    cases hf : cellOut F C t
    · exact HeapObservations.SafePostExc.weaken (fun _ _ _ h => nomatch h) (fun _ h => h) (trivial_run hs)
    · exact HeapObservations.SafePostExc.weaken (fun _ _ hq _ => hq) (fun _ h => h)
        (cellOut_sound hf hscope hF he hs)
  have hkeep := cellsKept_sound hkept hscope ht hsums hF he hi hk hw hh hs
  have h12 := HeapObservations.SafePostExc.cross_upto n (fun _ _ _ _ _ _ _ _ hu _ => hu) W W h _ hh hh hv hcell
  have h123 := HeapObservations.SafePostExc.cross_upto n (fun _ _ _ _ _ _ _ _ hu _ => hu) W W h _ hh hh h12 hkeep
  exact HeapObservations.SafePostExc.weaken (fun _ _ hq => ⟨hq.1.1, hq.1.2, hq.2⟩) (fun _ hq => hq.2) h123

/-! ## Fresh fields of a node

A node's value has a fresh field `f` (`fieldOut`): a slot copy, where the
slot's field `f` is fresh; a constant, which has no field; an allocation
of distinct keys whose field `f` is initialized from a slot holding a fresh
value. A node keeps the fresh fields of its entry where each slot's type
states the field stable (`fieldsKept`). -/

/-- The fields an allocation of distinct keys initializes from a slot
holding a fresh value, of the names `names`. -/
def allocFieldOut (names : List String) (F : List Nat) (t : Tm) : List String :=
  match HeapExpressionRules.allocationSlots t with
  | some parts => if (parts.map Prod.fst).Nodup then names.filter fun f =>
      match parts.lookup (.str f) with
      | some j => F.contains j
      | none => false
    else []
  | none => []

/-- The fields of a node's value that are fresh, of the names `names`. -/
def fieldOut (names : List String) (F : List Nat) (Fs : List (Nat × String)) (t : Tm) : List String :=
  match t with
  | .var j => names.filter fun f => Fs.contains (j, f)
  | .makeAt .absent ns xs => allocFieldOut names F (.makeAt .absent ns xs)
  | _ => if constTerm t then names else []

/-- A run whose value is claimed no fresh field. -/
theorem noFields_run {Ξ T : Fam} {n W h t} {b : Nat} {L : List String} (hnil : ∀ f, f ∈ L → False)
    (hs : Safe Ξ T n W h t) :
    HeapObservations.SafePostExc Ξ T (fun h' v => ∀ f ∈ L, FieldFresh b h' v f) (fun _ => True) n W h t :=
  HeapObservations.SafePostExc.weaken (fun _ _ _ f hf => (hnil f hf).elim) (fun _ h => h) (trivial_run hs)

theorem fieldOut_sound [DecidableEq ι] {G : NormalGraph ι} {names : List String} {F : List Nat}
    {Fs : List (Nat × String)} {c : NodeEvidence ι} {t : Tm}
    (hscope : ProgramCertificates.checkScope (entry c).length t = true)
    {n W h ρ} {b : Nat} (hF : ∀ i ∈ F, FreshValue b (ρ i)) (hFs : FieldsHold Fs b ρ h)
    (he : EnvOk G (entry c) ρ n W)
    (hs : Safe (excOf G) (meaning G (result c)) n W h (instantiate 0 ρ t)) :
    HeapObservations.SafePostExc (excOf G) (meaning G (result c))
      (fun h' v => ∀ f ∈ fieldOut names F Fs t, FieldFresh b h' v f) (fun _ => True)
      n W h (instantiate 0 ρ t) := by
  cases t
  case var j =>
    simp only [ProgramCertificates.checkScope, decide_eq_true_eq] at hscope
    simp only [instantiate, Nat.not_lt_zero, ite_false, Nat.sub_zero] at hs ⊢
    refine value_run (slot_value he hscope) (fun f hf => ?_) hs
    simp only [fieldOut, List.mem_filter] at hf
    exact hFs (j, f) (List.contains_iff_mem.mp hf.2)
  case makeAt code ns inits =>
    cases code
    case absent =>
      simp only [fieldOut]
      unfold allocFieldOut
      split
      · rename_i parts hparts
        split
        · rename_i hnd
          obtain ⟨hns, hinits⟩ := HeapExpressionRules.allocationParts_eq
            (by simpa [HeapExpressionRules.allocationSlots] using hparts)
          subst hns; subst hinits
          simp only [ProgramCertificates.checkScope, ProgramCertificates.checkScopes_iff, List.mem_map] at hscope
          have hin : ∀ p ∈ parts, p.2 < (entry c).length := fun p hp => by
            have := hscope _ ⟨p, hp, rfl⟩
            simpa [ProgramCertificates.checkScope] using this
          simp only [instantiate, instantiateArgs_eq_map, List.map_map] at hs ⊢
          have hfun : (instantiate 0 ρ ∘ fun p : PropKey × Nat => Tm.var p.2) = fun p => ρ p.2 := by
            funext p; simp [instantiate]
          rw [hfun] at hs ⊢
          refine fieldAlloc_fresh hnd (by simp) (fun v hv => ?_) (fun f hf => ?_) hs
          · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
            exact slot_value he (hin p hp)
          · simp only [List.mem_filter] at hf
            split at hf
            · rename_i j hl
              obtain ⟨i, hi, hk, hjv⟩ := lookup_parts hl
              refine ⟨i, by simpa using hi, by simpa using hk, fun v hv => ?_⟩
              simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
                Option.some.injEq] at hv
              subst hv
              rw [hjv]
              exact (hF j (List.contains_iff_mem.mp hf.2)).2
            · cases hf.2
        · exact HeapObservations.SafePostExc.weaken (fun _ _ _ f hf => nomatch hf) (fun _ h => h) (trivial_run hs)
      · exact HeapObservations.SafePostExc.weaken (fun _ _ _ f hf => nomatch hf) (fun _ h => h) (trivial_run hs)
    all_goals exact noFields_run (fun f hf => by simp [fieldOut, constTerm] at hf) hs
  all_goals first
    | (simp only [instantiate] at hs ⊢; exact value_run rfl (fun f _ => fieldFresh_of_fields rfl) hs)
    | exact noFields_run (fun f hf => by simp [fieldOut, constTerm] at hf) hs

/-- **A node passing the field check meets its fresh-field obligation.** -/
theorem fieldsCheck_sound [DecidableEq ι] {G : NormalGraph ι} {names : List String} {F : List Nat}
    {Fs : List (Nat × String)} {c : NodeEvidence ι} {t : Tm}
    (hk : fieldsKept G (entry c) Fs = true)
    (hscope : ProgramCertificates.checkScope (entry c).length t = true) (ht : ExpressionOk G c t) :
    FieldsWithin G c t F Fs (fieldOut names F Fs t) := by
  intro ε n W h ρ b _ hF hFs he hi hkn hw hh
  have hs := HeapObservations.erase (HeapObservations.consequence
    (fun _ _ _ hu => hu.1) (fun _ _ h => h) (ht ε n W h ρ he hi hkn hw hh))
  have hkeep := fieldsHold_frame hk he hh hFs (trivial_run hs)
  have hout := fieldOut_sound (names := names) hscope hF hFs he hs
  have hboth := HeapObservations.SafePostExc.cross_upto n (fun _ _ _ _ _ _ _ _ hu _ => hu) W W h _ hh hh
    hkeep hout
  exact HeapObservations.SafePostExc.weaken (fun _ _ hq => ⟨hq.1.2, hq.2⟩) (fun _ hq => hq.1.2) hboth

/-- A copy's origins: every region its slot holds. The node check verifies
the slot and scope. -/
def copyOrigins (facts : List ArgumentPathTracking.Fact) (t : Tm) : List ArgumentStoreRegion :=
  match t with
  | .var i => (facts.filter fun f => f.slot == i).map (·.region)
  | _ => []

@[nospecialize] def checkCopy [DecidableEq ι] (c : NodeEvidence ι)
    (facts : List ArgumentPathTracking.Fact) (t : Tm) (rs : List ArgumentStoreRegion) : Bool :=
  match t with
  | .var i => decide (i < (entry c).length) && rs.all fun r => facts.contains ⟨i, r⟩
  | _ => false

theorem checkCopy_sound [DecidableEq ι] {G : NormalGraph ι} {Φ : Footprints.Closed}
    {regions : List ArgumentStoreRegion} {facts : List ArgumentPathTracking.Fact}
    {c : NodeEvidence ι} {t : Tm} {rs : List ArgumentStoreRegion} {thr : Bool} {F : List Nat}
    {Fs : List (Nat × String)}
    (hc : checkCopy c facts t rs = true) (ht : ExpressionOk G c t) :
    NodeWithin G Φ regions c t facts F Fs rs thr := by
  intro ε n W h ρ initial input hb hf _ _ he hi hk hw hh _
  cases t <;> simp only [checkCopy, Bool.false_eq_true] at hc
  rename_i i
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem] at hc
  have hv : isVal (ρ i) = true :=
    (meaning_value (he.2 i _ (List.getElem?_eq_getElem hc.1))).1
  have hs := HeapObservations.erase (HeapObservations.consequence
    (fun _ _ _ hu => hu.1) (fun _ _ h => h) (ht ε n W h ρ he hi hk hw hh))
  simp only [instantiate, Nat.sub_zero] at hs ⊢
  cases n with
  | zero => trivial
  | succ n =>
    apply HeapObservations.SafePostExc.value hv (safe_value_mem hv hs)
    exact ⟨hb, fun r hr => hf ⟨i, r⟩ (hc.2 r hr)⟩

/-- **The stable-read node rule**'s candidates: a read of a traversed field
`f` of a tracked slot holding a position's entry value names the region
`(x, [f])`, for each such position. The node check verifies them. -/
def readOrigins (regions : List ArgumentStoreRegion) (facts : List ArgumentPathTracking.Fact) (t : Tm) :
    List ArgumentStoreRegion :=
  match t with
  | .readAt (.str f) (.var i) =>
    (facts.filter fun g => g.slot == i && g.region.path.isEmpty &&
      (ArgumentPathTracking.stableFields regions).contains (g.region.position, f)).map
      fun g => ⟨g.region.position, [f]⟩
  | _ => []

/-- A node's candidate origins: a copy's, and a stable read's. -/
def nodeOrigins (regions : List ArgumentStoreRegion) (facts : List ArgumentPathTracking.Fact) (t : Tm) :
    List ArgumentStoreRegion :=
  copyOrigins facts t ++ readOrigins regions facts t

@[nospecialize] def checkRead [DecidableEq ι] (G : NormalGraph ι) (c : NodeEvidence ι) (regions : List ArgumentStoreRegion)
    (facts : List ArgumentPathTracking.Fact) (t : Tm) (rs : List ArgumentStoreRegion) : Bool :=
  match t with
  | .readAt (.str f) (.var i) => decide (i < (entry c).length) && !rs.isEmpty &&
      (match (entry c)[i]? with
        | some A => HeapExpressionRules.fieldOperand (expand G A) (.str f)
        | none => false) &&
      rs.all fun r =>
        r.path == [f] && facts.contains ⟨i, ⟨r.position, []⟩⟩ &&
          (ArgumentPathTracking.stableFields regions).contains (r.position, f)
  | _ => false

/-- What a field read of an object whose field location holds `u` steps to. -/
private theorem read_step {h : Heap} {x : Val} {f : String} {u : Val}
    (hv : HeapKnowledge.readPath h x [f] = some u) : Step h (.readAt (.str f) x) h u := by
  cases x <;> simp [HeapKnowledge.readPath] at hv
  rename_i flds code oid
  cases hl : flds.lookup (.str f) with
  | none => simp [hl] at hv
  | some l =>
    cases hlv : h[l]? with
    | none => simp [hl, hlv] at hv
    | some w =>
      simp only [hl, hlv, Option.some.injEq] at hv
      subst hv
      exact (HeapFacts.ReadGave.present hl hlv).step

/-- A read of a traversed field of a tracked slot holding positions' entry
values reads the field's entry value (`read_now`): its result holds each
region `(x, [f])`'s entry value. -/
theorem checkRead_sound [DecidableEq ι] {G : NormalGraph ι} {Φ : Footprints.Closed}
    {regions : List ArgumentStoreRegion} {facts : List ArgumentPathTracking.Fact}
    {c : NodeEvidence ι} {t : Tm} {rs : List ArgumentStoreRegion} {thr : Bool} {F : List Nat}
    {Fs : List (Nat × String)}
    (hc : checkRead G c regions facts t rs = true) (ht : ExpressionOk G c t) :
    NodeWithin G Φ regions c t facts F Fs rs thr := by
  intro ε n W h ρ initial input hb hf _ _ he hi hk hw hh hst
  unfold checkRead at hc
  split at hc
  · rename_i f i
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq, List.contains_iff_mem,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
    obtain ⟨⟨⟨hlt, hne⟩, hfo⟩, hall⟩ := hc
    have hpresent : (Footprints.fieldsOf (ρ i)).lookup (.str f) ≠ none := by
      split at hfo
      · rename_i A hA
        obtain ⟨_, flds, code, oid, l, _, hobj, hl, -⟩ := HeapExpressionRules.fieldOperand_sound hfo (he.2 i A hA)
        simp [hobj, Footprints.fieldsOf, hl]
      · cases hfo
    have hs := HeapObservations.erase (HeapObservations.consequence
      (fun _ _ _ hu => hu.1) (fun _ _ h => h) (ht ε n W h ρ he hi hk hw hh))
    have hinst : instantiate 0 ρ (.readAt (.str f) (.var i)) = .readAt (.str f) (ρ i) := by
      simp [instantiate]
    rw [hinst] at hs ⊢
    cases n with
    | zero => trivial
    | succ n =>
      -- each origin reads, at the current heap, the value the read gives
      have hread : ∀ r ∈ rs, ∃ v, isVal v = true ∧
          HeapKnowledge.readPath initial (input r.position) r.path = some v ∧
          HeapKnowledge.readPath h (ρ i) [f] = some v := by
        intro r hr
        obtain ⟨⟨hpath, hfact⟩, hfld⟩ := hall r hr
        rw [hpath]
        exact ArgumentPathTracking.read_now hf hfact hfld (hst (Nat.succ_pos n)) (Nat.succ_pos n) hh hpresent
      obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil rs hne
      obtain ⟨u, hval, -, hu⟩ := hread r0 hr0
      have step := read_step hu
      rcases hs with (⟨hv0, _⟩ | hth) | ⟨U, h', t', hx', hU, st, hh', hs'⟩
      · simp [isVal] at hv0
      · exact absurd step hth.no_step
      · obtain ⟨rfl, rfl⟩ := Step_det st step
        refine .inr ⟨U, _, _, hx', hU, st, hh', ?_⟩
        cases n with
        | zero => trivial
        | succ m =>
          refine HeapObservations.SafePostExc.value hval (safe_value_mem hval hs') ⟨hb, fun r hr => ?_⟩
          obtain ⟨v, -, h₀v, hv⟩ := hread r hr
          rw [hu] at hv
          cases hv
          exact h₀v
  · cases hc

/-- All branch targets and handlers must justify their proposed facts. -/
@[nospecialize] def checkNode [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (ft : FreshTables) (exc : Bool)
    (l : Nat) (node : Node) (c : NodeEvidence ι) : Bool :=
  let facts := ArgumentPathTracking.atLabel table l
  let F := factsAt ft.values l
  let C := factsAt ft.cells l
  let Fs := fieldsAt ft.fields l
  let origins := nodeOrigins regions facts node.expression
  let thr := node.handler.isSome || exc
  fieldsKept G (entry c) Fs &&
    edgesFields ft.fields Fs (fieldOut ft.names F Fs node.expression) node.continuation &&
    (match node.handler with
      | some target => handlerFields ft.fields Fs target
      | none => true) &&
  ArgumentPathTracking.checkEdges table facts origins node.continuation &&
    ArgumentPathTracking.checkHandler table facts node.handler &&
    checkFresh G images sums Φ F C c node.expression node.handler.isSome &&
    edgesFresh ft.values F (freshOut G images sums F C c node.expression) false node.continuation &&
    edgesFresh ft.cells C (cellOut F C node.expression) false node.continuation &&
    (match node.handler with
      | some target => handlerFresh ft.values F target && handlerFresh ft.cells C target
      | none => true) &&
    match origins with
    | _ :: _ => checkCopy c facts node.expression origins || checkRead G c regions facts node.expression origins
    | [] => (stepEffects G images sums Φ c node.expression thr).any fun se => stepWithin Φ regions facts F Fs se thr

/-- The first node failing the same check used for certification. Its label
can be mapped through a source map by the declaration diagnostic. Shape and
entry failures belong to the enclosing declaration's diagnostic. -/
@[nospecialize] def firstRefusedNode [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (ft : FreshTables) (exc : Bool)
    (P : Program) (C : Certificate ι) : Option ((Node × NodeEvidence ι) × Nat) :=
  (P.zip C).zipIdx.find? fun ((node, c), l) => !checkNode G images sums Φ regions table ft exc l node c

theorem firstRefusedNode_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion}
    {table : List (List ArgumentPathTracking.Fact)} {ft : FreshTables} {exc : Bool}
    {P : Program} {C : Certificate ι} {node : Node} {c : NodeEvidence ι} {l : Nat}
    (hf : firstRefusedNode G images sums Φ regions table ft exc P C = some ((node, c), l)) :
    P[l]? = some node ∧ C[l]? = some c ∧
      checkNode G images sums Φ regions table ft exc l node c = false := by
  have hm := List.mem_of_find?_eq_some hf
  have hz := List.mem_zipIdx_iff_getElem?.mp hm
  have hc := List.getElem?_zip_eq_some.mp hz
  exact ⟨hc.1, hc.2, by simpa using (List.find?_some hf)⟩

/-- The table covers precisely the program and certificate being checked. -/
@[nospecialize] def checkNodes [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (ft : FreshTables) (exc : Bool)
    (P : Program) (C : Certificate ι) : Bool :=
  decide (P.length = C.length) && decide (table.length = P.length) &&
    (P.zip C).zipIdx.all fun ((node, c), l) => checkNode G images sums Φ regions table ft exc l node c

/-- Regional graph checking is independent of type-parameter assignment. -/
theorem checkNodes_reassign [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (η : MixedAssignment ι) (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion)
    (table : List (List ArgumentPathTracking.Fact)) (ft : FreshTables) (exc : Bool) (P : Program) (C : Certificate ι) :
    checkNodes (reassign G η) (images.reassign η) sums Φ regions table ft exc P C =
      checkNodes G images sums Φ regions table ft exc P C := by
  simp only [checkNodes, checkNode, stepEffects, callStep, checkClosedNode, checkRead, throwsWithin,
    checkFresh, cellsKept, freshOut, callFresh,
    Parametricity.checkTree_reassign, entryFacts_reassign, Parametricity.requiresTree_reassign,
    ExpressionEffects.emptyType]
  rfl

theorem checkNodes_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion} {table : List (List ArgumentPathTracking.Fact)}
    {ft : FreshTables} {exc : Bool} {Rty : Goal ι} {P : Program} {C : Certificate ι} {codes}
    (hg : checkGraphUsing (sums := sums) G images Rty P C codes = true)
    (hcodes : ProgramCertificates.CodesSound G codes)
    (hsums : ProgramCertificates.SummariesSound G images sums)
    (hc : checkNodes G images sums Φ regions table ft exc P C = true) :
    NodesWithin G Φ regions P C table ft exc := by
  intro l node c hn hcert
  simp only [checkNodes, Bool.and_eq_true] at hc
  have hz : (P.zip C)[l]? = some (node, c) := List.getElem?_zip_eq_some.mpr ⟨hn, hcert⟩
  have hm : ((node, c), l) ∈ (P.zip C).zipIdx := List.mem_zipIdx_iff_getElem?.mpr hz
  have hp := List.all_eq_true.mp hc.2 _ hm
  obtain ⟨actual, ha, ht, -⟩ := graph_node hg hcodes hsums hcert
  cases hn.symm.trans ha
  simp only [checkNode, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hkeep, hefl⟩, hhfl⟩, hedge⟩, hhandler⟩, hfresh⟩, hef⟩, hec⟩, hhf⟩, hp⟩ := hp
  have hscope : ProgramCertificates.checkScope (entry c).length node.expression = true := by
    have h0 := hfresh
    simp only [checkFresh, Bool.and_eq_true] at h0
    exact h0.1
  refine ⟨nodeOrigins regions (ArgumentPathTracking.atLabel table l) node.expression, _, _, _, ?_, hedge, hhandler,
    checkFresh_sound hfresh ht hsums, hef, hec, fieldsCheck_sound hkeep hscope ht, hefl, fun target htarget => ?_⟩
  rotate_right
  · rw [htarget] at hhf hhfl
    simp only [Bool.and_eq_true] at hhf
    exact ⟨hhf.1, hhf.2, hhfl⟩
  cases ho : nodeOrigins regions (ArgumentPathTracking.atLabel table l) node.expression with
  | cons r rs =>
    simp only [ho, Bool.or_eq_true] at hp ⊢
    rcases hp with hcopy | hread
    · exact checkCopy_sound hcopy ht
    · exact checkRead_sound hread ht
  | nil =>
    simp only [ho] at hp ⊢
    obtain ⟨se, hse, hwithin⟩ := List.any_eq_true.mp hp
    exact nodeWithin_of_step (stepEffects_ok hse ht hsums) hwithin

/-- Ordinary entry safety and regional obligations form one executable check. -/
@[nospecialize] def checkEntry [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (start : Nat) (inputs : List (Ty ι))
    (codes : CodeEntry ι → Bool) (table : List (List ArgumentPathTracking.Fact)) (ft : FreshTables) (exc : Bool)
    (entrySeparation : HeapSeparation.Separation := {}) (entryIndices : List HeapKnowledge.IndexAtom := []) : Bool :=
  checkEntryUsing (sums := sums) (entrySeparation := entrySeparation) (entryIndices := entryIndices)
    G images Rty P C start inputs codes &&
    ArgumentPathTracking.checkEntry (ArgumentPathTracking.atLabel table start) &&
    ((factsAt ft.values start).isEmpty && (factsAt ft.cells start).isEmpty) &&
    (fieldsAt ft.fields start).isEmpty &&
    ArgumentPathTracking.checkEntryFields G inputs regions &&
    checkNodes G images sums Φ regions table ft exc P C

theorem checkEntryFields_reassign [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)
    (inputs : List (Ty ι)) (regions : List ArgumentStoreRegion) :
    ArgumentPathTracking.checkEntryFields (reassign G η) inputs regions =
      ArgumentPathTracking.checkEntryFields G inputs regions := rfl

theorem checkEntry_reassign [DecidableEq ι] (G : NormalGraph ι)
    (images : InstanceImageCheck G) (sums : List (ProgramCertificates.ReadSummary ι))
    (η : MixedAssignment ι) (Φ : Footprints.Closed) (regions : List ArgumentStoreRegion) (Rty : Goal ι)
    (P : Program) (C : Certificate ι) (start : Nat) (inputs : List (Ty ι))
    (codes : CodeEntry ι → Bool) (table : List (List ArgumentPathTracking.Fact)) (ft : FreshTables) (exc : Bool)
    (entrySeparation : HeapSeparation.Separation) (entryIndices : List HeapKnowledge.IndexAtom) :
    checkEntry (reassign G η) (images.reassign η) sums Φ regions Rty P C start inputs codes table ft exc
      entrySeparation entryIndices =
    checkEntry G images sums Φ regions Rty P C start inputs codes table ft exc entrySeparation entryIndices := by
  simp only [checkEntry, Parametricity.checkEntry_reassign, checkNodes_reassign, checkEntryFields_reassign]

/-- Successful executable checking establishes the graph's regional bound.
There is no semantic node-obligation premise. -/
theorem checkEntry_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {sums : List (ProgramCertificates.ReadSummary ι)}
    {Φ : Footprints.Closed} {regions : List ArgumentStoreRegion} {Rty : Goal ι} {E K C start inputs codes}
    {table : List (List ArgumentPathTracking.Fact)} {ft : FreshTables} {exc : Bool}
    {entrySeparation : HeapSeparation.Separation} {entryIndices : List HeapKnowledge.IndexAtom}
    (hc : checkEntry G images sums Φ regions Rty (program E K) C start inputs codes table ft exc
      entrySeparation entryIndices = true)
    (hcodes : ProgramCertificates.CodesSound G codes)
    (hsums : ProgramCertificates.SummariesSound G images sums)
    (n W h L d) (he : EnvOk G inputs (envOf L d) n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hsep : HeapSeparation.Holds entrySeparation (envOf L d))
    (hidx : HeapKnowledge.IndexHolds ⟨envOf L d, h⟩ entryIndices (envOf L d) h) :
    HeapObservations.SafePostExc (excOf G) (GoalHolds G Rty (Rty.argument (envOf L d)))
      (fun h' _ => ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      (fun h' => exc = true → ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      n W h (.goto E K start L d) := by
  simp only [checkEntry, Bool.and_eq_true] at hc
  have hg := hc.1.1.1.1.1
  simp only [checkEntryUsing_eq, Bool.and_eq_true] at hg
  exact goto_bounded hc.1.1.1.1.1 hcodes hsums
    (checkNodes_sound hg.1 hcodes hsums hc.2) hc.1.1.1.1.2 (by simpa only [Bool.and_eq_true] using hc.1.1.1.2)
    hc.1.1.2 hc.1.2 n W h L d he hw hh hsep hidx

end Verification.GraphCode.ArgumentRegionGraph
