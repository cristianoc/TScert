import Verification.Programs.TolerantFramesSelect

/-! # Tolerant frames: the pass's footprint check at a node

Where an invocation states a bound `Φ` (`SinglePass.lean` 1342–1380), the
pass checks each node: its normal exit within `Φ` (`within`: an inspection,
a write the bound admits (`writes`), a call at a selected signature within
the bound (`GraphCode.selectedWithinAt` on the step's derivation), or a type
no value has), and its throw where a live handler or the bound's `onThrow`
needs it (`throws`). This module states what that check gives:

- `pass_within_normal`, `pass_within_throw`: the node's run is within `Φ` on
  the locations below `b` from the node's entry heap, the slots `F` holding
  stores allocated at or after `b`; with `Closed.Holds.trans_on`, within `Φ`
  from the invocation's entry `h₀` where `b = |h₀|` (`pass_within_entry`);
- `pass_write_judgment`: where `writes` holds, the step's judgment within
  `Φ` on the whole heap, both exits, with its rule's output, the form
  `write_judgment` states for `writeWithin`.

The call case reads the step's derivation `d`, which the footprint check
does not check: `DerivChecked` (its claim at the node's context and term, its
tree accepted) is a premise. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations

section Footprint
variable {ι : Type} [DecidableEq ι]
open ProgramTyping PositiveCertificates ProgramCertificates PositiveGraphs PositiveRules HeapExpressionRules

/-! ## The pass's conditions -/

/-- The pass's `writes` (`SinglePass.lean` 1356–1357), at the step's knowledge
`kS` (`stepK`). -/
def passWrites (G : NormalGraph ι) (Γ : List (Ty ι)) (kS : HeapKnowledge.Knowledge) (Φ : Footprints.Closed)
    (t : Tm) : Bool :=
  ExpressionEffects.writeWithin G Γ Φ t || ExpressionEffects.initWriteWithin G Γ kS Φ t

/-- The pass's `within` (lines 1358–1360) at the node's sequent `j`, the
step's derivation `d` (`stepDeriv`) and the fresh receiver slots `F`. -/
def passWithin (G : NormalGraph ι) (j : Sequent ι) (kS : HeapKnowledge.Knowledge) (Φ : Footprints.Closed)
    (F : List Nat) (d : ProgramCertificates.Evidence ι) : Bool :=
  ExpressionEffects.check G j.context j.term || passWrites G j.context kS Φ j.term ||
    GraphCode.selectedWithinAt Φ F d || ExpressionEffects.emptyType G j.type ||
    j.context.any (ExpressionEffects.emptyType G ·)

/-- The pass's `throws` (lines 1367–1371) but its first disjunct, which
discharges no throw: the throw bounded by an inspection, a write, a selected
call stating `onThrow`, or an unreachable node. -/
def passThrows (G : NormalGraph ι) (j : Sequent ι) (kS : HeapKnowledge.Knowledge) (Φ : Footprints.Closed)
    (F : List Nat) (d : ProgramCertificates.Evidence ι) : Bool :=
  ExpressionEffects.check G j.context j.term || passWrites G j.context kS Φ j.term ||
    (GraphCode.selectedWithinAt Φ F d && ExpressionEffects.selectedThrows d &&
      (match ExpressionEffects.selectedEffect d with | some eff => eff.onThrow | none => false)) ||
    j.context.any (ExpressionEffects.emptyType G ·)

/-- The step's derivation checked at the node: claimed at the node's context
and term, its tree accepted with the codes or by `requiresTree` at `k`. The
pass checks this only where `d` is the tree it checks (`passTree`). -/
def DerivChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (k : HeapKnowledge.Knowledge) (j : Sequent ι)
    (d : ProgramCertificates.Evidence ι) : Prop :=
  (claim d).context = j.context ∧ (claim d).term = j.term ∧
    (checkTreeUsing G images d codes sums || PromiseCalls.requiresTree G images k codes sums d) = true

/-- **Where the step's derivation is the tree the pass checks**, it is
checked at the node: `select`'s metadata claims it at the node's context
and term, and the pass's tree check accepted it. -/
theorem derivChecked_of_select {G : NormalGraph ι} {images : InstanceImageCheck G} {j : Sequent ι}
    {k out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool} {sums : List (ReadSummary ι)}
    {d : ProgramCertificates.Evidence ι}
    (hok : passTreeOk G images k codes sums e = true)
    (hc : (checkStepResult G images j k e codes sums (tree := false)).value = some out)
    (hd : passTree e = some d) : DerivChecked G images codes sums k j d :=
  ⟨(select_claim_term hc hd).1, (select_claim_term hc hd).2, by simpa [passTreeOk, hd] using hok⟩

/-! ## What the check gives -/

theorem passWrites_sound {G : NormalGraph ι} {Γ : List (Ty ι)} {kS : HeapKnowledge.Knowledge}
    {Φ : Footprints.Closed} {t : Tm} {T : Fam} {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (hc : passWrites G Γ kS Φ t = true) (he : EnvOk G Γ ρ n W) (hh : HeapOk n W h)
    (hkS : HeapKnowledge.Holds kS ρ h) (hs : Safe (excOf G) T n W h (instantiate 0 ρ t)) :
    SafePostExc (excOf G) T (fun h' _ => Φ.Holds h h') (fun h' => Φ.Holds h h') n W h (instantiate 0 ρ t) := by
  simp only [passWrites, Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · exact ExpressionEffects.write_within_exc hc he hh hs
  · exact ExpressionEffects.init_write_within_exc hc he hh hkS hs

/-- A selected call's `within`, its receiver's store fresh where the
signature excepts it, bounds the heap by `Φ` on the locations below `b`
(the case analysis of `GraphCode.nodePost_of_checked`). -/
theorem selected_within_on {Φ : Footprints.Closed} {F : List Nat} {b : Nat} {ρ : Env} {t : Tm}
    {eff : CallEffects.Effect} {h h' : Heap} (hF : GraphCode.FreshOk F b ρ)
    (hle : eff.footprint.le Φ = true)
    (hr : (if eff.receiverOwn then eff.ownChange.le Φ else
        (!eff.receiverStore || Φ == .top || GraphCode.receiverFresh F t)) = true)
    (hq : eff.within (ExpressionEffects.receiverOf (instantiate 0 ρ t)) (ExpressionEffects.actualsOf (instantiate 0 ρ t))
      h h') :
    Φ.HoldsOn (· < b) h h' := by
  split at hr
  · rename_i ho
    exact ((CallEffects.Effect.within_own hq ho).mono hr).on _
  rename_i ho
  simp only [Bool.not_eq_true] at ho
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hr
  rcases hr with (hr | hr) | hr
  · exact ((CallEffects.Effect.within_holds hq hr ho).mono hle).on _
  · rw [hr]; exact (CallEffects.Effect.within_top hq).on _
  · exact (CallEffects.Effect.within_below hq (fun _ => GraphCode.receiverFresh_sound hr hF)
      (fun h => by rw [ho] at h; cases h)).mono hle

/-- **The pass's `within` bounds the node's normal exit** by `Φ` on the
locations below `b`, from the node's entry heap. -/
theorem pass_within_normal {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {j : Sequent ι} {k kS : HeapKnowledge.Knowledge} {Φ : Footprints.Closed}
    {F : List Nat} {d : ProgramCertificates.Evidence ι}
    (hwi : passWithin G j kS Φ F d = true)
    (hd : GraphCode.selectedWithinAt Φ F d = true → DerivChecked G images codes sums k j d)
    (hscope : checkScope j.context.length j.term = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} {b : Nat} (hF : GraphCode.FreshOk F b ρ)
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hkS : HeapKnowledge.Holds kS ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (hsafe : Safe (excOf G) (meaning G j.type) n W h (instantiate 0 ρ j.term)) :
    SafePost (excOf G) (meaning G j.type) (fun h' _ => Φ.HoldsOn (· < b) h h') n W h (instantiate 0 ρ j.term) := by
  simp only [passWithin, Bool.or_eq_true] at hwi
  rcases hwi with (((hexpr | hwrite) | hcall) | hempty) | hctx
  · exact weaken (fun _ _ hq => (Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _) hq).on _)
      (ExpressionEffects.sound hexpr hscope he hw hh hsafe)
  · exact weaken (fun _ _ hq => hq.on _) (SafePostExc.post (passWrites_sound hwrite he hh hkS hsafe))
  · obtain ⟨hctx, hterm, htree⟩ := hd hcall
    have hsel := hcall
    simp only [GraphCode.selectedWithinAt, Bool.and_eq_true] at hsel
    obtain ⟨hops, hsel⟩ := hsel
    split at hsel
    · rename_i eff heff
      simp only [Bool.and_eq_true] at hsel
      obtain ⟨hle, hr⟩ := hsel
      have hs : SafePost (excOf G) (meaning G (claim d).type)
          (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (claim d).term))
            (ExpressionEffects.actualsOf (instantiate 0 ρ (claim d).term)) h) n W h
          (instantiate 0 ρ (claim d).term) := by
        rcases Bool.or_eq_true_iff.mp htree with htree | hreq
        · exact ExpressionEffects.selected_sound d htree hops heff hcodes hsums (hctx ▸ he) hw hh
        · obtain ⟨eff', heff', hs⟩ := PromiseCalls.requiresTree_sound hcodes hsums d hreq
          rw [heff] at heff'
          cases heff'
          exact hs (hctx ▸ he) hk hw hh
      rw [hterm] at hs
      have hboth := cross_upto n (fun _ _ _ _ _ _ _ _ hb _ => hb) W W h _ hh hh
        (of_value_property (Q := fun _ _ => True) (fun _ _ _ _ _ => trivial) hsafe) hs
      exact weaken (fun _ _ hq => selected_within_on hF hle (hterm ▸ hr) hq.2.1) hboth
    · cases hsel
  · exact ExpressionEffects.noReturn_sound hempty hsafe
  · obtain ⟨A, hA, hnil⟩ := List.any_eq_true.mp hctx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hA
    exact (ExpressionEffects.emptyType_sound hnil (he.2 i A hi)).elim

/-- **The pass's `throws` bounds the node's throw** by `Φ` on the locations
below `b`, from the node's entry heap. -/
theorem pass_within_throw {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {j : Sequent ι} {k kS : HeapKnowledge.Knowledge} {Φ : Footprints.Closed}
    {F : List Nat} {d : ProgramCertificates.Evidence ι}
    (hth : passThrows G j kS Φ F d = true)
    (hd : GraphCode.selectedWithinAt Φ F d = true → DerivChecked G images codes sums k j d)
    (hscope : checkScope j.context.length j.term = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap} {b : Nat} (hF : GraphCode.FreshOk F b ρ)
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hkS : HeapKnowledge.Holds kS ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (hsafe : Safe (excOf G) (meaning G j.type) n W h (instantiate 0 ρ j.term)) :
    SafePostExc (excOf G) (meaning G j.type) (fun _ _ => True) (fun h' => Φ.HoldsOn (· < b) h h') n W h
      (instantiate 0 ρ j.term) := by
  simp only [passThrows, Bool.or_eq_true] at hth
  rcases hth with ((hexpr | hwrite) | hcall) | hctx
  · exact SafePostExc.weaken (fun _ _ _ => trivial)
      (fun _ hq => (Footprints.Closed.Holds.mono (Footprints.Closed.empty_le _) hq).on _)
      (ExpressionEffects.sound_exc hexpr hscope he hw hh hsafe)
  · exact SafePostExc.weaken (fun _ _ _ => trivial) (fun _ hq => hq.on _) (passWrites_sound hwrite he hh hkS hsafe)
  · simp only [Bool.and_eq_true] at hcall
    obtain ⟨⟨hsw, hthr⟩, hon⟩ := hcall
    obtain ⟨hctx, hterm, htree⟩ := hd hsw
    have hsel := hsw
    simp only [GraphCode.selectedWithinAt, Bool.and_eq_true] at hsel
    obtain ⟨hops, hsel⟩ := hsel
    split at hsel
    · rename_i eff heff
      rw [heff] at hon
      simp only at hon
      simp only [Bool.and_eq_true] at hsel
      obtain ⟨hle, hr⟩ := hsel
      have hs : SafePostExc (excOf G) (meaning G (claim d).type)
          (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (claim d).term))
            (ExpressionEffects.actualsOf (instantiate 0 ρ (claim d).term)) h)
          (eff.excPost (ExpressionEffects.receiverOf (instantiate 0 ρ (claim d).term))
            (ExpressionEffects.actualsOf (instantiate 0 ρ (claim d).term)) h) n W h
          (instantiate 0 ρ (claim d).term) := by
        rcases Bool.or_eq_true_iff.mp htree with htree | hreq
        · exact ExpressionEffects.selected_sound_exc d htree hops hthr heff hcodes hsums (hctx ▸ he) hw hh
        · obtain ⟨eff', heff', hs⟩ := PromiseCalls.requiresTree_sound_exc hcodes hsums d hreq
          rw [heff] at heff'
          cases heff'
          exact hs (hctx ▸ he) hk hw hh
      rw [hterm] at hs
      have hboth := SafePostExc.cross_upto n (fun _ _ _ _ _ _ _ _ hb _ => hb) W W h _ hh hh
        (SafePostExc.of_post (R := fun _ => True) (fun _ => trivial)
          (of_value_property (Q := fun _ _ => True) (fun _ _ _ _ _ => trivial) hsafe)) hs
      exact SafePostExc.weaken (fun _ _ _ => trivial)
        (fun _ hq => selected_within_on hF hle (hterm ▸ hr) (hq.2 hon)) hboth
    · cases hsel
  · obtain ⟨A, hA, hnil⟩ := List.any_eq_true.mp hctx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hA
    exact (ExpressionEffects.emptyType_sound hnil (he.2 i A hi)).elim

/-- **Relative to the invocation's entry**: a run within `Φ` from the
invocation's entry `h₀` to the node's entry, then within `Φ` on the
locations below `|h₀|`, is within `Φ` from `h₀`. -/
theorem pass_within_entry {Φ : Footprints.Closed} {h₀ h h' : Heap} (h₁ : Φ.Holds h₀ h)
    (h₂ : Φ.HoldsOn (· < h₀.length) h h') : Φ.Holds h₀ h' :=
  Footprints.Closed.Holds.trans_on h₁ h₂

/-- **A write the pass's `writes` admits, with its rule's output**: the
judgment within `Φ` on the whole heap, both exits (`write_judgment` at the
invocation's bound, the initialisation write included). -/
theorem pass_write_judgment {G : NormalGraph ι} {images : InstanceImageCheck G} (checker : Checker G images)
    {j : Sequent ι} {k kS out : HeapKnowledge.Knowledge} {e : StepEvidence ι} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} (hr : (checker.run j k e codes sums).value = some out)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums) {Φ : Footprints.Closed}
    (hc : passWrites G j.context kS Φ j.term = true)
    {ρ : Env} {n : Nat} {W : WorldT n} {h : Heap}
    (he : EnvOk G j.context ρ n W) (hk : HeapKnowledge.Holds k ρ h) (hkS : HeapKnowledge.Holds kS ρ h)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePostExc (excOf G) (meaning G j.type) (fun h' v => Φ.Holds h h' ∧ HeapKnowledge.Holds out (push v ρ) h')
      (fun h' => Φ.Holds h h' ∧ True) n W h (instantiate 0 ρ j.term) :=
  judgment_with_output checker hr hcodes hsums he hk hw hh
    (passWrites_sound hc he hh hkS (erase (checker.sound hr hcodes hsums he hk hw hh)))

end Footprint

end Verification.TolerantFrames
