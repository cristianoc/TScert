import Verification.Programs.TolerantFramesNodeBound

/-! # Tolerant frames: a call's fresh result behind its derivation's check

`run` reads a fresh result off the step's derivation (`outFresh`'s call
disjunct, `passCallFresh`: the selected effect states a fresh result, its
operands selected, claimed at the node's term) without checking that
derivation's tree there; `CallFreshOk` (Leg 14b) is the named hypothesis
standing for it. Pass change D4 puts that disjunct behind the derivation's
check (`passDerivChecked`, as `footprintCheck`'s `derivChecked`):
`passOutFreshChecked` mirrors it. `callFresh_of_checked` proves the
checked disjunct gives every run of the node's term to a value within the
state's budget a store allocated at or past the mark (`CallFreshBelow`),
the form `footprintKept_of` consumes, whose run is within the budget
(`EvalKeeps`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section CallFresh
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

/-- `run`'s `outFresh` with the call disjunct behind the derivation's
check (pass change D4): a copy of a slot holding a fresh name, or a call
stating a fresh result whose derivation `passDerivChecked` accepts at the
step's knowledge `kS` and the node's sequent `j`. -/
def passOutFreshChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (kS : HeapKnowledge.Knowledge) (j : Sequent ι) (node : Node)
    (entry : SinglePass.State) (deriv : ProgramCertificates.Evidence ι) : Bool :=
  (match node.expression with
    | .var i => (entry.names[i]?).any entry.fresh.contains
    | _ => false) || (passCallFresh node deriv && passDerivChecked G images codes sums kS j deriv)

omit [Hashable ι] [Instantiates ι] in
theorem passOutFresh_of_checked {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {kS : HeapKnowledge.Knowledge} {j : Sequent ι} {node : Node}
    {entry : SinglePass.State} {deriv : ProgramCertificates.Evidence ι}
    (h : passOutFreshChecked G images codes sums kS j node entry deriv = true) :
    passOutFresh node entry deriv = true := by
  simp only [passOutFreshChecked, Bool.or_eq_true, Bool.and_eq_true] at h
  simp only [passOutFresh, Bool.or_eq_true]
  exact h.imp id (·.1)

/-- **A call's fresh result within the budget**: from a state where the
node assertion holds, every run of the node's term with fewer steps than
the state's budget to a value returns a store allocated at or past the
mark. -/
def CallFreshBelow (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (ctx : Nat → List (Ty ι)) (m l : Nat) (node : Node) (deriv : ProgramCertificates.Evidence ι) : Prop :=
  passCallFresh node deriv = true → ∀ ρ (s : IndexedHeap), passPreT G w startNames ρ0 ctx l ρ m s →
    ∀ k h' v, k < s.n → Steps k s.h (instantiate 0 ρ node.expression) h' v → isVal v = true → FreshAt m v

omit [Hashable ι] [Instantiates ι] in
/-- **The checked call disjunct gives a fresh result** (what D4 makes
provable): where the selected effect states a fresh result
(`passCallFresh`) and `passDerivChecked` accepts the derivation at the
node's term and context (its tree, or `requiresTree` at the step's
knowledge, which holds), every run of the node's term to a value within
the budget returns a store allocated at or past the heap's length, hence
at or past any mark below it. -/
theorem callFresh_of_checked {G : NormalGraph ι} {images : InstanceImageCheck G} {codes : CodeEntry ι → Bool}
    {sums : List (ReadSummary ι)} {kS : HeapKnowledge.Knowledge} {c : PointClaim ι} {node : Node}
    {d : ProgramCertificates.Evidence ι}
    (hcf : passCallFresh node d = true)
    (hdc : passDerivChecked G images codes sums kS ⟨c.context, node.expression, c.type⟩ d = true)
    (hcodes : CodesSound G codes) (hsums : SummariesSound G images sums)
    {ρ : Env} {s : IndexedHeap} {m : Nat} (hm : m ≤ s.h.length)
    (he : EnvOk G c.context ρ s.n s.W) (hkS : HeapKnowledge.Holds kS ρ s.h) :
    ∀ k h' v, k < s.n → Steps k s.h (instantiate 0 ρ node.expression) h' v → isVal v = true → FreshAt m v := by
  simp only [passCallFresh, Bool.and_eq_true, beq_iff_eq] at hcf
  obtain ⟨⟨hfr, hops⟩, hterm⟩ := hcf
  simp only [passDerivChecked, Bool.and_eq_true, beq_iff_eq] at hdc
  obtain ⟨⟨-, hctx⟩, htree⟩ := hdc
  cases heff : ExpressionEffects.selectedEffect d with
  | none => rw [heff] at hfr; cases hfr
  | some eff =>
    rw [heff] at hfr
    simp only at hfr
    have hs : SafePost (excOf G) (meaning G (claim d).type)
        (eff.post (ExpressionEffects.receiverOf (instantiate 0 ρ (claim d).term))
          (ExpressionEffects.actualsOf (instantiate 0 ρ (claim d).term)) s.h) s.n s.W s.h
        (instantiate 0 ρ (claim d).term) := by
      rcases Bool.or_eq_true_iff.mp htree with htree | hreq
      · exact ExpressionEffects.selected_sound d htree hops heff hcodes hsums (hctx ▸ he) s.adm s.ok
      · obtain ⟨eff', heff', hs⟩ := PromiseCalls.requiresTree_sound hcodes hsums d hreq
        rw [heff] at heff'
        cases heff'
        exact hs (hctx ▸ he) hkS s.adm s.ok
    rw [hterm] at hs
    intro k h' v hk hst hv
    have hpost := GraphCode.returnsPost_of_safePost hs k h' v hk hst hv
    exact FreshAt.lower hm (hpost.2.1 hfr)

end CallFresh

end Verification.TolerantFrames
