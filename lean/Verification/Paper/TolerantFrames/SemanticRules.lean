import Verification.Paper.TolerantFrames.ParityAssertions
import Verification.Semantics.ExitWorlds
import Verification.Semantics.Support

/-! # Semantic premises of Tolerant frames

The existing mechanisms extended here are `TolerantFrames.Box` and
`SupportDomain.Supports`. These statements quantify over arbitrary assertions,
not the finite assertion arena or the search/checker certificates. In particular
semantic respect (Definition 12) is distinct from its sufficient Boolean check.
No change to the shared semantics or the running verifier is made here.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints
open Verification.TolerantFrames

/-- The environment and mark part of a paper state (Definition 5), alongside
the shared indexed heap. The surrounding type system supplies variable types. -/
def ValidContext (ρ : Env) (m : Nat) (s : IndexedHeap) : Prop :=
  RootsOk s.W ρ ∧ (∀ x, isSourceVal (ρ x) = true) ∧ m ≤ s.h.length

theorem ValidContext.admissible {ρ m s t} (hv : ValidContext ρ m s) (ha : Admissible s t) :
    ValidContext ρ m t := ⟨Verification.RootsOk.admissible ha hv.1, hv.2.1, Nat.le_trans hv.2.2 ha.length_le⟩

/-- Entailment on the well-formed states of the paper. -/
def EntailsOn (F G : Assertion) : Prop := ∀ ρ m s, ValidContext ρ m s → F ρ m s → G ρ m s

/-- The shared domain of well-formed indexed heaps. Environment validity is
an additional premise of results that follow references from roots. -/
def domain : SupportDomain IndexedHeap := ⟨IndexedHeap.h, Admissible⟩

/-- Definition 11, including its condition on transitions. -/
abbrev Supports (C : ConditionOn IndexedHeap) (F : Assertion) (S : Footprint) : Prop :=
  domain.Supports (fun ρ m s t => ValidContext ρ m s ∧ C ρ m s t) F S

/-- Definition 12: every action from K meets every support constraint. This
is a semantic property, not the pairwise sufficient decision procedure. -/
def Respects (K : Assertion) (Φ S : Footprint) : Prop :=
  ∀ ρ m s s', ValidContext ρ m s → K ρ m s → Action Φ ρ s s' → Supported S ρ s.h s'.h

/-- The pairwise check is sufficient for semantic respect. -/
theorem respects_of_check {K : Assertion} {Φ S : Footprint} {q : SepQuery}
    (hc : respects q S Φ = true)
    (hq : ∀ ρ m s, ValidContext ρ m s → K ρ m s → q.Sound ρ s.h) : Respects K Φ S :=
  fun ρ m s _ hv hK ha => respect_sound hc (hq ρ m s hv hK) ha.2

/-- Theorem 13 with precisely semantic support, respect, and the condition
on all actions. No certificate or search completeness premise is involved. -/
theorem tolerant_frame {K F : Assertion} {Φ S : Footprint} {C : ConditionOn IndexedHeap}
    (hs : Supports C F S) (hr : Respects K Φ S)
    (hc : ∀ ρ m s s', ValidContext ρ m s → K ρ m s → Action Φ ρ s s' → C ρ m s s') :
    EntailsOn (fun ρ m s => K ρ m s ∧ F ρ m s) (Box Φ F) :=
  fun ρ m s hv ⟨hK, hF⟩ s' ha => hs ρ m s s' ha.1 ⟨hv, hc ρ m s s' hv hK ha⟩ hF (hr ρ m s s' hv hK ha)

/-- Unconditional support is the special case C = true. -/
theorem tolerant_frame_unconditional {K F : Assertion} {Φ S : Footprint}
    (hs : Supports (fun _ _ _ _ => True) F S) (hr : Respects K Φ S) :
    EntailsOn (fun ρ m s => K ρ m s ∧ F ρ m s) (Box Φ F) :=
  tolerant_frame hs hr (fun _ _ _ _ _ _ _ => trivial)

/-- Structural supports of arbitrary disjunctions, without invariant guards. -/
theorem supports_or {C : ConditionOn IndexedHeap} {F G : Assertion} {S T : Footprint}
    (hF : Supports C F S) (hG : Supports C G T) :
    Supports C (fun ρ m s => F ρ m s ∨ G ρ m s) (S ++ T) := hF.or hG

/-- Structural supports of conjunctions. -/
theorem supports_and {C : ConditionOn IndexedHeap} {F G : Assertion} {S T : Footprint}
    (hF : Supports C F S) (hG : Supports C G T) :
    Supports C (fun ρ m s => F ρ m s ∧ G ρ m s) (S ++ T) := hF.and hG

/-- Remark 8: stable under the action of Φ. -/
def Stable (Φ : Footprint) (F : Assertion) : Prop :=
  ∀ ρ m s s', Action Φ ρ s s' → F ρ m s → F ρ m s'

/-- For rigid Φ the box is stable, by transitivity of its action. -/
theorem box_stable {Φ : Footprint} {F : Assertion} (hr : ∀ ρ, Rigid Φ ρ) : Stable Φ (Box Φ F) :=
  fun ρ _ s s' ha hb s'' ha' => hb s'' (hr ρ s s' s'' ha ha')

/-- Remark 8's weakest stable strengthening characterization. It also states
that the box strengthens F. The competing G ranges over all assertions. -/
theorem box_weakest_stable {Φ : Footprint} {F : Assertion} (hr : ∀ ρ, Rigid Φ ρ) :
    Entails (Box Φ F) F ∧ Stable Φ (Box Φ F) ∧
      ∀ G : Assertion, Entails G F → Stable Φ G → Entails G (Box Φ F) := by
  refine ⟨fun _ _ _ hb => box_elim hb, box_stable hr, ?_⟩
  intro G hGF hG ρ m s hg s' ha
  exact hGF ρ m s' (hG ρ m s s' ha hg)

/-- Rigidity on the well-formed contexts of the paper. -/
def RigidOn (Φ : Footprint) : Prop :=
  ∀ ρ m s t u, ValidContext ρ m s → Action Φ ρ s t → Action Φ ρ t u → Action Φ ρ s u

/-- Invariance on precisely the paper's contexts. -/
def InvariantOn (F : Assertion) : Prop :=
  ∀ ρ m s t, ValidContext ρ m s → Admissible s t → F ρ m s → F ρ m t

/-- Law 9(b), with arbitrary semantic entailment on well-formed contexts. -/
theorem box_mono_on {Φ : Footprint} {F G : Assertion} (hfg : EntailsOn F G) :
    EntailsOn (Box Φ F) (Box Φ G) :=
  fun ρ m _ hv hb t ha => hfg ρ m t (hv.admissible ha.1) (hb t ha)

/-- Law 9(d) needs semantic invariance, not a recognized invariant guard. -/
theorem box_or_on {Φ : Footprint} {F G : Assertion} (hg : InvariantOn G) :
    EntailsOn (fun ρ m s => G ρ m s ∨ Box Φ F ρ m s)
      (Box Φ (fun ρ m s => G ρ m s ∨ F ρ m s)) := by
  intro ρ m s hv hb t ha
  rcases hb with hG | hF
  · exact .inl (hg ρ m s t hv ha.1 hG)
  · exact .inr (hF t ha)

/-- Law 9(e) at semantic rigidity on the valid contexts. -/
theorem box_idem_on {Φ : Footprint} {F : Assertion} (hr : RigidOn Φ) :
    EntailsOn (Box Φ F) (Box Φ (Box Φ F)) :=
  fun ρ m s hv hb t ha u hau => hb u (hr ρ m s t u hv ha hau)

/-- Stability quantified only over well-formed paper contexts. -/
def StableOn (Φ : Footprint) (F : Assertion) : Prop :=
  ∀ ρ m s t, ValidContext ρ m s → Action Φ ρ s t → F ρ m s → F ρ m t

/-- Remark 8 on precisely the paper's valid contexts. A competing stable
strengthening need not satisfy any property at an invalid environment. -/
theorem box_weakest_stable_on {Φ : Footprint} {F : Assertion} (hr : RigidOn Φ) :
    EntailsOn (Box Φ F) F ∧ StableOn Φ (Box Φ F) ∧
      ∀ G : Assertion, EntailsOn G F → StableOn Φ G → EntailsOn G (Box Φ F) := by
  refine ⟨fun _ _ _ _ hb => box_elim hb, fun ρ m s t hv ha hb u hau => hb u (hr ρ m s t u hv ha hau), ?_⟩
  intro G hGF hG ρ m s hv hg t ha
  exact hGF ρ m t (hv.admissible ha.1) (hG ρ m s t hv ha hg)

/-- The weakest liberal precondition of a single arbitrary Φ action. -/
def HavocWlp (Φ : Footprint) (F : Assertion) : Assertion :=
  fun ρ m s => ∀ s', Action Φ ρ s s' → F ρ m s'

theorem box_eq_havoc_wlp (Φ : Footprint) (F : Assertion) : Box Φ F = HavocWlp Φ F := rfl

/-- Freshness of any region, rather than only of an array spine. -/
def Fresh (r : Region) : Assertion :=
  fun ρ m s => ∀ l, r.mem ρ s.h l = true → m ≤ l

/-- A region denotes only locations that existed at invocation entry. -/
def BelowMark (r : Region) : Assertion :=
  fun ρ m s => ∀ l, r.mem ρ s.h l = true → l < m

/-- The freshness disjointness rule of Definition 23, for arbitrary regions. -/
theorem fresh_disjoint_below {r t : Region} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hf : Fresh r ρ m s) (hb : BelowMark t ρ m s) :
    ∀ l, r.mem ρ s.h l = true → t.mem ρ s.h l = true → False := by
  intro l hr ht
  exact Nat.not_lt_of_ge (hf l hr) (hb l ht)

/-- Proposition 19: a sequence of actions of a rigid effect is bounded by
that effect. The list records every prefix endpoint, including callbacks. -/
inductive ActionChain (Φ : Footprint) (ρ : Env) : IndexedHeap → IndexedHeap → Prop where
  | refl (s) : ActionChain Φ ρ s s
  | step {s t u} : ActionChain Φ ρ s t → Action Φ ρ t u → ActionChain Φ ρ s u

theorem ActionChain.action {Φ : Footprint} {ρ : Env} (hr : Rigid Φ ρ)
    {s t : IndexedHeap} (h : ActionChain Φ ρ s t) : Action Φ ρ s t := by
  induction h with
  | refl => exact Action.refl _ _ _
  | step _ ha ih => exact hr _ _ _ ih ha

/-- Every chosen prefix retains F, from the full modal premise of Reliance. -/
theorem reliance {Φ : Footprint} {ρ : Env} {m : Nat} {F : Assertion} {s t : IndexedHeap}
    (hr : Rigid Φ ρ) (hb : Box Φ F ρ m s) (h : ActionChain Φ ρ s t) : F ρ m t :=
  hb t (h.action hr)

/-- A rigid action bounds every prefix without requiring anything at invalid
roots. This is the paper's Reliance at its full modal premise. -/
theorem ActionChain.action_on {Φ : Footprint} {ρ : Env} {m : Nat} (hr : RigidOn Φ)
    {s t : IndexedHeap} (hv : ValidContext ρ m s) (h : ActionChain Φ ρ s t) : Action Φ ρ s t := by
  induction h with
  | refl => exact Action.refl _ _ _
  | step _ ha ih => exact hr ρ m _ _ _ hv ih ha

theorem reliance_on {Φ : Footprint} {ρ : Env} {m : Nat} {F : Assertion} {s t : IndexedHeap}
    (hr : RigidOn Φ) (hv : ValidContext ρ m s) (hb : Box Φ F ρ m s) (h : ActionChain Φ ρ s t) : F ρ m t :=
  hb t (h.action_on hr hv)

end Verification.Paper.TolerantFrames

namespace Verification.CallEffects
open Verification Footprints Parity TolerantFrames HeapObservations

/-- Conj of the paper. Result-family compatibility is discharged by retaining
B, the first derivation's family. The paper combines postconditions and does
not ask for an independently chosen result family D. Reduction determinism
and independence transport are supplied by `cross_independent`. -/
theorem SafePostExcV.conj_independent {Ξ B C : Fam} {Q Q' : WPost} {R R' : WExcV}
    (s : IndexedHeap) (hq : IndependentFrom s Q') (hr : IndependentFrom s R') {t : Tm}
    (ha : SafePostExcV Ξ B Q R s.n s.W s.h t)
    (hb : SafePostExcV Ξ C Q' R' s.n s.W s.h t) :
    SafePostExcV Ξ B (fun k W h v => Q k W h v ∧ Q' k W h v)
      (fun k W h v => R k W h v ∧ R' k W h v) s.n s.W s.h t :=
  SafePostExcV.cross_independent s (fun _ _ _ _ _ _ _ _ hB _ => hB) hq hr ha hb

end Verification.CallEffects
