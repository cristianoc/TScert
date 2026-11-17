import Verification.Programs.SinglePass.GraphSafety

/-! # Tolerant frames: transfer along an exit

A node's local safety, its exit footprints and posts, and the retained index
facts under the modality of each exit's footprint, transported to every
target environment, give the node's exit obligations, which `graph_safe`
composes (`transfer`). -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations
open ControlFlow PointClaims

/-! ## Transfer along an exit -/

open HeapKnowledge in
/-- The retained index facts `K`, read at `ρ`, hold at every target
environment `ρ'` under every renaming `g` that maps each slot they name to a
slot of `ρ'` holding the same value. -/
def Transported (ε : EntryState) (K : List IndexFact) (ρ ρ' : Env) (h : Heap) : Prop :=
  ∀ F ∈ K, ∀ (g : Nat → Option Nat) (F' : IndexFact), F.mapM g = some F' →
    (∀ i ∈ F.slots, ∀ j, g i = some j → ρ' j = ρ i) → F'.HoldsAt ε ρ' h

open HeapKnowledge in
theorem transported_of {K : List IndexFact} {ρ : Env} {h : Heap} (hK : ∀ F ∈ K, F.HoldsAt ε ρ h)
    (ρ' : Env) : Transported ε K ρ ρ' h :=
  fun F hF _ _ hm hg => (IndexFact.holdsAt_mapM hm hg).mpr (hK F hF)

/-- With the exit's value bound, a target slot mapped to source slot `i + 1`
reads the node's slot `i`. -/
theorem mapEnv_push_slot {θ : Mapping} {v : Tm} {ρ : Env} {i j : Nat} (hs : slot θ j = i + 1) :
    mapEnv θ (push v ρ) j = ρ i := by
  simp [mapEnv, hs, push]

open HeapKnowledge in
/-- **TRANSFER.** A node's local safety from `s₀`, its exit-specific footprints
`cn`, `ce` and posts `Qn`, `Qe`; the retained facts `Kn`, `Ke` under the
modality of the exit's footprint; and, per exit, the target obligation from
the exit's value, its type above, its post and the retained facts transported
to every target environment: then the node meets its exit obligations, which
`graph_safe` composes into `SafeGraph`. -/
theorem transfer {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop} {cn ce : Footprints.Closed}
    {Qn : Post}
    {Qe : Heap → Prop} {ρ : Env} {m : Nat} {s₀ : IndexedHeap} {k : Continuation} {x : Option Target}
    {Kn Ke : List IndexFact}
    (hshape : ∀ (j : Nat) (U : WorldT (j + 1)) (h : Heap) (v : Tm), isVal v = true → T (j + 1) U v →
      cn.Holds s₀.h h → Qn h v → ShapeOk v k)
    (hkeepN : ∀ F ∈ Kn, Box cn.fp (fun ρ _ s => F.HoldsAt ε ρ s.h) ρ m s₀)
    (hkeepE : ∀ F ∈ Ke, Box ce.fp (fun ρ _ s => F.HoldsAt ε ρ s.h) ρ m s₀)
    (hentN : ∀ (s : IndexedHeap) (v : Tm), Action cn.fp ρ s₀ s → isVal v = true → Above T s v → Qn s.h v →
      (∀ ρ', Transported ε Kn ρ ρ' s.h) → NormalTarget pre Tres Qres ρ m s v k)
    (hentE : ∀ (s : IndexedHeap) (e : Tm), Action ce.fp ρ s₀ s → Scoped 0 e → Above Ξ s e → Qe s.h →
      (∀ ρ', Transported ε Ke ρ ρ' s.h) → RaiseTarget pre Ξres Rres ρ m s e x) :
    NodeObligations pre Ξres Tres Qres Rres Ξ T cn ce Qn Qe ρ m s₀ k x :=
  ⟨hshape,
    fun s v ha hv hT hq => hentN s v ha hv hT hq (transported_of fun F hF => hkeepN F hF s ha),
    fun s e ha hsc hΞ hq => hentE s e ha hsc hΞ hq (transported_of fun F hF => hkeepE F hF s ha)⟩

end Verification.TolerantFrames
