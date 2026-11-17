import Verification.Paper.TolerantFrames.Derivations
import Verification.Paper.TolerantFrames.Renaming

/-! # Regional checked transfer

The existing mechanisms extended here are `Derivation.sound`, command executions,
and existential-world triples. This assembles the exact five parts of Check:
old knowledge, the regional action, the node postcondition, branch condition,
and target assertion pulled back along the edge renaming. The finite derivation
language is explicitly a subcalculus of Definition 23; transfer is general in
the assertions and regional footprints, without assuming search completeness.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge HeapObservations
open Verification.TolerantFrames

abbrev Knowledge := List Formula

def Satisfies (K : Knowledge) : Assertion := fun ρ m s => ∀ F ∈ K, F.Holds ρ m s

/-- An edge's four pieces of proof data. `taken` identifies actual exits of
the command; `condition` is justified separately from command execution. -/
structure Edge where
  command : Command
  taken : Exit → Prop
  effect : Footprint
  post : Postcondition
  condition : Assertion
  rename : Nat → Nat

/-- The target environment induced by the source environment. Renaming is
capture-free because it is a map of free target names, not binder slots. -/
def Target (θ : Nat → Nat) (A : Formula) : Postcondition :=
  fun _ ρ' m _ t => A.Holds (fun x => ρ' (θ x)) m t

/-- The semantic target pullback is precisely capture-avoiding syntactic
renaming, including target assertions with logical binders and modalities. -/
theorem Target.syntactic (θ : Nat → Nat) (A : Formula) (ρ ρ' : Env) (m : Nat) (s t : IndexedHeap) :
    Target θ A ρ ρ' m s t ↔ (A.rename θ).Holds ρ' m t := (A.holds_rename θ ρ' m t).symm

/-- Definition 21's assembled sequent, instantiated in the sound general
subcalculus. No regional effect or knowledge shape is discarded. -/
def Check (K : Knowledge) (e : Edge) (A : Formula) : Prop :=
  Derivation [Old (Satisfies K), Transition e.effect, e.post, Now e.condition] (Target e.rename A)

/-- Sound per-edge specifications are about actual command executions and
choose their exit world, just as triples do. -/
def EdgeSound (host : NativeCode) (K : Knowledge) (edge : Edge) : Prop :=
  ∀ ρ m s n ρ' h' exit, ValidContext ρ m s → Satisfies K ρ m s →
    Executes host edge.command ρ s.h n ρ' h' exit → edge.taken exit → n < s.n →
    ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧ ValidContext ρ' m t ∧ ExitValid exit t ∧
      Action edge.effect ρ s t ∧ edge.post ρ ρ' m s t ∧ edge.condition ρ' m t

/-- Connect a node's two-exit triple and effects to its per-edge summary.
The branch condition and selection of this edge's post/effect are exact proof
obligations. No class-only footprint restriction occurs. -/
theorem edge_sound_of_triple {host K edge P Q Qe J Ret Φ Φe}
    (ht : Triple host P edge.command Q Qe J Ret)
    (he : Effects host P edge.command Φ Φe) (hp : Entails (Satisfies K) P)
    (hframe : ∀ exit, edge.taken exit → edge.effect = (match exit with | .thrown _ => Φe | _ => Φ))
    (hpost : ∀ exit ρ ρ' m s t, edge.taken exit → ExitPost Q Qe J Ret exit ρ ρ' m s t → edge.post ρ ρ' m s t)
    (hbranch : ∀ ρ m s n ρ' h' exit (t : IndexedHeap), Satisfies K ρ m s →
      Executes host edge.command ρ s.h n ρ' h' exit → edge.taken exit →
      Admissible s t → t.h = h' → t.n + n = s.n → edge.condition ρ' m t) : EdgeSound host K edge := by
  intro ρ m s n ρ' h' exit hv hK hr htake hn
  have hP := hp ρ m s hK
  obtain ⟨t, ha, hh, hk, hvt, hve, hq⟩ := ht _ _ _ _ _ _ _ hv hP hr hn
  have hφ := he _ _ _ _ _ _ _ hv hP hr hn
  refine ⟨t, ha, hh, hk, hvt, hve, ⟨ha, ?_⟩, hpost _ _ _ _ _ _ htake hq, hbranch _ _ _ _ _ _ _ t hK hr htake ha hh hk⟩
  rw [hframe exit htake, hh]
  exact hφ

/-- Theorem 22, connected to a completed command execution, for full regional
effects and arbitrary paper knowledge. The result uses the summary's chosen
world; it does not claim the same assertion at every admissible exit world. -/
theorem transfer {host : NativeCode} {K : Knowledge} {edge : Edge} {A : Formula}
    (hs : EdgeSound host K edge) (hc : Check K edge A)
    {ρ : Env} {m : Nat} {s : IndexedHeap} {n : Nat} {ρ' : Env} {h' : Heap} {exit : Exit}
    (hv : ValidContext ρ m s) (hK : Satisfies K ρ m s) (hr : Executes host edge.command ρ s.h n ρ' h' exit)
    (he : edge.taken exit) (hn : n < s.n) :
    ∃ t : IndexedHeap, Admissible s t ∧ t.h = h' ∧ t.n + n = s.n ∧ ValidContext ρ' m t ∧ ExitValid exit t ∧
      A.Holds (fun x => ρ' (edge.rename x)) m t := by
  obtain ⟨t, ha, hh, hk, hvt, hve, hΦ, hQ, hB⟩ := hs _ _ _ _ _ _ _ hv hK hr he hn
  refine ⟨t, ha, hh, hk, hvt, hve, hc.sound ρ ρ' m s t hv hvt ?_⟩
  intro F hF
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl | rfl
  · exact hK
  · exact hΦ
  · exact hQ
  · exact hB

end Verification.Paper.TolerantFrames
