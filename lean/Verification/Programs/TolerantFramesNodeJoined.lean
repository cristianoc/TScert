import Verification.Programs.TolerantFramesWalkJoined

/-! # Tolerant frames: an exit into a merge delivers the merge's joined implications

A merge keeps a joined implication (`joinedChecked`) where every edge
recorded into it as `(Γe, atSlots, m)` passes `impliesCheck` at its source
context `Γe`. The implication is justified by the source environment's
types, which the edge state's meaning (`StateHolds`) does not read; so it
holds where an exit delivers it, at the exit's source environment `ρs`
typed by `Γe` (`joined_of_exit`). Proved:

- `joinedAt_of_exit`: an edge recorded as `(Γe, atSlotsOf names carried,
  m)` into `t`, its source environment `ρs` typed by `Γe`, its slots naming
  `names`' values at `η`, its carried implications holding at `η` ⟹
  `joinedAt t (mapEnv m ρs)`. -/
namespace Verification.TolerantFrames
open Verification SinglePass Footprints HeapObservations
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open PositiveRules HeapExpressionRules

section Joined
variable {ι : Type} [DecidableEq ι]

/-- **An exit establishes the merge's joined implications**: an edge
recorded into `t` as `(Γe, atSlotsOf names carried, m)`, a source
environment `ρs` typed by `Γe` whose slots hold `names`' values at `η`, the
carried implications holding at `η` (`joined_of_exit`). -/
theorem joinedAt_of_exit {G : NormalGraph ι} {w : Walk ι} {given : Nat → Bool} {ctx : Nat → List (Ty ι)}
    {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)} {t : Nat}
    {Γe : List (Ty ι)} {names : List Nat} {carried : List (PromiseCalls.Implication ι)} {m : PointClaims.Mapping}
    {ρs η : Env} {k : Nat} {s : IndexedHeap} (hin : (Γe, atSlotsOf names carried, m) ∈ edgesIn t)
    (he : EnvOk G Γe ρs s.n s.W) (hss : SlotsNamed names ρs η) (hcar : PromiseCalls.ImpliesOk G carried η s.n s.W) :
    joinedAt G w given ctx edgesIn t (PointClaims.mapEnv m ρs) k s :=
  fun _ _ => joined_of_exit hin he hss hcar

end Joined

end Verification.TolerantFrames
