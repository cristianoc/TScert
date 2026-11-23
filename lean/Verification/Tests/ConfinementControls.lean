import Verification.Semantics.Confinement
import Verification.Programs.LocalConfinement
import Verification.Programs.SinglePass

/-! Controls for checked local-object confinement (`Confinement`,
`LocalConfinement`, `SinglePass.checkWalkConfinement`).

Each theorem verifies that the checked verifier refuses a forged confinement
table (`LocalConfinement.Table`) or refutes an unsound relaxation of the
confinement rules:
1. `scalar_outside_can_store_object`: `Footprints.Change.scalar` (and `.init`)
   outside `Priv` admits storing an object value, which is why
   `LocalConfinement.frameConfined` requires strictly `.keep` outside
   `owned`/`ownedArr`.
2. `forged_start_nonempty_refused`: `SinglePass.checkWalkConfinement` refuses a
   forged table whose `start` entry claims a non-empty `owned` set.
3. `forged_missing_holder_refused`: `LocalConfinement.checkNode` refuses a
   forged table that allocates a fresh object into `owned` but omits the result
   slot from `holders` at the successor node.
4. `forged_framed_callback_mentioning_holder_refused`: `LocalConfinement.checkNode`
   refuses a forged table that puts a call into `framedNodes` when the call
   passes a slot in `holders`.
5. `forged_write_escape_refused`: `LocalConfinement.checkNode` refuses a forged
   table that keeps `owned` across writing a `holder` slot into a field of a
   non-owned object.
6. `forged_unverified_call_refused`: `LocalConfinement.checkNode` refuses a
   forged table that keeps `owned` across an `.invoke` mentioning a holder when
   no confined step derivation is supplied. -/

namespace Verification.LocalConfinement.Controls
open Verification Verification.Footprints Verification.ControlFlow Verification.ProgramTyping
open Verification.PositiveGraphs Verification.PositiveCertificates Verification.CertificateProducer
open Verification.LocalConfinement

private def emptyG : NormalGraph Nat :=
  { rows := fun
      | 0 => [.num]
      | _ => [] }

private def emptyImg : InstanceImageCheck emptyG := finiteInstanceImages emptyG

private def noCodes : CodeEntry Nat → Bool := fun _ => false

private def numTy : Ty Nat := [0]
private def objTy : Ty Nat := [1]

/-- `Change.scalar` and `Change.init` permit replacing `undefined` with an
object value, so a `scalar` or `init` frame outside `Priv` can leak a private
object into an outside heap cell. -/
theorem scalar_outside_can_store_object :
    let obj : Val := .objAt [(.str "i", 0)] .absent 1
    Change.Holds .scalar 0 .undef obj ∧ Change.Holds .init 0 .undef obj := by
  refine ⟨.inr ⟨by rfl, by rfl, by rfl⟩, .inr ⟨by rfl, by rfl⟩⟩

/-- A forged table claiming `owned = [0]` at `start` is refused by
`SinglePass.checkWalkConfinement`. -/
theorem forged_start_nonempty_refused :
    let P : Program := [⟨.nul, .ret, none⟩]
    let claims : List (PointClaim Nat) := [⟨[objTy], numTy⟩]
    let forged : LocalConfinement.Table :=
      { nodes := #[{ owned := [0], holders := [0] }], framedNodes := [], allocPriv := [] }
    let w : SinglePass.Walk Nat :=
      { labels := #[{}], incoming := #[[]], incomingImpl := #[[]], incomingEdges := #[[]] }
    SinglePass.checkWalkConfinement emptyG emptyImg noCodes [] P claims 0 forged w = false := by
  decide

/-- A forged table that puts a freshly allocated object into `owned` at node 1
while omitting slot 0 from `holders` is refused by `LocalConfinement.checkNode`. -/
theorem forged_missing_holder_refused :
    let n0 : Node := ⟨.makeAt .absent [.str "i"] [.num 0], .bind { label := 1, mapping := none }, none⟩
    let claims : List (PointClaim Nat) := [⟨[], objTy⟩, ⟨[objTy], numTy⟩]
    let forged : LocalConfinement.Table :=
      { nodes := #[{}, { owned := [0], holders := [] }]
        framedNodes := []
        allocPriv := [0] }
    LocalConfinement.checkNode emptyG emptyImg noCodes [] claims forged 0 n0 claims[0]! {} none = false := by
  decide

/-- A forged table that marks a callback invocation passing a holder (`var 0`)
as framed (`framedNodes := [0]`) is refused by `LocalConfinement.checkNode`. -/
theorem forged_framed_callback_mentioning_holder_refused :
    let n0 : Node := ⟨.invoke (.var 1) .undef [.var 0], .ret, none⟩
    let claims : List (PointClaim Nat) := [⟨[objTy, objTy], numTy⟩]
    let forged : LocalConfinement.Table :=
      { nodes := #[{ owned := [0], holders := [0] }]
        framedNodes := [0]
        allocPriv := [] }
    LocalConfinement.checkNode emptyG emptyImg noCodes [] claims forged 0 n0 claims[0]! {} none = false := by
  decide

/-- A forged table that keeps `owned = [0]` across writing holder `var 0` into a
field of non-owned `var 1` is refused by `LocalConfinement.checkNode`. -/
theorem forged_write_escape_refused :
    let n0 : Node := ⟨.writeAt (.str "cur") (.var 1) (.var 0), .effect { label := 1, mapping := none }, none⟩
    let claims : List (PointClaim Nat) := [⟨[objTy, objTy], numTy⟩, ⟨[objTy, objTy], numTy⟩]
    let forged : LocalConfinement.Table :=
      { nodes := #[{ owned := [0], holders := [0] }, { owned := [0], holders := [0] }]
        framedNodes := []
        allocPriv := [] }
    LocalConfinement.checkNode emptyG emptyImg noCodes [] claims forged 0 n0 claims[0]! {} none = false := by
  decide

/-- A forged table that keeps `owned = [0]` across a call passing holder `var 0`
without a checked confined derivation is refused by `LocalConfinement.checkNode`. -/
theorem forged_unverified_call_refused :
    let n0 : Node := ⟨.invoke (.var 1) .undef [.var 0], .effect { label := 1, mapping := none }, none⟩
    let claims : List (PointClaim Nat) := [⟨[objTy, objTy], numTy⟩, ⟨[objTy, objTy], numTy⟩]
    let forged : LocalConfinement.Table :=
      { nodes := #[{ owned := [0], holders := [0] }, { owned := [0], holders := [0] }]
        framedNodes := []
        allocPriv := [] }
    LocalConfinement.checkNode emptyG emptyImg noCodes [] claims forged 0 n0 claims[0]! {} none = false := by
  decide

end Verification.LocalConfinement.Controls
