import Verification.Source.Claims.CallbackInterfaceCheck

/-! Controls at the lowered proof-rule boundary. The examples supply their
live facts, possible write bounds, and location evidence explicitly. -/
namespace Verification.SourceClaimJson.CallbackPreservation.Controls
open Footprints HeapKnowledge CallEffects

private def own (root : Nat) (key : String) : FactKind :=
  .cell ⟨root, {}, .str key⟩

private def sameRoots : RootMap := fun root => some (root, [])
private def xsOnly : RootMap := fun root => if root == 0 then some (0, []) else none

/-! In `walk(xs, visit)` the cursor is private. A numeric argument cannot
expose its object. The possible effects include both arrays and a public
record's same-named field. -/
private def walk : Site where
  parameter := 1
  live := ⟨{
    heap := [own 1 "i", .dense 0 1, .elems 0 { num := true }]
    index := [.bound 0 3 true]
  }, {}⟩
  possible := ⟨[
    (.field 0 arraySpineKey, .any), (.cells 0, .any),
    (.field 2 arraySpineKey, .any), (.field 4 (.str "i"), .any)
  ], []⟩
  localEvidence := { facts := [.locs 4 none 1 (.str "i")] }
  toInterface := xsOnly

private def trace (capture : Nat) : Callback where
  effects := ⟨[(.field 8 arraySpineKey, .extend)], []⟩
  actuals := fun formal => if formal == 8 then some capture else none

private def argument (parameter : Nat) (callback : Callback) : Nat → Option Callback :=
  fun slot => if slot == parameter then some callback else none

private def traceApart : SepEvidence := { facts := [.arrays (0, []) (2, [])] }

#guard
  match walk.infer with
  | .error _ => false
  | .ok demand =>
    (project xsOnly demand.support.normal).isSome &&
    demand.support.normal.contains (.cells 0, .keep) &&
    demand.support.exceptional.isEmpty &&
    walk.checkPublished demand sameRoots &&
    !walk.checkPublished { demand with support := ⟨[], []⟩ } sameRoots &&
    demand.check xsOnly (argument 1 (trace 2)) traceApart &&
    !demand.check xsOnly (argument 1 (trace 2)) {} &&
    !demand.check xsOnly (argument 1 (trace 0)) traceApart &&
    !demand.check xsOnly (argument 2 (trace 2)) traceApart &&
    !demand.check xsOnly (argument 1 { trace 0 with effects := ⟨[(.cells 8, .any)], []⟩ }) {} &&
    let concrete := { walk with localEvidence := traceApart }
    concrete.checkContinuation ((trace 2).effects.map (·.renameM (trace 2).actuals))

-- A caller can forward the visitor and export the demand on its own parameter.
#guard
  match walk.infer.toOption >>= (·.forward 3 (fun root => if root == 0 then some (5, []) else none)) with
  | none => false
  | some demand =>
    demand.parameter == 3 &&
    demand.check (fun root => if root == 5 then some (0, []) else none)
      (argument 3 (trace 2)) traceApart

-- The bound and density alone tolerate append.
#guard
  let growWalk := { walk with live := ⟨{ walk.live.normal with heap := [own 1 "i", .dense 0 1] }, {}⟩ }
  match growWalk.infer with
  | .error _ => false
  | .ok demand =>
    demand.check xsOnly (argument 1 (trace 0)) {} &&
    growWalk.checkContinuation ((trace 0).effects.map (·.renameM (trace 0).actuals)) &&
    !growWalk.checkContinuation ⟨[(.field 0 arraySpineKey, .any)], []⟩

-- If the cursor becomes reachable, it must be published or the rule refuses.
#guard
  let exposed := { walk with localEvidence := {} }
  match exposed.infer, ({ exposed with toInterface := sameRoots }).infer with
  | .error _, .ok demand =>
    ({ exposed with toInterface := sameRoots }).checkPublished demand sameRoots &&
    !demand.check sameRoots (argument 1 ⟨⟨[(.field 8 (.str "i"), .any)], []⟩,
      fun formal => if formal == 8 then some 1 else none⟩) {}
  | _, _ => false

-- An exceptional continuation can need the same support independently.
#guard
  let catches := { walk with live := ⟨{}, walk.live.normal⟩, possible := ⟨[], walk.possible.normal⟩ }
  let callback := { trace 0 with effects := ⟨[], [(.field 8 arraySpineKey, .any)]⟩ }
  match catches.infer with
  | .error _ => false
  | .ok demand =>
    demand.support.normal.isEmpty && !demand.support.exceptional.isEmpty &&
    !demand.check xsOnly (argument 1 callback) {} &&
    demand.check xsOnly (argument 1 { callback with effects := ⟨callback.effects.exceptional, []⟩ }) {}

/-! `findWholeLine` supplies `flow.data`. Its closure captures `flow` and
updates the three cached results beside that data. The two linear facts
express equality of the geometry lengths. -/
private def widths := Term.now .length 0 ["widths"]
private def flags := Term.now .view 0 ["segmentFlags"]

private def rawWalk : Site where
  parameter := 3
  live := ⟨{
    heap := [own 1 "segmentIndex", own 1 "graphemeIndex"]
    index := [.linear (.le [(widths, 1), (flags, -1)] 0),
              .linear (.le [(flags, 1), (widths, -1)] 0)]
  }, {}⟩
  possible := ⟨[
    (.path 0 ["widths"] arraySpineKey, .any),
    (.field 0 (.str "widths"), .any), (.field 0 (.str "segmentFlags"), .any)
  ], []⟩
  localEvidence := {}
  toInterface := xsOnly

private def wholeLine (normal : Footprint) : Callback where
  effects := ⟨normal, []⟩
  actuals := fun formal => if formal == 8 then some 5 else none

private def flowData : RootMap := fun root => if root == 0 then some (5, ["data"]) else none

#guard
  match rawWalk.infer with
  | .error _ => false
  | .ok demand =>
    let cacheWrites : Footprint :=
      ["wholeWidth", "wholeStart", "wholeEnd"].map fun k => (.field 8 (.str k), .any)
    rawWalk.checkPublished demand sameRoots &&
    demand.check flowData (argument 3 (wholeLine cacheWrites)) {} &&
    !demand.check flowData (argument 3 (wholeLine [(.path 8 ["data"] (.str "widths"), .any)])) {} &&
    !demand.check flowData
      (argument 3 (wholeLine [(.path 8 ["data"] (.str "segmentFlags"), .any)])) {} &&
    !demand.check flowData
      (argument 3 (wholeLine [(.path 8 ["data", "widths"] arraySpineKey, .extend)])) {}

end Verification.SourceClaimJson.CallbackPreservation.Controls

namespace Verification.SourceClaimJson.CallbackEffectInference.Controls
open Footprints ControlFlow

private def writes (field : String) : Footprint := [(.field 2 (.str field), .any)]

-- The handler's return carries the throwing step's writes. On the normal
-- branch, the cycle retains the writes of each possible iteration.
#guard
  let nodes : Program := [⟨.undef, .effect 1, some 3⟩, ⟨.undef, .branch 0 2, none⟩,
    ⟨.undef, .ret, none⟩, ⟨.undef, .ret, none⟩, ⟨.undef, .ret, none⟩]
  let locals : Array (Option Summary) := #[some ⟨some (writes "normal"), some (writes "raised")⟩,
    some ⟨some [], none⟩, some ⟨some [], none⟩, some ⟨some (writes "caught"), none⟩,
    some ⟨some (writes "unreachable"), none⟩]
  match composeChecked nodes 0 locals with
  | .ok ⟨some normal, none⟩ =>
    normal.length == 3 && (["normal", "raised", "caught"].flatMap writes).all normal.contains
  | _ => false

-- An absent record at a reached return cannot certify an absent normal exit.
#guard
  let nodes : Program := [⟨.undef, .effect 1, none⟩, ⟨.undef, .ret, none⟩]
  match composeChecked nodes 0 #[some ⟨some [], none⟩, none] with
  | .error msg => msg == "closure effect flow certificate does not cover every reached node and exit"
  | .ok _ => false

end Verification.SourceClaimJson.CallbackEffectInference.Controls

namespace Verification.SourceClaimJson.CallbackInterfaceCheck.Controls
open ControlFlow ProgramTyping CallbackOrigins CallbackEffectInference CallbackPreservation Footprints

/-- The rest row and non-rest row have the same body. Slot 1 is the receiver
for the rest row and a capture of input 0 for the non-rest row. -/
private def collision (row : CallEffects.Arrow (Ty Nat)) : Option Callback := Id.run do
  let key := arraySpineKey
  let body : List Tm := [.writeAt key (.var 1) (.setElem (.readAt key (.var 1)) (.num 0) (.num 0))]
  let conts : List (Continuation × Option Target) := [(.ret, none)]
  let entry : CodeEntry Nat := ⟨0, body, conts, 0, [[]], row, none⟩
  let effect : Summary := ⟨some [(.field 1 arraySpineKey, .any)], some []⟩
  let rows : Array (CheckedCode Nat) := #[⟨{entry with spine := some []}, effect⟩, ⟨entry, effect⟩]
  let term := Tm.makeAt (.graph 0 body conts 0 [.var 0] .call false none) [] []
  let allocations : Array Node := #[⟨.arrLit [], .bind 1, none⟩, ⟨term, .ret, none⟩]
  let atAllocation : Table := #[some #[[.input 0]], some #[[.input 0], [.allocated 0]]]
  return ← closure rows allocations atAllocation 1 #[[.allocated 1], [.input 0], [.allocated 0]] [some (1, [])] (.var 0)

example (row : CallEffects.Arrow (Ty Nat)) :
    (collision row >>= fun cb => cb.actuals 1) = some 0 := by rfl

private def verdict (row : CallEffects.Arrow (Ty Nat)) : Bool :=
  let demand : Demand := ⟨0, ⟨[(.field 0 arraySpineKey, .keep)], []⟩, []⟩
  demand.check (fun x => some (x, [])) (fun _ => collision row)
    { facts := [.spines (0, []) (1, [])] }

example (row : CallEffects.Arrow (Ty Nat)) : verdict row = false := by rfl

end Verification.SourceClaimJson.CallbackInterfaceCheck.Controls
