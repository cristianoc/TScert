import Verification.Types.Decode
import Verification.Types.PositiveGraphs

/- Strict finite resolution metadata. The wire records a proposal; its
semantic qualifications are established by the source certificate checker. -/
namespace Verification.ResolutionWire
open Lean

/-- The names a qualified binder owns: its observation, and, for a resolvable
binder, its result; an awaitable binder owns no result (`"result": null`). -/
structure Slots where
  observation : String
  result : Option String
  deriving Repr, BEq, Inhabited

instance : ToJson Slots := ⟨fun s =>
  Json.mkObj [("observation", toJson s.observation), ("result", toJson s.result)]⟩

/-- The owned projection names. -/
def Slots.names (s : Slots) : List String := s.observation :: s.result.toList

instance : FromJson Slots where
  fromJson? j := do
    fieldsExactly j ["observation", "result"]
    let observation ← jStr (← jField j "observation")
    let result ← match ← jField j "result" with
      | .null => pure none
      | r => some <$> jStr r
    if observation.isEmpty || result == some "" || result == some observation then
      throw "resolution slots need distinct nonempty names"
    return ⟨observation, result⟩

/-- Names owned by a source binder, including its hidden projections. -/
def ownedNames (name : String) (resolution : Option Slots) : List String :=
  name :: (resolution.map Slots.names).getD []

/-- Each projection belongs to one binder and shadows no other binder in
this signature. Lexical binding against an enclosing scope is checked there. -/
def validateOwnership (parameters : List (String × Option Slots)) : Except String Unit := do
  let names := parameters.flatMap fun (name, resolution) => ownedNames name resolution
  if names.any String.isEmpty || names.eraseDups.length != names.length then
    throw "duplicate or overlapping resolution binder names"

/-- Positional descriptor groups in the expanded signature binder list. -/
def groups (parameters : List (String × Option Slots)) : List PositiveGraphs.ResolutionSlots :=
  (parameters.foldl (fun (state : Nat × List PositiveGraphs.ResolutionSlots) p =>
    match p.2 with
    | none => (state.1 + 1, state.2)
    | some { result := none, .. } => (state.1 + 2, state.2 ++ [⟨state.1, state.1 + 1, none⟩])
    | some { result := some _, .. } =>
      (state.1 + 3, state.2 ++ [⟨state.1, state.1 + 1, some (state.1 + 2)⟩])) (0, [])).2

structure Binder (T : Type) where
  name : String
  bound : Option T
  resolution : Option Slots
  deriving Repr, BEq, Inhabited

def Binder.ownedNames (b : Binder T) : List String := ResolutionWire.ownedNames b.name b.resolution

/-- How an input is classified: `stable`, a native promise whose payload the
child classifies (`native`), a native promise observed at its payload whatever
it is (`promise`), a union of classified arms, or a binder in scope. -/
inductive Certificate where
  | stable
  | native (child : Certificate)
  | promise
  | union (arms : List Certificate)
  | binder (name : String)
  deriving Repr, BEq, Inhabited

private partial def Certificate.encode : Certificate → Json
  | .stable => Json.mkObj [("k", toJson "stable")]
  | .native child => Json.mkObj [("k", toJson "native"), ("child", Certificate.encode child)]
  | .promise => Json.mkObj [("k", toJson "promise")]
  | .union arms => Json.mkObj [("k", toJson "union"), ("arms", toJson (arms.map Certificate.encode))]
  | .binder name => Json.mkObj [("k", toJson "binder"), ("binder", toJson name)]

instance : ToJson Certificate := ⟨Certificate.encode⟩

private partial def Certificate.fromJson (j : Json) : Except String Certificate := do
  match ← jStr (← jField j "k") with
  | "stable" =>
    fieldsExactly j ["k"]
    return .stable
  | "native" =>
    fieldsExactly j ["k", "child"]
    return .native (← Certificate.fromJson (← jField j "child"))
  | "promise" =>
    fieldsExactly j ["k"]
    return .promise
  | "union" =>
    fieldsExactly j ["k", "arms"]
    let arms ← jArr j "arms"
    if arms.isEmpty then throw "a resolution union needs an arm"
    return .union (← arms.mapM Certificate.fromJson)
  | "binder" =>
    fieldsExactly j ["k", "binder"]
    let name ← jStr (← jField j "binder")
    if name.isEmpty then throw "empty resolution certificate binder"
    return .binder name
  | _ => throw "unknown resolution certificate constructor"

instance : FromJson Certificate := ⟨Certificate.fromJson⟩

structure Instance where
  certificate : Certificate
  deriving Repr, BEq, Inhabited, ToJson

instance : FromJson Instance where
  fromJson? j := do
    fieldsExactly j ["certificate"]
    return ⟨← fromJson? (← jField j "certificate")⟩

end Verification.ResolutionWire
