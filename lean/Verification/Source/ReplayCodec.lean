import Lean.Elab.Command
import Lean.Elab.Term
namespace Verification.ReplayKey
open Lean
class Codec (α : Type) where
  put : α → Json
  get : Json → Option α
  read_put (x : α) : get (put x) = some x

export Codec (put get)
attribute [simp] Codec.read_put

instance : Codec Json := ⟨id, some, fun _ => rfl⟩
instance : Codec String := ⟨.str, fun | .str s => some s | _ => none, fun _ => rfl⟩
instance : Codec Bool := ⟨.bool, fun | .bool b => some b | _ => none, fun _ => rfl⟩
instance : Codec Nat := ⟨fun n => .num ⟨n,0⟩, fun | .num ⟨.ofNat n,0⟩ => some n | _ => none, fun _ => rfl⟩
instance : Codec Int := ⟨fun n => .num ⟨n,0⟩, fun | .num ⟨n,0⟩ => some n | _ => none, fun _ => rfl⟩
instance : Codec UInt64 := ⟨fun n => put n.toNat, fun j => UInt64.ofNat <$> get j, by
  intro n; simp⟩

instance [Codec α] [Codec β] : Codec (α × β) :=
  ⟨fun (x,y) => .arr ⟨[put x, put y]⟩,
   fun | .arr ⟨[x,y]⟩ => return (← get x, ← get y) | _ => none,
   by rintro ⟨x,y⟩; simp⟩

def getList [Codec α] : List Json → Option (List α)
  | [] => some []
  | x :: xs => return (← get x) :: (← getList xs)

theorem getList_put [Codec α] (xs : List α) : getList (xs.map put) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [getList, ih]

instance [Codec α] : Codec (List α) :=
  ⟨fun xs => .arr ⟨xs.map put⟩, fun | .arr ⟨js⟩ => getList js | _ => none, getList_put⟩
instance [Codec α] : Codec (Array α) :=
  ⟨fun xs => put xs.toList, fun j => List.toArray <$> get j, by intro xs; simp⟩
instance [Codec α] : Codec (Option α) :=
  ⟨fun | none => .null | some x => .arr ⟨[put x]⟩,
   fun | .null => some none | .arr ⟨[j]⟩ => some <$> get j | _ => none,
   by intro x; cases x <;> simp⟩

open Lean Meta Elab Command

/-- Derive a codec and its inverse equation by cases on the constructors.
Mutually recursive field types share a block. The field codecs of all other
types are inferred. Tags distinguish constructors of a sum. -/
syntax "replay_codec " ident " for " term,+ : command

private structure Field where
  binder : Ident
  recursiveIndex : Option Nat

private structure Variant where
  name : Name
  fields : Array Field

private structure Shape where
  type : Term
  variants : Array Variant

private def inspectShapes (specs : Array Term) : TermElabM (Array Shape) := do
  let types ← specs.mapM fun spec => Lean.Elab.Term.elabType spec
  types.mapIdxM fun i type => do
    let type ← withReducible (whnf type)
    let .const name levels := type.getAppFn | throwError "expected an inductive type, got {type}"
    let .inductInfo ind ← getConstInfo name | throwError "{name} is not inductive"
    let variants ← ind.ctors.toArray.mapM fun ctor => do
      let applied := mkAppN (.const ctor levels) type.getAppArgs
      let fields ← forallTelescopeReducing (← inferType applied) fun args _ => args.mapIdxM fun j arg => do
        let argType ← inferType arg
        let sibling ← types.findIdxM? (fun t => isDefEq t argType)
        return {binder := mkIdent (Name.mkSimple s!"field{j}"), recursiveIndex := sibling : Field}
      return { name := ctor, fields }
    return {type := specs[i]!, variants}

private def commandText (source : String) : CommandElabM Unit := do
  let cmd ← ofExcept <| Parser.runParserCategory (← getEnv) `command source
  elabCommand cmd

private def keyCommands (shapes : Array Shape) : CommandElabM Unit := do
  let recursive := shapes.any fun s => s.variants.any fun v => v.fields.any (·.recursiveIndex.isSome)
  let termination := if recursive then "\ntermination_by x => sizeOf x" else ""
  let mut encoders := #[]
  let mut decoders := #[]
  let mut laws := #[]
  let mut instances := #[]
  for s in shapes, i in [:shapes.size] do
    let ty := (← liftCoreM <| PrettyPrinter.ppTerm s.type).pretty
    let mut enc := s!"private def encode{i} : {ty} → Json"
    let mut dec := s!"private def decode{i} : Json → Option ({ty})"
    let mut law := s!"private theorem decode_encode{i} : (x : {ty}) → decode{i} (encode{i} x) = some x"
    for v in s.variants do
      let tag := v.name.getString!
      let prefixFields := if s.variants.size > 1 then [s!".str {reprStr tag}"] else []
      let ctor := String.intercalate " " (("." ++ tag) :: v.fields.toList.map (fun f => f.binder.getId.toString))
      let mut encoded := prefixFields
      let mut patterns := prefixFields
      let mut decoded := ["." ++ tag]
      let mut lemmas := [s!"encode{i}", s!"decode{i}"]
      for f in v.fields do
        let x := f.binder.getId.toString
        let put := f.recursiveIndex.elim "put" (fun j => s!"encode{j}")
        let get := f.recursiveIndex.elim "get" (fun j => s!"decode{j}")
        patterns := patterns ++ [x]
        encoded := encoded ++ [s!"{put} {x}"]
        decoded := decoded ++ [s!"(← {get} {x})"]
        if let some j := f.recursiveIndex then lemmas := lemmas ++ [s!"decode_encode{j} {x}"]
      enc := enc ++ s!"\n  | {ctor} => .arr ⟨[{", ".intercalate encoded}]⟩"
      dec := dec ++ s!"\n  | .arr ⟨[{", ".intercalate patterns}]⟩ => return {" ".intercalate decoded}"
      law := law ++ s!"\n  | {ctor} => by simp [{", ".intercalate lemmas}]"
    encoders := encoders.push (enc ++ termination)
    decoders := decoders.push (dec ++ "\n  | _ => none" ++ termination)
    laws := laws.push (law ++ termination)
    instances := instances.push s!"instance : Codec ({ty}) := ⟨encode{i}, decode{i}, decode_encode{i}⟩"
  for block in #[encoders, decoders, laws] do
    if block.size > 1 then commandText ("mutual\n" ++ "\n".intercalate block.toList ++ "\nend")
    else commandText block[0]!
  for inst in instances do commandText inst

elab_rules : command
  | `(replay_codec $name:ident for $specs,*) => do
    let shapes ← runTermElabM fun _ => inspectShapes specs.getElems
    elabCommand (← `(namespace $name))
    keyCommands shapes
    elabCommand (← `(end $name))

end Verification.ReplayKey
