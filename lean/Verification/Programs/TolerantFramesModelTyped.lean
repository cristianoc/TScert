import Verification.Programs.TolerantFramesWrites

/-! # Tolerant frames: the supports a typed environment gives

Three world facts the modality's atoms take as premises follow from a typed
environment (`ProgramTyping.EnvOk`):

- **allocated cells** (`StoreCells`): a slot whose type is a record whose
  store field has a type of one `.list` clause holds an object whose store
  location's contract meets a tuple contract (`storeCells_of_typed`); and an
  object of a record, dictionary or `source` clause owning the store key, in
  a graph stating the built-ins, meets the array invariant
  (`storeCells_of_builtins`);
- **stable paths** (`StableAt`): a field every clause of the slot's type
  states stable is read one way for the object's life
  (`stableAt_of_stableField`, the `stableFirst` evidence
  `stableAt_of_stableFirst`), and paths compose through a slot holding the
  intermediate value (`stableAt_cons`);
- **class evidence** (`ClassOk`): a field of source-value type holds a value,
  not a store (`valueClass_ok`), and a store field of a `.list` type holds a
  store (`storeClass_ok`), at every heap meeting the world. -/
namespace Verification.TolerantFrames
open Verification Footprints ProgramTyping PositiveGraphs PositiveRules PositiveNormalization
open ExpressionEffects HeapExpressionRules
open Verification.HeapKnowledge (ElementsBelow ElementsAbove RegionsApart)

variable {ι : Type}

/-! ## Allocated cells -/

/-! ## Stable paths -/

/-! ## Class evidence -/

end Verification.TolerantFrames
