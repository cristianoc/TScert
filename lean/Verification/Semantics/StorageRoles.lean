import Verification.Semantics.Calculus
/-!
# Storage roles

A type grants a location for each of its storage positions: a record's
invariant field, an optional field where the object has it, a dictionary's
writable index. The location's role is fixed by the allocation that made it
(docs/drafts/location-kinds.md, §4), and the type states it: a **storage
role** is the syntax of that statement, carried by every storage position of a
type and compared, ordered and serialized with it. Its meaning is a storage
capability over kinded worlds (`Kinds.Capability.ofRole`): `field` an
ordinary property F, `cell` a binding's storage C, `arrayStore` an ordinary
array's store, `viewStore` a typed array's view store of any fixed length.

A store's element positions carry none: every cell a store lists is an
element cell in every well-formed state (`Kinds.HeapOk.store_cells`).
-/
namespace Verification

inductive StorageRole where
  | field | cell | arrayStore | viewStore
  deriving DecidableEq, Repr, Inhabited

/-- One storage position of a type: its key, the role it grants, and its
contents' type. -/
abbrev Stored (α : Type) := PropKey × StorageRole × α

/-- The positions of an operand with each contents' type mapped, keys and
roles kept. -/
def mapStored {α β : Type} (f : α → β) (fs : List (Stored α)) : List (Stored β) :=
  fs.map fun p => (p.1, p.2.1, f p.2.2)

/-- The storage a list of positions grants: each key with its role. -/
def storageOf {α : Type} (fs : List (Stored α)) : List (PropKey × StorageRole) :=
  fs.map fun p => (p.1, p.2.1)

/-- **Mapping keeps every key's role.** -/
@[simp] theorem storageOf_mapStored {α β : Type} (f : α → β) (fs : List (Stored α)) :
    storageOf (mapStored f fs) = storageOf fs := by
  simp [storageOf, mapStored, Function.comp_def]

theorem mem_mapStored {α β : Type} {f : α → β} {fs : List (Stored α)} {k : PropKey}
    {s : StorageRole} {b : β} :
    (k, s, b) ∈ mapStored f fs ↔ ∃ a, (k, s, a) ∈ fs ∧ f a = b := by
  simp only [mapStored, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨k', s', a⟩, hm, rfl, rfl, rfl⟩; exact ⟨a, hm, rfl⟩
  · rintro ⟨a, hm, rfl⟩; exact ⟨(k, s, a), hm, rfl, rfl, rfl⟩

end Verification
