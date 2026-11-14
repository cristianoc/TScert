import Verification.Semantics.Worlds
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
element cell in every well-formed state (`HeapOk.store_cells`).
-/
namespace Verification

inductive StorageRole where
  | field | cell | arrayStore | viewStore
  deriving DecidableEq, Repr, Inhabited

/-- The order roles are compared in, their declaration order. -/
def StorageRole.rank : StorageRole → Nat
  | .field => 0 | .cell => 1 | .arrayStore => 2 | .viewStore => 3

def StorageRole.before (a b : StorageRole) : Bool := a.rank < b.rank

/-- One storage position of a type: its key, the role it grants, and its
contents' type. -/
abbrev Stored (α : Type) := PropKey × StorageRole × α

/-- The positions of an operand with each contents' type mapped, keys and
roles kept. -/
def mapStored {α β : Type} (f : α → β) (fs : List (Stored α)) : List (Stored β) :=
  fs.map fun p => (p.1, p.2.1, f p.2.2)

/-- Positions of one role: each key (a property key, or an index's key
class) with its contents, every location allocated with the role `s`. -/
def withRole {κ α : Type} (s : StorageRole) (fs : List (κ × α)) : List (κ × StorageRole × α) :=
  fs.map fun p => (p.1, s, p.2)

theorem mem_withRole {κ α : Type} {s r : StorageRole} {fs : List (κ × α)} {k : κ} {a : α} :
    (k, r, a) ∈ withRole s fs ↔ r = s ∧ (k, a) ∈ fs := by
  simp only [withRole, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨k', a'⟩, hm, rfl, rfl, rfl⟩; exact ⟨rfl, hm⟩
  · rintro ⟨rfl, hm⟩; exact ⟨(k, a), hm, rfl, rfl, rfl⟩

theorem mapStored_withRole {α β : Type} (f : α → β) (s : StorageRole) (fs : List (PropKey × α)) :
    mapStored f (withRole s fs) = withRole s (fs.map fun p => (p.1, f p.2)) := by
  simp [mapStored, withRole, Function.comp_def]

theorem withRole_map_snd {κ α : Type} {s : StorageRole} {cs : List (κ × StorageRole × α)}
    (h : ∀ y ∈ cs, y.2.1 = s) : withRole s (cs.map fun c => (c.1, c.2.2)) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨k, r, a⟩ := c
    have hr : r = s := h _ List.mem_cons_self
    subst hr
    simp only [withRole, List.map_cons, List.map_map] at ih ⊢
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

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

/-- The roles a storage role tag names. -/
def StorageRole.permits : StorageRole → Role → Prop
  | .field, r => r = .field
  | .cell, r => r = .cell
  | .arrayStore, r => r = .store .array
  | .viewStore, r => ∃ N, r = .store (.view N)

/-- **Distinct tags name disjoint roles**: a role determines the tag naming it. -/
theorem StorageRole.permits_unique {s s' : StorageRole} {r : Role}
    (h : s.permits r) (h' : s'.permits r) : s = s' := by
  cases s <;> cases s' <;> simp only [StorageRole.permits] at h h' <;>
    first | rfl | (subst h; simp_all) | (obtain ⟨N, rfl⟩ := h; simp_all)

/-- Every tag names some role. -/
theorem StorageRole.inhabited (s : StorageRole) : ∃ r, s.permits r := by
  cases s
  · exact ⟨.field, rfl⟩
  · exact ⟨.cell, rfl⟩
  · exact ⟨.store .array, rfl⟩
  · exact ⟨.store (.view 0), 0, rfl⟩


end Verification
