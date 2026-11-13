import Verification.Semantics.KindsWrites
import Verification.Semantics.StorageRoles
/-!
# Role-bearing storage capabilities

A **storage capability** is what a type grants over one own key of an object:
the key, and the pairs of a role and a contents type its location may have
(`Capability`). Its meaning (`Capability.Holds`) is that the key denotes a
location of the object whose world entry has one of those roles with a
contract agreeing with the paired type. The role is the one the world
recorded when the location was allocated: a capability exposes it and cannot
change it.

A family of pairs lets one capability range over roles, as a typed array's
element store does over every view length (`Capability.viewStore`). The three
constructions of the calculus's one object allocation are capabilities that
differ in their role: an object literal's property is a field
(`Capability.field`), a binding cell's is a cell (`Capability.binding`), an
array's store slot is an array store (`Capability.arrayStore`). Each holds of
the object its allocation makes (`Capability.holds_alloc`), a lookup exposes
the target's role (`Capability.Holds.role`), a write of contents of that
role's shape and type keeps the heap well-formed (`Capability.At.write`), and
two capabilities over one key of one object share a role
(`Capability.Holds.common`): a binding capability is no field capability
(`Capability.binding_not_field`).
-/
namespace Verification.Kinds

/-- A semantic type over kinded worlds: a family of approximations indexed by
a budget and judged against a world at that budget. -/
abbrev Fam := (k : Nat) → WorldT k → Val → Prop

/-- A semantic type restricts to a contract at any level. -/
def res {k : Nat} (T : Fam) : Ctr k := fun j _ W' v => T j W' v

/-- **A storage capability**: a key and the permitted pairs of a role and a
contents type. -/
structure Capability where
  key : PropKey
  permits : Role → Fam → Prop

namespace Capability

/-- The capability's meaning at a location: the world gives it a permitted
role, with a contract agreeing with the paired type at every lower budget. -/
def At (cap : Capability) {k : Nat} (W : WorldT k) (l : Nat) : Prop :=
  ∃ (r : Role) (c : Ctr k) (T : Fam), roleAt W l = some r ∧ lookup W l = some c ∧
    cap.permits r T ∧ ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u ↔ T j W' u

/-- **The capability's meaning** over an object's field map: its key denotes
a location with a permitted role and its contract. -/
def Holds (cap : Capability) {k : Nat} (W : WorldT k) (flds : List (PropKey × Nat)) : Prop :=
  ∃ l, flds.lookup cap.key = some l ∧ cap.At W l

/-- Extension keeps a capability's meaning. -/
theorem At.mono {cap : Capability} {k : Nat} {W W' : WorldT k} (hx : WExt W W') {l : Nat}
    (h : cap.At W l) : cap.At W' l :=
  let ⟨r, c, T, hr, hl, hp, hc⟩ := h
  ⟨r, c, T, WExt_roleAt hx hr, WExt_lookup hx hl, hp, hc⟩

/-- Truncation keeps a capability's meaning. -/
theorem At.trunc {cap : Capability} {k j : Nat} (hj : j ≤ k) {W : WorldT k} {l : Nat}
    (h : cap.At W l) : cap.At (trunc j hj W) l :=
  let ⟨r, c, T, hr, hl, hp, hc⟩ := h
  ⟨r, _, T, by simpa using hr, lookup_trunc hj W l c hl, hp,
    fun i hi W' u => hc i (Nat.lt_of_lt_of_le hi hj) W' u⟩

theorem Holds.mono {cap : Capability} {k : Nat} {W W' : WorldT k} (hx : WExt W W')
    {flds : List (PropKey × Nat)} (h : cap.Holds W flds) : cap.Holds W' flds :=
  let ⟨l, hl, ha⟩ := h; ⟨l, hl, ha.mono hx⟩

theorem Holds.trunc {cap : Capability} {k j : Nat} (hj : j ≤ k) {W : WorldT k}
    {flds : List (PropKey × Nat)} (h : cap.Holds W flds) : cap.Holds (Kinds.trunc j hj W) flds :=
  let ⟨l, hl, ha⟩ := h; ⟨l, hl, ha.trunc hj⟩

/-- **Lookup exposes the target's role**: the key's location, its role in the
world and a type the capability pairs with that role. -/
theorem Holds.role {cap : Capability} {k : Nat} {W : WorldT k} {flds : List (PropKey × Nat)}
    (h : cap.Holds W flds) :
    ∃ l r T, flds.lookup cap.key = some l ∧ roleAt W l = some r ∧ cap.permits r T :=
  let ⟨l, hl, r, _, T, hr, _, hp, _⟩ := h; ⟨l, r, T, hl, hr, hp⟩

/-- **Two capabilities over one key of one object share a role.** -/
theorem Holds.common {a b : Capability} {k : Nat} {W : WorldT k} {flds : List (PropKey × Nat)}
    (hk : a.key = b.key) (ha : a.Holds W flds) (hb : b.Holds W flds) :
    ∃ r A B, a.permits r A ∧ b.permits r B := by
  obtain ⟨l, r, A, hl, hr, hp⟩ := ha.role
  obtain ⟨l', r', B, hl', hr', hp'⟩ := hb.role
  rw [hk, hl'] at hl; cases hl
  rw [hr'] at hr; cases hr
  exact ⟨r, A, B, hp, hp'⟩

/-- `a` grants no more than `b`: the same key, and every pair `a` permits
`b` permits. -/
def le (a b : Capability) : Prop := a.key = b.key ∧ ∀ r T, a.permits r T → b.permits r T

theorem Holds.weaken {a b : Capability} (hle : a.le b) {k : Nat} {W : WorldT k}
    {flds : List (PropKey × Nat)} (h : a.Holds W flds) : b.Holds W flds :=
  let ⟨l, hl, r, c, T, hr, hc, hp, hag⟩ := h
  ⟨l, hle.1 ▸ hl, r, c, T, hr, hc, hle.2 r T hp, hag⟩

/-- **A write through a capability keeps the heap well-formed**: the contents
have the shape of the target's role and meet each type the capability pairs
with that role, at every lower budget. -/
theorem At.write {cap : Capability} {n : Nat} {W : WorldT n} {h : Heap} {l : Nat} {v : Val}
    (hok : HeapOk n W h) (hat : cap.At W l)
    (hv : ∀ r T, roleAt W l = some r → cap.permits r T →
      Shape W r v ∧ ∀ (j : Nat) (hj : j < n), T j (Kinds.trunc j (Nat.le_of_lt hj) W) v) :
    HeapOk n W (h.set l v) := by
  obtain ⟨r, c, T, hr, hl, hp, hc⟩ := hat
  obtain ⟨hs, ht⟩ := hv r T hr hp
  exact write_sound n W h l c r v hok hl hr (fun j hj => (hc j hj _ v).mpr (ht j hj)) hs

/-! ## The constructions -/

/-- An ordinary property of type `A`: a field location. -/
def field (f : PropKey) (A : Fam) : Capability := ⟨f, fun r T => r = .field ∧ T = A⟩

/-- A binding's storage of type `A`: a cell, under the binding wrapper's
key. -/
def binding (A : Fam) : Capability := ⟨valueField, fun r T => r = .cell ∧ T = A⟩

/-- An ordinary array's store, of the store type `A`. -/
def arrayStore (A : Fam) : Capability := ⟨arrayStoreKey, fun r T => r = .store .array ∧ T = A⟩

/-- A typed array's element store: a view store of some length `N`, of the
store type `A N`. -/
def viewStore (A : Nat → Fam) : Capability :=
  ⟨viewElementsKey, fun r T => ∃ N, r = .store (.view N) ∧ T = A N⟩

theorem objectEntries_snd {k : Nat} {rs : List Role} {cs : List (Ctr k)} {cid : Ctr k}
    (h : rs.length = cs.length) : (objectEntries rs cs cid).map Prod.snd = cs ++ [cid] := by
  simp [objectEntries, List.map_snd_zip, h]

/-- **Allocation establishes a capability.** In the world an object
allocation extends by the entries its rule chose (`objectEntries`: the `i`-th
named field the role `rs[i]` and the contract of the type `As[i]`), a
capability over the `i`-th key permitting that role with that type holds of
the allocated object's field map. -/
theorem holds_alloc {k : Nat} (W : WorldT k) {ns : List PropKey} {rs : List Role} {As : List Fam}
    (cid : Ctr k) (hnd : ns.Nodup) (hrs : rs.length = ns.length) (hAs : As.length = ns.length)
    {i : Nat} (hi : i < ns.length) {cap : Capability} (hk : cap.key = ns[i])
    (hp : cap.permits (rs[i]'(by omega)) (As[i]'(by omega))) :
    cap.Holds (appendWs W (objectEntries rs (As.map res) cid)) (slots (entries W).length ns) := by
  refine ⟨(entries W).length + i, by rw [hk]; exact lookup_slots hnd hi,
    rs[i]'(by omega), res (As[i]'(by omega)), As[i]'(by omega), ?_, ?_, hp, fun _ _ _ _ => Iff.rfl⟩
  · rw [roleAt_appendWs', objectEntries_fst (by simp; omega),
      List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
  · rw [lookup_appendWs_ge, objectEntries_snd (by simp; omega),
      List.getElem?_append_left (by simp; omega), List.getElem?_eq_getElem (by simp; omega)]
    simp

/-- **An object literal's property is a field**: the allocation of
`{value: v}` with the role `field` establishes the field capability. -/
theorem field_holds_literal {k : Nat} (W : WorldT k) (A : Fam) (cid : Ctr k) :
    (field valueField A).Holds (appendWs W (objectEntries [.field] [res A] cid))
      [(valueField, (entries W).length)] :=
  holds_alloc W (ns := [valueField]) (rs := [.field]) (As := [A]) cid (by simp) rfl rfl
    (i := 0) (by simp) rfl ⟨rfl, rfl⟩

/-- **A binding cell's storage is a cell**: the same allocation with the role
`cell` establishes the binding capability. -/
theorem binding_holds_cell {k : Nat} (W : WorldT k) (A : Fam) (cid : Ctr k) :
    (binding A).Holds (appendWs W (objectEntries [.cell] [res A] cid))
      [(valueField, (entries W).length)] :=
  holds_alloc W (ns := [valueField]) (rs := [.cell]) (As := [A]) cid (by simp) rfl rfl
    (i := 0) (by simp) rfl ⟨rfl, rfl⟩

/-- **An array's store slot is an array store.** -/
theorem arrayStore_holds_array {k : Nat} (W : WorldT k) (A : Fam) (cid : Ctr k) :
    (arrayStore A).Holds (appendWs W (objectEntries [.store .array] [res A] cid))
      [(arrayStoreKey, (entries W).length)] :=
  holds_alloc W (ns := [arrayStoreKey]) (rs := [.store .array]) (As := [A]) cid (by simp) rfl rfl
    (i := 0) (by simp) rfl ⟨rfl, rfl⟩

/-- A field write's target is a field location, a binding write's a cell. -/
theorem field_role {f : PropKey} {A : Fam} {k : Nat} {W : WorldT k} {flds : List (PropKey × Nat)}
    (h : (field f A).Holds W flds) : ∃ l, flds.lookup f = some l ∧ roleAt W l = some .field := by
  obtain ⟨l, r, T, hl, hr, rfl, -⟩ := h.role
  exact ⟨l, hl, hr⟩

theorem binding_role {A : Fam} {k : Nat} {W : WorldT k} {flds : List (PropKey × Nat)}
    (h : (binding A).Holds W flds) : ∃ l, flds.lookup valueField = some l ∧ roleAt W l = some .cell := by
  obtain ⟨l, r, T, hl, hr, rfl, -⟩ := h.role
  exact ⟨l, hl, hr⟩

/-! ## The meaning of a storage role

A type's storage position states a role tag (`StorageRole`); its meaning is
the capability permitting the roles the tag names, each with the position's
contents type. -/

end Capability

/-- The roles a storage role tag names. -/
def _root_.Verification.StorageRole.permits : StorageRole → Role → Prop
  | .field, r => r = .field
  | .cell, r => r = .cell
  | .arrayStore, r => r = .store .array
  | .viewStore, r => ∃ N, r = .store (.view N)

/-- **Distinct tags name disjoint roles**: a role determines the tag naming it. -/
theorem _root_.Verification.StorageRole.permits_unique {s s' : StorageRole} {r : Role}
    (h : s.permits r) (h' : s'.permits r) : s = s' := by
  cases s <;> cases s' <;> simp only [StorageRole.permits] at h h' <;>
    first | rfl | (subst h; simp_all) | (obtain ⟨N, rfl⟩ := h; simp_all)

/-- Every tag names some role. -/
theorem _root_.Verification.StorageRole.inhabited (s : StorageRole) : ∃ r, s.permits r := by
  cases s
  · exact ⟨.field, rfl⟩
  · exact ⟨.cell, rfl⟩
  · exact ⟨.store .array, rfl⟩
  · exact ⟨.store (.view 0), 0, rfl⟩

namespace Capability

/-- **The capability a storage position states**: its key, and each role its
tag names paired with its contents type. -/
def ofRole (s : StorageRole) (k : PropKey) (A : Fam) : Capability :=
  ⟨k, fun r T => s.permits r ∧ T = A⟩

/-- The constructions are the capabilities of their tags. -/
theorem ofRole_field (f : PropKey) (A : Fam) : ofRole .field f A = field f A := rfl
theorem ofRole_cell (A : Fam) : ofRole .cell valueField A = binding A := rfl
theorem ofRole_arrayStore (A : Fam) : ofRole .arrayStore arrayStoreKey A = arrayStore A := rfl
theorem ofRole_viewStore (A : Fam) : ofRole .viewStore viewElementsKey A = viewStore (fun _ => A) := by
  simp only [ofRole, viewStore, StorageRole.permits]
  congr; funext r T; apply propext
  constructor
  · rintro ⟨⟨N, rfl⟩, rfl⟩; exact ⟨N, rfl, rfl⟩
  · rintro ⟨N, rfl, rfl⟩; exact ⟨⟨N, rfl⟩, rfl⟩

/-- **A storage position's lookup exposes a role its tag names.** -/
theorem ofRole_role {s : StorageRole} {key : PropKey} {A : Fam} {k : Nat} {W : WorldT k}
    {flds : List (PropKey × Nat)} (h : (ofRole s key A).Holds W flds) :
    ∃ l r, flds.lookup key = some l ∧ roleAt W l = some r ∧ s.permits r := by
  obtain ⟨l, r, T, hl, hr, hp, -⟩ := h.role
  exact ⟨l, r, hl, hr, hp⟩

/-- **One key of one object has one tag**: two storage positions over the
same key that both hold state the same role tag. -/
theorem ofRole_exclusive {s s' : StorageRole} {key : PropKey} {A B : Fam} {k : Nat}
    {W : WorldT k} {flds : List (PropKey × Nat)}
    (h : (ofRole s key A).Holds W flds) (h' : (ofRole s' key B).Holds W flds) : s = s' := by
  obtain ⟨r, _, _, ⟨hs, -⟩, ⟨hs', -⟩⟩ := Holds.common (a := ofRole s key A) (b := ofRole s' key B) rfl h h'
  exact StorageRole.permits_unique hs hs'

/-- **Inclusion keeps the tag**: a storage position grants no more than
another only with the same key, the same tag and the same contents type. -/
theorem ofRole_le {s s' : StorageRole} {k k' : PropKey} {A B : Fam}
    (h : (ofRole s k A).le (ofRole s' k' B)) : k = k' ∧ s = s' ∧ A = B := by
  obtain ⟨r, hr⟩ := s.inhabited
  obtain ⟨hs', hAB⟩ := h.2 r A ⟨hr, rfl⟩
  exact ⟨h.1, StorageRole.permits_unique hr hs', hAB⟩

/-- **Allocation establishes each storage position whose tag names the role
the allocation chose**: the `i`-th key of an object allocated with roles `rs`
and types `As`. -/
theorem ofRole_holds_alloc {k : Nat} (W : WorldT k) {ns : List PropKey} {rs : List Role}
    {As : List Fam} (cid : Ctr k) (hnd : ns.Nodup) (hrs : rs.length = ns.length)
    (hAs : As.length = ns.length) {i : Nat} (hi : i < ns.length) {s : StorageRole}
    (hs : s.permits (rs[i]'(by omega))) :
    (ofRole s ns[i] (As[i]'(by omega))).Holds (appendWs W (objectEntries rs (As.map res) cid))
      (slots (entries W).length ns) :=
  holds_alloc W cid hnd hrs hAs hi rfl ⟨hs, rfl⟩

/-- **A binding capability cannot be read as a field capability**: of one
object, at any world, not both hold (an instance of `ofRole_exclusive`). -/
theorem binding_not_field {A B : Fam} {k : Nat} {W : WorldT k} {flds : List (PropKey × Nat)}
    (hb : (binding A).Holds W flds) : ¬ (field valueField B).Holds W flds := fun hf =>
  nomatch ofRole_exclusive (s := .cell) (s' := .field) hb hf

/-- No inclusion takes a binding capability to a field capability (an
instance of `ofRole_le`). -/
theorem binding_not_le_field (A B : Fam) : ¬ (binding A).le (field valueField B) := fun h =>
  nomatch (ofRole_le (s := .cell) (s' := .field) h).2.1

/-- A binding's storage and an ordinary property are distinct tags, so of
one object at most one holds over a key (`binding_not_field`), and neither
grants the other. -/
theorem cell_ne_field : StorageRole.cell ≠ StorageRole.field := by decide

end Capability

end Verification.Kinds
