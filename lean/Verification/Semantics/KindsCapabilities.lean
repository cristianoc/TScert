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

/-- `a` grants no more than `b` below the budget `k`: the same key, and each
pair `a` permits `b` permits with a contents type agreeing below `k`. This
is inclusion up to the semantic equivalence covering proves. -/
def leBelow (k : Nat) (a b : Capability) : Prop :=
  a.key = b.key ∧ ∀ r T, a.permits r T → ∃ T', b.permits r T' ∧
    ∀ (j : Nat), j < k → ∀ (W : WorldT j) (v : Val), T j W v ↔ T' j W v

/-- **Inclusion up to agreement keeps a capability's meaning.** -/
theorem Holds.weakenBelow {a b : Capability} {k : Nat} {W : WorldT k} {flds : List (PropKey × Nat)}
    (hle : leBelow k a b) (h : a.Holds W flds) : b.Holds W flds :=
  let ⟨l, hl, r, c, T, hr, hc, hp, hag⟩ := h
  let ⟨T', hp', hTT⟩ := hle.2 r T hp
  ⟨l, hle.1 ▸ hl, r, c, T', hr, hc, hp', fun j hj W' u => (hag j hj W' u).trans (hTT j hj W' u)⟩

/-- **Inclusion of storage positions up to agreement**: one position grants
no more than another below `k` exactly when they state the same key and the
same tag, and their contents types agree below `k`. The literal equality of
`ofRole_le` is its instance at equal types. -/
theorem ofRole_leBelow_iff {s s' : StorageRole} {key key' : PropKey} {A B : Fam} {k : Nat} :
    (ofRole s key A).leBelow k (ofRole s' key' B) ↔
      key = key' ∧ s = s' ∧ ∀ (j : Nat), j < k → ∀ (W : WorldT j) (v : Val), A j W v ↔ B j W v := by
  constructor
  · rintro ⟨hk, h⟩
    obtain ⟨r, hr⟩ := s.inhabited
    obtain ⟨T', ⟨hs', rfl⟩, hag⟩ := h r A ⟨hr, rfl⟩
    exact ⟨hk, StorageRole.permits_unique hr hs', hag⟩
  · rintro ⟨hk, rfl, hag⟩
    exact ⟨hk, fun r T ⟨hs, hT⟩ => ⟨B, ⟨hs, rfl⟩, by subst hT; exact hag⟩⟩

/-- A binding's storage and an ordinary property are distinct tags, so of
one object at most one holds over a key (`binding_not_field`), and neither
grants the other. -/
theorem cell_ne_field : StorageRole.cell ≠ StorageRole.field := by decide

end Capability

/-! ## Concrete allocation roles

An allocation's claim states each storage position's role as a tag; the
world entry the allocation appends records a role, a view store's with its
length. The role is the tag's, chosen by the allocated contents
(`StorageRole.concrete`): a view store's length is the length of the store
it is allocated holding. -/

/-- **The contents a tag's location holds**, by category: a source value
under a field or a cell, a store under a store slot. -/
def _root_.Verification.StorageRole.Holds : StorageRole → Val → Prop
  | .field, v | .cell, v => isSourceVal v = true
  | .arrayStore, v | .viewStore, v => ∃ ls, v = .arr ls

/-- **The role an allocation records** for a location whose position
states the tag `s`, allocated holding `v`: the tag's role, a view store's of
the length of the store `v`; none where `v` is not of the tag's category. -/
def _root_.Verification.StorageRole.concrete : StorageRole → Val → Option Role
  | .field, v => if isSourceVal v = true then some .field else none
  | .cell, v => if isSourceVal v = true then some .cell else none
  | .arrayStore, .arr _ => some (.store .array)
  | .viewStore, .arr ls => some (.store (.view ls.length))
  | _, _ => none

/-- **Tag to role**: the recorded role is one the tag names. -/
theorem _root_.Verification.StorageRole.concrete_permits {s : StorageRole} {v : Val} {r : Role}
    (h : s.concrete v = some r) : s.permits r := by
  unfold StorageRole.concrete at h
  split at h
  · split at h <;> cases h; rfl
  · split at h <;> cases h; rfl
  · cases h; rfl
  · cases h; exact ⟨_, rfl⟩
  · cases h

/-- **Initializer shape**: the allocated contents have the recorded role's
category, a view store's of its length. -/
theorem _root_.Verification.StorageRole.concrete_cat {s : StorageRole} {v : Val} {r : Role}
    (h : s.concrete v = some r) : Cat r v := by
  unfold StorageRole.concrete at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · split at h
    · cases h; assumption
    · cases h
  · cases h; exact ⟨_, rfl⟩
  · cases h; exact ⟨_, rfl, rfl⟩
  · cases h

/-- Contents of the tag's category determine a recorded role. -/
theorem _root_.Verification.StorageRole.concrete_of_holds {s : StorageRole} {v : Val}
    (h : s.Holds v) : ∃ r, s.concrete v = some r := by
  cases s with
  | field => exact ⟨.field, by simp [StorageRole.concrete, show isSourceVal v = true from h]⟩
  | cell => exact ⟨.cell, by simp [StorageRole.concrete, show isSourceVal v = true from h]⟩
  | arrayStore => obtain ⟨ls, rfl⟩ := h; exact ⟨_, rfl⟩
  | viewStore => obtain ⟨ls, rfl⟩ := h; exact ⟨_, rfl⟩

/-- **A view store's recorded length is its store's.** -/
theorem _root_.Verification.StorageRole.concrete_view {ls : List (Option Nat)} :
    StorageRole.viewStore.concrete (.arr ls) = some (.store (.view ls.length)) := rfl

/-- **Key fit** of a tag: an array store under `[]`, a view store under
`[[viewElements]]`, a field or a cell under every other key. -/
def _root_.Verification.StorageRole.fitsKey (s : StorageRole) (key : PropKey) : Bool :=
  if key = arrayStoreKey then s == .arrayStore
  else if key = viewElementsKey then s == .viewStore
  else s == .field || s == .cell

/-- **A tag fitting its key gives every role it names the slot's role.** -/
theorem _root_.Verification.StorageRole.slotRole_of_fitsKey {s : StorageRole} {key : PropKey} {r : Role}
    (hf : s.fitsKey key = true) (hp : s.permits r) : SlotRole key (some r) := by
  unfold StorageRole.fitsKey at hf
  by_cases h1 : key = arrayStoreKey
  · rw [if_pos h1] at hf
    have hs : s = .arrayStore := by simpa using hf
    subst hs
    simp only [StorageRole.permits] at hp
    subst hp
    exact h1
  · rw [if_neg h1] at hf
    by_cases h2 : key = viewElementsKey
    · rw [if_pos h2] at hf
      have hs : s = .viewStore := by simpa using hf
      subst hs
      obtain ⟨N, rfl⟩ := hp
      exact h2
    · rw [if_neg h2] at hf
      have hs : s = .field ∨ s = .cell := by simpa using hf
      rcases hs with rfl | rfl <;>
        (simp only [StorageRole.permits] at hp; subst hp; exact ⟨h1, h2⟩)

/-- **Metadata fit** of an allocation of the keys `ns` with roles `rs` and
contracts `cs`: each `[[viewLength]]` location is a field whose contract
admits one length `N` alone, and each `[[viewElements]]` location a view
store of a length `N` that the allocation's `[[viewLength]]` location
admits alone. -/
def MetaFit {k : Nat} (ns : List PropKey) (rs : List Role) (cs : List (Ctr k)) : Prop :=
  (∀ i : Nat, ns[i]? = some viewLengthKey →
    ∃ (N : Nat) (c : Ctr k), rs[i]? = some Role.field ∧ cs[i]? = some c ∧ CtrStable c (.num (bitsOfNat N))) ∧
  (∀ j : Nat, ns[j]? = some viewElementsKey → ∃ (N i : Nat) (c : Ctr k), rs[j]? = some (Role.store (.view N)) ∧
    ns[i]? = some viewLengthKey ∧ rs[i]? = some Role.field ∧ cs[i]? = some c ∧
      CtrStable c (.num (bitsOfNat N)))

/-- An allocation naming neither metadata key fits trivially. -/
theorem MetaFit.of_not_mem {k : Nat} {ns : List PropKey} {rs : List Role} {cs : List (Ctr k)}
    (hl : viewLengthKey ∉ ns) (he : viewElementsKey ∉ ns) : MetaFit ns rs cs :=
  ⟨fun _ hi => absurd (List.mem_of_getElem? hi) hl, fun _ hj => absurd (List.mem_of_getElem? hj) he⟩

/-- **View metadata of an allocated object**: an allocation whose roles and
contracts fit its metadata keys gives a field map with valid view
metadata. -/
theorem viewMetaOk_alloc {k : Nat} (W : WorldT k) {ns : List PropKey} {rs : List Role}
    {cs : List (Ctr k)} (cid : Ctr k) (hnd : ns.Nodup) (hrs : rs.length = ns.length)
    (hcs : cs.length = ns.length) (hfit : MetaFit ns rs cs) :
    ViewMetaOk (appendWs W (objectEntries rs cs cid)) (slots (entries W).length ns) := by
  have hfst := objectEntries_fst (cid := cid) (show rs.length = cs.length by omega)
  have hsnd := Capability.objectEntries_snd (cid := cid) (show rs.length = cs.length by omega)
  have hmeta : ∀ i N c, i < ns.length → rs[i]? = some .field → cs[i]? = some c →
      CtrStable c (.num (bitsOfNat N)) →
      LengthMeta (appendWs W (objectEntries rs cs cid)) ((entries W).length + i) N := by
    intro i N c hi hr hc hst
    refine ⟨c, ?_, ?_, hst⟩
    · rw [roleAt_appendWs', hfst, List.getElem?_append_left (by omega)]; exact hr
    · rw [lookup_appendWs_ge, hsnd, List.getElem?_append_left (by omega)]; exact hc
  refine ⟨fun m hm => ?_, fun e he => ?_⟩
  · obtain ⟨i, hi, hp⟩ := mem_slots hm
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hk, rfl⟩ := hp
    obtain ⟨N, c, hr, hc, hst⟩ := hfit.1 i (by rw [List.getElem?_eq_getElem hi, hk])
    exact ⟨N, hmeta i N c hi hr hc hst⟩
  · obtain ⟨j, hj, hp⟩ := mem_slots he
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hk, rfl⟩ := hp
    obtain ⟨N, i, c, hr, hni, hri, hc, hst⟩ := hfit.2 j (by rw [List.getElem?_eq_getElem hj, hk])
    have hi : i < ns.length := (List.getElem?_eq_some_iff.mp hni).1
    have hki : ns[i] = viewLengthKey := by
      have := List.getElem?_eq_getElem hi; rw [hni] at this; exact (Option.some.inj this).symm
    refine ⟨N, (entries W).length + i, ?_, ?_, hmeta i N c hi hri hc hst⟩
    · rw [roleAt_appendWs', hfst, List.getElem?_append_left (by omega)]; exact hr
    · rw [← hki]; exact lookup_slots hnd hi

/-- **The roles an allocation records**, one per position: each tag's
concrete role at its contents (`StorageRole.concrete`); none where a
contents is not of its tag's category. -/
def concreteRoles : List StorageRole → List Val → Option (List Role)
  | s :: ss, v :: vs => do
      let r ← s.concrete v
      let rs ← concreteRoles ss vs
      pure (r :: rs)
  | [], [] => some []
  | _, _ => none

theorem concreteRoles_spec : ∀ {ss : List StorageRole} {vs : List Val} {rs : List Role},
    concreteRoles ss vs = some rs →
      ss.length = vs.length ∧ rs.length = ss.length ∧
        ∀ (i : Nat) (s : StorageRole) (v : Val), ss[i]? = some s → vs[i]? = some v → ∃ r, rs[i]? = some r ∧ s.concrete v = some r
  | [], [], rs, h => by
    simp [concreteRoles] at h; subst h; exact ⟨rfl, rfl, fun i s v hs => by simp at hs⟩
  | [], _ :: _, _, h => by simp [concreteRoles] at h
  | _ :: _, [], _, h => by simp [concreteRoles] at h
  | s :: ss, v :: vs, rs, h => by
    simp only [concreteRoles, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs', hrs', rfl⟩ := h
    obtain ⟨h1, h2, h3⟩ := concreteRoles_spec hrs'
    refine ⟨by simp [h1], by simp [h2], fun i s' v' hs hv => ?_⟩
    cases i with
    | zero => simp at hs hv; subst hs hv; exact ⟨r, rfl, hr⟩
    | succ i => simpa using h3 i s' v' (by simpa using hs) (by simpa using hv)

/-- Contents each of its tag's category determine the recorded roles. -/
theorem concreteRoles_of_holds : ∀ {ss : List StorageRole} {vs : List Val},
    ss.length = vs.length → (∀ (i : Nat) (s : StorageRole) (v : Val), ss[i]? = some s → vs[i]? = some v → s.Holds v) →
      ∃ rs, concreteRoles ss vs = some rs
  | [], [], _, _ => ⟨[], rfl⟩
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | s :: ss, v :: vs, hl, h => by
    obtain ⟨r, hr⟩ := StorageRole.concrete_of_holds (h 0 s v rfl rfl)
    obtain ⟨rs, hrs⟩ := concreteRoles_of_holds (ss := ss) (vs := vs) (by simpa using hl)
      (fun i s' v' hs hv => h (i + 1) s' v' (by simpa using hs) (by simpa using hv))
    exact ⟨r :: rs, by simp [concreteRoles, hr, hrs]⟩

/-- **An allocation at concrete roles keeps kinds.** An object allocated
with keys `ns`, each position's tag `ss[i]` fitting its key and its
initializer of the tag's category, records for each key the role its tag
and its contents choose (`StorageRole.concrete`), and with contracts fitting
its metadata keys the extended heap is well-formed in its structural part
and the object's references are valid. -/
theorem concrete_shaped {k : Nat} {W : WorldT k} {h : Heap} {c : CallCode} {ns : List PropKey}
    {vs : List Tm} {ss : List StorageRole} {rs : List Role} (cs : List (Ctr k)) (cid : Ctr k)
    (hlen : h.length = (entries W).length) (hsh : Shaped W h) (hnd : ns.Nodup)
    (hss : ss.length = ns.length) (hcs : cs.length = ns.length) (hns : ns.length = vs.length)
    (hrs : concreteRoles ss vs = some rs)
    (href : RefsOk W (.makeAt c ns vs))
    (hfits : ∀ (i : Nat) (s : StorageRole), ss[i]? = some s → ∀ key : PropKey, ns[i]? = some key → s.fitsKey key = true)
    (hmeta : MetaFit ns rs cs) :
    Shaped (appendWs W (objectEntries rs cs cid)) (h ++ vs ++ [.nul]) ∧
      RefsOk (appendWs W (objectEntries rs cs cid)) (.objAt (slots h.length ns) c (h.length + vs.length)) := by
  obtain ⟨_, hrl', hri⟩ := concreteRoles_spec hrs
  have hrl : rs.length = ns.length := by omega
  have hat : ∀ i (hi : i < ns.length), ∃ s, ss[i]? = some s ∧
      s.concrete (vs[i]'(by omega)) = some (rs[i]'(by omega)) := by
    intro i hi
    obtain ⟨r, hr, hc⟩ := hri i (ss[i]'(by omega)) (vs[i]'(by omega)) (List.getElem?_eq_getElem _)
      (List.getElem?_eq_getElem _)
    rw [List.getElem?_eq_getElem (by omega)] at hr
    cases hr
    exact ⟨_, List.getElem?_eq_getElem _, hc⟩
  refine makeFields_shaped rs cs cid hlen hsh hrl hcs hns href
    (fun i hi => by
      obtain ⟨s, hs, hc⟩ := hat i hi
      exact StorageRole.slotRole_of_fitsKey (hfits i s hs _ (List.getElem?_eq_getElem hi))
        (StorageRole.concrete_permits hc))
    (fun i hi => by
      obtain ⟨s, hs, hc⟩ := hat i hi
      exact StorageRole.concrete_cat hc) ?_
  rw [hlen]
  exact viewMetaOk_alloc W cid hnd hrl hcs hmeta

end Verification.Kinds
