import Verification.Semantics.FootprintRebase
import Verification.Semantics.Support

/-! # Regions bounded by role classes

A region's **bound** (`Region.bound`) is a set of role classes
(`RoleClass`, `Semantics/Worlds.lean`) that holds the class of the role of
every allocated location in the region, at every well-formed state: a heap
satisfying its world (`HeapOk`) and an environment whose roots are valid
(`RootsOk`), `Region.bound_sound`. Two regions whose bounds have no class in
common share no allocated location (`Region.apart_of_bound`): the note
*Tolerant frames*, §3, two regions are disjoint when no kind of location
belongs to both. The query `boundQuery` answers by bounds.

The bound is read from the region's form alone:

- a field at a key is a slot of the key's role (`SlotRole`): an array spine
  at the spine key, a field or a cell at every other key;
- an object's field locations are slots under keys other than the spine
  key: field, cell;
- the cells a spine lists are element cells (`HeapOk.entries_cells`);
- the spine a path selects is an array spine or a view spine
  (`HeapKnowledge.elementsOf`);
- a class region holds the classes of the categories its selector names
  (`Shaped.category`);
- `inCls r c` holds the classes of both `r`'s bound and `c`'s categories;
- `all` holds every class. -/
namespace Verification.Footprints
open HeapKnowledge

/-! ## Bounds -/

/-- Field and cell. -/
def RoleSet.fieldsAndCells : RoleSet := ⟨true, true, false, false, false, false⟩

/-- The array spine. -/
def RoleSet.arraySpine : RoleSet := ⟨false, false, false, true, false, false⟩

/-- Element cells. -/
def RoleSet.elems : RoleSet := ⟨false, false, true, false, false, false⟩

/-- Array spines and view spines. -/
def RoleSet.spines : RoleSet := ⟨false, false, false, true, true, false⟩

/-- The role classes of the categories a selector names. -/
def Selector.roles (c : Selector) : RoleSet := RoleSet.ofCategories c.has

/-- The classes a slot under `k` may have (`SlotRole`): the array spine
under the spine key, a field or a cell under every other key. -/
def slotBound (k : PropKey) : RoleSet :=
  if k = arraySpineKey then RoleSet.arraySpine else RoleSet.fieldsAndCells

/-- **A region's bound**: a set of role classes holding the class of every
allocated location of the region in a well-formed state
(`Region.bound_sound`). -/
def Region.bound : Region → RoleSet
  | .field _ k | .path _ _ k => slotBound k
  | .fields _ | .pathFields _ _ => RoleSet.fieldsAndCells
  | .cells _ | .pathCells _ _ => RoleSet.elems
  | .cls c => c.roles
  | .all => RoleSet.all
  | .inCls r c => r.bound.inter c.roles
  | .spine _ _ => RoleSet.spines

/-! ## Valid references along paths -/

/-- **A path read from a value with valid references reads a value with
valid references**, in a well-formed heap. -/
theorem readPath_refs {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) :
    ∀ {v v' : Val} (p : List String), RefsOk W v → readPath h v p = some v' → RefsOk W v'
  | v, v', [], hv, hr => by simp [readPath] at hr; subst hr; exact hv
  | v, v', f :: p, hv, hr => by
    cases v with
    | objAt fs c i =>
      simp only [readPath] at hr
      split at hr
      · rename_i l _
        split at hr
        · rename_i u hu
          exact readPath_refs hok p (hok.refs_at hu) hr
        · cases hr
      · cases hr
    | _ => simp [readPath] at hr

/-- An object's slot is among its references. -/
theorem slot_mem_refs {fs : List (PropKey × Nat)} {c : CallCode} {i : Nat} {k : PropKey} {l : Nat}
    (hkl : (k, l) ∈ fs) : Ref.slot k l ∈ refs (.objAt fs c i) := by
  have : Ref.slot k l ∈ objRefs fs i := by
    simp only [objRefs, List.mem_cons, List.mem_map, reduceCtorEq, false_or]
    exact ⟨(k, l), hkl, rfl⟩
  cases c <;> simp only [refs] <;> first | exact this | exact List.mem_append_left _ this

/-! ## Each form's bound -/

theorem slotBound_sound {n : Nat} {W : WorldT n} {k : PropKey} {l : Nat}
    (hs : SlotRole k (roleAt W l)) :
    ∃ role, roleAt W l = some role ∧ (slotBound k).contains role.cls = true := by
  rcases hr : roleAt W l with _ | role
  · rw [hr] at hs; cases hs
  · rw [hr] at hs
    refine ⟨role, rfl, ?_⟩
    cases role with
    | spine f =>
      cases f with
      | array => simp only [SlotRole] at hs; simp [slotBound, hs, Role.cls, RoleSet.contains, RoleSet.arraySpine]
      | view => simp [SlotRole] at hs
    | field | cell =>
      simp only [SlotRole] at hs
      simp [slotBound, hs.2, Role.cls, RoleSet.contains, RoleSet.fieldsAndCells]
    | _ => simp [SlotRole] at hs

/-- A field of a value with valid references (`field`, `path`). -/
theorem field_bound {n : Nat} {W : WorldT n} {v : Val} (hv : RefsOk W v) {k : PropKey} {l : Nat}
    (hm : ((fieldsOf v).lookup k == some l) = true) :
    ∃ role, roleAt W l = some role ∧ (slotBound k).contains role.cls = true :=
  slotBound_sound (slotRole_of_refs hv (by simpa using hm))

/-- A field location of a value with valid references (`fields`,
`pathFields`): a slot under a key other than the spine key. -/
theorem fields_bound {n : Nat} {W : WorldT n} {v : Val} (hv : RefsOk W v) {l : Nat}
    (hm : (fieldLocs v).contains l = true) :
    ∃ role, roleAt W l = some role ∧ RoleSet.fieldsAndCells.contains role.cls = true := by
  cases v with
  | objAt fs c i =>
    simp only [fieldLocs, fieldsOf, List.contains_iff_mem, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq] at hm
    obtain ⟨⟨k, l'⟩, ⟨hkl, hk⟩, rfl⟩ := hm
    have hb := slotBound_sound (hv _ (slot_mem_refs (c := c) (i := i) hkl))
    simpa [slotBound, hk] using hb
  | _ => simp [fieldLocs, fieldsOf] at hm

/-- A cell a value's spines list (`cells`, `pathCells`): an element cell
(`HeapOk.entries_cells`). -/
theorem cells_bound {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) {v : Val} {l : Nat}
    (hm : (spineCells h v).contains (some l) = true) :
    ∃ role, roleAt W l = some role ∧ RoleSet.elems.contains role.cls = true := by
  have key : ∀ o : Option Nat, some l ∈ entriesAt h o → roleAt W l = some .elem := by
    intro o ho
    cases o with
    | none => simp [entriesAt] at ho
    | some s =>
      simp only [entriesAt] at ho
      cases he : h[s]?.bind spineEntries with
      | none => rw [he] at ho; simp at ho
      | some ls =>
        rw [he] at ho
        exact (hok.entries_cells he (by simpa using ho)).1
  simp only [spineCells, List.contains_iff_mem, List.mem_append] at hm
  have hr : roleAt W l = some .elem := hm.elim (key _) (key _)
  exact ⟨.elem, hr, rfl⟩

/-- The spine a value with valid references selects (`spine`): an array
spine under its spine key, or the view spine its descriptor names. -/
theorem spine_bound {n : Nat} {W : WorldT n} {v : Val} (hv : RefsOk W v) {l : Nat}
    (hm : (elementsOf v == some l) = true) :
    ∃ role, roleAt W l = some role ∧ RoleSet.spines.contains role.cls = true := by
  cases v with
  | objAt fs c i =>
    simp only [elementsOf, beq_iff_eq] at hm
    cases hk : fs.lookup arraySpineKey with
    | some s =>
      rw [hk] at hm; cases hm
      have hs := slotRole_of_refs hv (k := arraySpineKey) (l := l) (by simpa [fieldsOf] using hk)
      rcases hr : roleAt W l with _ | role
      · rw [hr] at hs; cases hs
      · rw [hr] at hs
        refine ⟨role, rfl, ?_⟩
        cases role with
        | spine f => cases f <;> rfl
        | _ => simp [SlotRole] at hs
    | none =>
      rw [hk] at hm
      cases c with
      | view s f m =>
        cases hm
        have hmem : Ref.view l f m (fs.lookup arraySpineKey).isNone ∈ refs (.objAt fs (.view l f m) i) := by
          simp [refs]
        have hr : roleAt W l = some (.spine (.view f m)) := (hv _ hmem).2
        exact ⟨_, hr, rfl⟩
      | _ => simp at hm
  | _ => simp [elementsOf] at hm

/-- An allocated location of a well-formed heap whose contents a selector
selects has a role of the selector's classes (`Shaped.category`). -/
theorem selects_bound {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) {c : Selector}
    {l : Nat} {v : Val} (hv : h[l]? = some v) (hs : c.selects v = true) :
    ∃ role, roleAt W l = some role ∧ c.roles.contains role.cls = true := by
  have hlt : l < (entries W).length := by
    have := (List.getElem?_eq_some_iff.mp hv).1; have := hok.1.1; simp at this; omega
  obtain ⟨role, hr⟩ := roleAt_some hlt
  refine ⟨role, hr, ?_⟩
  have hcat := Shaped.category hok.2 hr hv
  simpa [Selector.roles, Selector.selects, hcat] using hs

/-! ## Soundness -/

/-- **Bound soundness**: in a well-formed state, every allocated location
of a region has a role of a class the region's bound holds. -/
theorem Region.bound_sound {n : Nat} {W : WorldT n} {h : Heap} {ρ : Env}
    (hok : HeapOk n W h) (hρ : RootsOk W ρ) :
    ∀ (r : Region) {l : Nat}, l < h.length → r.mem ρ h l = true →
      ∃ role, roleAt W l = some role ∧ r.bound.contains role.cls = true
  | .field x k, _, _, hm => field_bound (hρ x) hm
  | .fields x, _, _, hm => fields_bound (hρ x) hm
  | .cells _, _, _, hm => cells_bound hok hm
  | .cls c, l, _, hm => by
    simp only [Region.mem] at hm
    split at hm
    · rename_i v hv; exact selects_bound hok hv hm
    · cases hm
  | .all, l, hl, _ => by
    obtain ⟨role, hr⟩ := roleAt_some (W := W) (l := l) (by have := hok.1.1; simp at this; omega)
    exact ⟨role, hr, RoleSet.contains_all _⟩
  | .path x p k, _, _, hm => by
    simp only [Region.mem] at hm
    split at hm
    · rename_i v hv; exact field_bound (readPath_refs hok p (hρ x) hv) hm
    · cases hm
  | .pathFields x p, _, _, hm => by
    simp only [Region.mem] at hm
    split at hm
    · rename_i v hv; exact fields_bound (readPath_refs hok p (hρ x) hv) hm
    · cases hm
  | .pathCells _ _, _, _, hm => by
    simp only [Region.mem] at hm
    split at hm
    · exact cells_bound hok hm
    · cases hm
  | .inCls r c, l, hl, hm => by
    simp only [Region.mem, Bool.and_eq_true] at hm
    obtain ⟨role, hr, hb⟩ := Region.bound_sound hok hρ r hl hm.1
    have hc := hm.2
    split at hc
    · rename_i v hv
      obtain ⟨role', hr', hc'⟩ := selects_bound hok hv hc
      rw [hr] at hr'; cases hr'
      exact ⟨role, hr, by simp [Region.bound, hb, hc']⟩
    · cases hc
  | .spine x p, _, _, hm => by
    simp only [Region.mem] at hm
    split at hm
    · rename_i v hv; exact spine_bound (readPath_refs hok p (hρ x) hv) hm
    · cases hm

/-- **Regions whose bounds hold no class in common share no allocated
location**, in a well-formed state. -/
theorem Region.apart_of_bound {n : Nat} {W : WorldT n} {h : Heap} {ρ : Env}
    (hok : HeapOk n W h) (hρ : RootsOk W ρ) {r s : Region}
    (hd : (r.bound.inter s.bound).isEmpty = true) {l : Nat} (hl : l < h.length)
    (hr : r.mem ρ h l = true) (hs : s.mem ρ h l = true) : False := by
  obtain ⟨role, hrole, hb⟩ := Region.bound_sound hok hρ r hl hr
  obtain ⟨role', hrole', hb'⟩ := Region.bound_sound hok hρ s hl hs
  rw [hrole] at hrole'; cases hrole'
  rw [RoleSet.inter_isEmpty hd hb] at hb'
  cases hb'

/-! ## Class regions -/

/-- **Two selectors' role classes are apart exactly when the selectors
are**: no category in both. -/
theorem Selector.roles_inter_isEmpty (a b : Selector) : (a.roles.inter b.roles).isEmpty = a.disjoint b := by
  rcases a with ⟨a1, a2, a3⟩
  rcases b with ⟨b1, b2, b3⟩
  cases a1 <;> cases a2 <;> cases a3 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

/-- **Class regions whose bounds hold no class in common share no
location**, in a heap meeting its world: a class region's bound needs no
valuation. -/
theorem Region.cls_apart_of_bound {n : Nat} {W : WorldT n} {h : Heap} {ρ : Env} (hok : HeapOk n W h)
    {c c' : Selector} (hd : ((Region.cls c).bound.inter (Region.cls c').bound).isEmpty = true) {l : Nat}
    (hc : (Region.cls c).mem ρ h l = true) (hc' : (Region.cls c').mem ρ h l = true) : False := by
  simp only [Region.mem] at hc hc'
  simp only [Region.bound] at hd
  split at hc
  · rename_i v hv
    rw [hv] at hc'
    obtain ⟨role, hrole, hb⟩ := selects_bound hok hv hc
    obtain ⟨role', hrole', hb'⟩ := selects_bound hok hv hc'
    rw [hrole] at hrole'; cases hrole'
    rw [RoleSet.inter_isEmpty hd hb] at hb'
    cases hb'
  · cases hc

/-! ## Keys

A field or a cell location has a key fixed at its allocation (the note
*Tolerant frames*, §3 and (W3)), which the world records in its role
(`Role.key?`). A region at a field `k`, read from any value, holds only
locations of the key `k`: a slot under `k` is a location of `k`'s role
(`SlotRole`). So two regions at different keys share no location, whatever
the values they are read from (the note, Definition "Derivations": $`\pi.f`$
and $`\pi'.g`$ with $`f\ne g`$ are disjoint). -/

/-- **The key of a region's locations**, where the region's form fixes one:
the key `k` of a field or a path's field `k` other than the spine key, and
the key of `r` for its part in a class. -/
def Region.key? : Region → Option PropKey
  | .field _ k | .path _ _ k => if k = arraySpineKey then none else some k
  | .inCls r _ => r.key?
  | _ => none

/-- A slot under a key other than the spine key is a location of that
key. -/
theorem slotRole_key {n : Nat} {W : WorldT n} {k : PropKey} {l : Nat} (hk : k ≠ arraySpineKey)
    (hs : SlotRole k (roleAt W l)) : ∃ role, roleAt W l = some role ∧ role.key? = some k := by
  rcases hr : roleAt W l with _ | role
  · rw [hr] at hs; cases hs
  · rw [hr] at hs
    refine ⟨role, rfl, ?_⟩
    cases role with
    | field k' => simp only [SlotRole] at hs; simp [Role.key?, hs.1]
    | cell k' => simp only [SlotRole] at hs; simp [Role.key?, hs.1]
    | spine f => cases f <;> simp [SlotRole] at hs; exact absurd hs hk
    | _ => simp [SlotRole] at hs

/-- **Key soundness**: in a well-formed state, every allocated location of a
region whose form fixes a key is a location of that key. -/
theorem Region.key_sound {n : Nat} {W : WorldT n} {h : Heap} {ρ : Env}
    (hok : HeapOk n W h) (hρ : RootsOk W ρ) :
    ∀ (r : Region) {k : PropKey} {l : Nat}, r.key? = some k → r.mem ρ h l = true →
      ∃ role, roleAt W l = some role ∧ role.key? = some k
  | .field x k', k, l, hk, hm => by
    simp only [Region.key?] at hk
    split at hk
    · cases hk
    · rename_i hne; cases hk
      exact slotRole_key hne (slotRole_of_refs (hρ x) (by simpa [Region.mem] using hm))
  | .path x p k', k, l, hk, hm => by
    simp only [Region.key?] at hk
    split at hk
    · cases hk
    · rename_i hne; cases hk
      simp only [Region.mem] at hm
      split at hm
      · rename_i v hv
        exact slotRole_key hne (slotRole_of_refs (readPath_refs hok p (hρ x) hv) (by simpa using hm))
      · cases hm
  | .inCls r c, k, l, hk, hm => by
    simp only [Region.mem, Bool.and_eq_true] at hm
    exact Region.key_sound hok hρ r (by simpa [Region.key?] using hk) hm.1
  | .fields _, _, _, hk, _ | .cells _, _, _, hk, _ | .cls _, _, _, hk, _ | .all, _, _, hk, _
  | .pathFields _ _, _, _, hk, _ | .pathCells _ _, _, _, hk, _ | .spine _ _, _, _, hk, _ => by
    simp [Region.key?] at hk

/-- **Regions at different keys**: both fix a key, and the keys differ. -/
def Region.keysApart (r s : Region) : Bool :=
  match r.key?, s.key? with
  | some a, some b => a != b
  | _, _ => false

theorem Region.keysApart_symm (r s : Region) : r.keysApart s = s.keysApart r := by
  unfold Region.keysApart
  cases r.key? <;> cases s.key? <;> simp [bne_comm]

/-- **Regions at different keys share no location**, in a well-formed
state (the note, Definition "Derivations": $`\pi.f`$ and $`\pi'.g`$ with
$`f\ne g`$ are disjoint, whatever $`\pi`$ and $`\pi'`$ read). -/
theorem Region.apart_of_keys {n : Nat} {W : WorldT n} {h : Heap} {ρ : Env}
    (hok : HeapOk n W h) (hρ : RootsOk W ρ) {r s : Region} (hd : r.keysApart s = true) {l : Nat}
    (hr : r.mem ρ h l = true) (hs : s.mem ρ h l = true) : False := by
  unfold Region.keysApart at hd
  split at hd
  · rename_i a b ha hb
    obtain ⟨role, hrole, hk⟩ := Region.key_sound hok hρ r ha hr
    obtain ⟨role', hrole', hk'⟩ := Region.key_sound hok hρ s hb hs
    rw [hrole] at hrole'; cases hrole'
    rw [hk] at hk'; cases hk'
    simp at hd
  · cases hd

/-! ## The query by bounds -/

/-- **Disjointness by bounds** (the note, §3: no kind of location belongs
to both, and Definition "Derivations": no key belongs to both): two regions
whose bounds hold no role class in common, or whose forms fix different
keys. -/
def boundQuery : SepQuery := ⟨fun r s => (r.bound.inter s.bound).isEmpty || r.keysApart s⟩

/-- Bounds with no class in common answer the query. -/
theorem boundQuery_of_isEmpty {r s : Region} (h : (r.bound.inter s.bound).isEmpty = true) :
    boundQuery.disjoint r s = true := by
  simp [boundQuery, h]

/-- **The query by bounds is sound** at a heap meeting its world with
valid roots (`Region.apart_of_bound`, `Region.apart_of_keys`). -/
theorem boundQuery_sound {n : Nat} {W : WorldT n} {h : Heap} {ρ : Env} (hok : HeapOk n W h)
    (hρ : RootsOk W ρ) : boundQuery.Sound ρ h := by
  intro _ _ _ hl hd hr hs
  simp only [boundQuery, Bool.or_eq_true] at hd
  rcases hd with hd | hd
  · exact Region.apart_of_bound hok hρ hd hl hr hs
  · exact Region.apart_of_keys hok hρ hd hr hs

/-- **The query by bounds separates every pair of a class region and a
region's part in a disjoint class**, the part `inCls r c` against
`cls c'` either way round. -/
theorem boundQuery_inCls_cls (r : Region) {c c' : Selector} (hd : c.disjoint c' = true) :
    boundQuery.disjoint (.inCls r c) (.cls c') = true ∧ boundQuery.disjoint (.cls c') (.inCls r c) = true := by
  have h0 : ∀ cl, (c.roles.contains cl && c'.roles.contains cl) = false := by
    intro cl
    have := RoleSet.isEmpty_iff.mp ((Selector.roles_inter_isEmpty c c').trans hd) cl
    simpa using this
  simp only [boundQuery, Region.bound, Bool.or_eq_true]
  constructor <;> refine .inl (RoleSet.isEmpty_iff.mpr fun cl => ?_) <;> have := h0 cl <;>
    simp only [RoleSet.contains_inter] <;> revert this <;>
    cases r.bound.contains cl <;> cases c.roles.contains cl <;> cases c'.roles.contains cl <;> simp

end Verification.Footprints
