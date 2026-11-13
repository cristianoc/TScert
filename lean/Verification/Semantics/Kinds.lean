import Verification.Semantics.Calculus
/-!
# Fixed location kinds

The model of the note *Tolerant frames* (§§2–3) partitions a heap's locations
by **kind**, fixed for a location's life: field locations F, cells C, element
cells E, store locations S, and object-identity locations I
(docs/drafts/location-kinds.md). A kind is part of the world, which is
proof-level: the calculus (`Step`) and the lowering are those of
`Semantics/Calculus.lean`, and a location receives its role when a typing rule
extends the world at the allocation that justifies it.

A world entry here is a **role** beside the contract of `Semantics/Worlds.lean`.
`Kinds.WorldT` is the stratified construction of that module with a role in
each entry, and every name of its interface (`Ctr`, `toList`, `lookup`, `trunc`,
`WExt`, `appendW`, `appendWs`, `CtrAdm`, `WorldAdm`, `HeapOk`) is the name of the
existing one, so the activation of kinded worlds replaces the definitions of
those modules by these. A contract inspects kinded worlds below its level.

An object value's ordinary property locations have the role `field` or
`cell`: the role of a binding cell's single property is `cell`, given by the
rule that allocates the binding; the calculus allocates both as the same
object. Its array store slot `[]` has the role of an array store, its
`[[viewElements]]` slot that of a view store of a fixed length, its identity
the role `identity`. A store lists element cells only. F, C and E hold source
values whose references are valid (`RefsOk`); I holds `null`.
-/
namespace Verification.Kinds

/-! ## Kinds and roles -/

/-- The five kinds of location. -/
inductive Kind where
  | field | cell | elem | store | identity
  deriving DecidableEq, Repr

/-- The two forms of a store location: an ordinary array's store, or a typed
array's view store, whose length is fixed. -/
inductive StoreForm where
  | array
  | view (length : Nat)
  deriving DecidableEq, Repr

/-- A location's role, fixed when the world is extended at its allocation. -/
inductive Role where
  | field | cell | elem
  | store (form : StoreForm)
  | identity
  deriving DecidableEq, Repr

def Role.kind : Role → Kind
  | .field => .field
  | .cell => .cell
  | .elem => .elem
  | .store _ => .store
  | .identity => .identity

/-! ## Kinded worlds -/

/-- A kinded world at level `k`: each location's role and its contract, which
may inspect kinded worlds at any strictly lower level. -/
def WorldT : Nat → Type
  | k => List (Role × ((j : Nat) → j < k → WorldT j → Val → Prop))
termination_by k => k
decreasing_by omega

theorem WorldT_eq (k : Nat) :
    WorldT k = List (Role × ((j : Nat) → j < k → WorldT j → Val → Prop)) := by
  rw [WorldT.eq_def]

/-- A contract at level `k`. -/
abbrev Ctr (k : Nat) := (j : Nat) → j < k → WorldT j → Val → Prop

/-- A stable contract admits the same single value at every level and world. -/
def CtrStable {k : Nat} (c : Ctr k) (v : Val) : Prop :=
  ∀ j hj U u, c j hj U u → u = v

theorem CtrStable.restrict {k j : Nat} {c : Ctr k} {v : Val}
    (hc : CtrStable c v) (h : j ≤ k) :
    CtrStable (fun i hi U u => c i (Nat.lt_of_lt_of_le hi h) U u) v :=
  fun i hi U u hu => hc i (Nat.lt_of_lt_of_le hi h) U u hu

/-- A world's entries, in location order. -/
def entries {k : Nat} (W : WorldT k) : List (Role × Ctr k) := cast (WorldT_eq k) W

def ofEntries {k : Nat} (es : List (Role × Ctr k)) : WorldT k := cast (WorldT_eq k).symm es

@[simp] theorem entries_ofEntries {k} (es : List (Role × Ctr k)) : entries (ofEntries es) = es := by
  simp [entries, ofEntries]

@[simp] theorem ofEntries_entries {k} (W : WorldT k) : ofEntries (entries W) = W := by
  simp [entries, ofEntries]

/-- The contracts of a world, in location order. -/
def toList {k : Nat} (W : WorldT k) : List (Ctr k) := (entries W).map Prod.snd

/-- The roles of a world, in location order. -/
def roles {k : Nat} (W : WorldT k) : List Role := (entries W).map Prod.fst

@[simp] theorem toList_length {k} (W : WorldT k) : (toList W).length = (entries W).length := by
  simp [toList]

@[simp] theorem roles_length {k} (W : WorldT k) : (roles W).length = (entries W).length := by
  simp [roles]

def lookup {k : Nat} (W : WorldT k) (l : Nat) : Option (Ctr k) := (toList W)[l]?

def roleAt {k : Nat} (W : WorldT k) (l : Nat) : Option Role := (roles W)[l]?

def kindAt {k : Nat} (W : WorldT k) (l : Nat) : Option Kind := (roleAt W l).map Role.kind

/-- Restricting an entry's contract to level `j ≤ k`; its role is kept. -/
def restrictE {k : Nat} (j : Nat) (h : j ≤ k) (e : Role × Ctr k) : Role × Ctr j :=
  (e.1, fun i hi w => e.2 i (Nat.lt_of_lt_of_le hi h) w)

/-- Truncation keeps every role and weakens every contract's bound. -/
def trunc {k : Nat} (j : Nat) (h : j ≤ k) (W : WorldT k) : WorldT j :=
  ofEntries ((entries W).map (restrictE j h))

/-- Extension keeps every existing entry, role and contract. -/
def WExt {k : Nat} (W W' : WorldT k) : Prop :=
  ∃ tail, entries W' = entries W ++ tail

theorem WExt_refl {k} (W : WorldT k) : WExt W W := ⟨[], by simp⟩

theorem WExt_trans {k} {W V U : WorldT k} (h : WExt W V) (h' : WExt V U) : WExt W U := by
  obtain ⟨a, ha⟩ := h; obtain ⟨b, hb⟩ := h'
  exact ⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩

@[simp] theorem entries_trunc {k j} (h : j ≤ k) (W : WorldT k) :
    entries (trunc j h W) = (entries W).map (restrictE j h) := by
  simp [trunc]

@[simp] theorem roles_trunc {k j} (h : j ≤ k) (W : WorldT k) : roles (trunc j h W) = roles W := by
  simp [roles, Function.comp_def, restrictE]

@[simp] theorem toList_trunc_length {k j} (h : j ≤ k) (W : WorldT k) :
    (toList (trunc j h W)).length = (toList W).length := by
  simp

theorem lookup_trunc {k j : Nat} (h : j ≤ k) (W : WorldT k) (l : Nat) (c : Ctr k)
    (hl : lookup W l = some c) :
    lookup (trunc j h W) l = some (fun i hi w => c i (Nat.lt_of_lt_of_le hi h) w) := by
  simp only [lookup, toList, entries_trunc, List.map_map, List.getElem?_map] at hl ⊢
  rcases hd : (entries W)[l]? with _ | e
  · rw [hd] at hl; simp at hl
  · rw [hd] at hl; simp only [Option.map_some, Option.some.injEq] at hl
    subst hl; rfl

theorem lookup_trunc_inv {k j : Nat} (h : j ≤ k) (W : WorldT k) (l : Nat) (c' : Ctr j)
    (hl : lookup (trunc j h W) l = some c') :
    ∃ c, lookup W l = some c ∧ c' = fun i hi w => c i (Nat.lt_of_lt_of_le hi h) w := by
  simp only [lookup, toList, entries_trunc, List.map_map, List.getElem?_map] at hl ⊢
  rcases hd : (entries W)[l]? with _ | e
  · rw [hd] at hl; simp at hl
  · rw [hd] at hl; simp only [Option.map_some, Option.some.injEq] at hl
    exact ⟨e.2, rfl, hl.symm⟩

/-- **Truncation keeps roles.** -/
@[simp] theorem roleAt_trunc {k j} (h : j ≤ k) (W : WorldT k) (l : Nat) :
    roleAt (trunc j h W) l = roleAt W l := by
  simp [roleAt]

/-- **Truncation keeps kinds**, at every level, zero included. -/
@[simp] theorem kindAt_trunc {k j} (h : j ≤ k) (W : WorldT k) (l : Nat) :
    kindAt (trunc j h W) l = kindAt W l := by
  simp [kindAt]

theorem WExt_lookup {k : Nat} {W W' : WorldT k} (hx : WExt W W') {l : Nat} {c : Ctr k}
    (hl : lookup W l = some c) : lookup W' l = some c := by
  obtain ⟨tail, ht⟩ := hx
  simp only [lookup, toList] at hl ⊢
  rw [ht, List.map_append]
  have := (List.getElem?_eq_some_iff.mp hl).1
  rw [List.getElem?_append_left this]; exact hl

/-- **Extension keeps roles.** -/
theorem WExt_roleAt {k : Nat} {W W' : WorldT k} (hx : WExt W W') {l : Nat} {r : Role}
    (hl : roleAt W l = some r) : roleAt W' l = some r := by
  obtain ⟨tail, ht⟩ := hx
  simp only [roleAt, roles] at hl ⊢
  rw [ht, List.map_append]
  have := (List.getElem?_eq_some_iff.mp hl).1
  rw [List.getElem?_append_left this]; exact hl

/-- **Extension keeps kinds** of every location of the smaller world. -/
theorem WExt_kindAt {k : Nat} {W W' : WorldT k} (hx : WExt W W') {l : Nat}
    (hl : l < (entries W).length) : kindAt W' l = kindAt W l := by
  have : roleAt W l = some ((roles W)[l]'(by simpa using hl)) := List.getElem?_eq_getElem _
  simp only [kindAt, this, WExt_roleAt hx this]

theorem WExt_length {k : Nat} {W W' : WorldT k} (hx : WExt W W') :
    (entries W).length ≤ (entries W').length := by
  obtain ⟨tail, ht⟩ := hx; rw [ht]; simp

theorem trunc_id {k : Nat} (h : k ≤ k) (W : WorldT k) : trunc k h W = W := by
  simp only [trunc]
  have : restrictE k h = id := by funext e; rfl
  rw [this, List.map_id, ofEntries_entries]

theorem trunc_trunc {k j i : Nat} (h1 : i ≤ j) (h2 : j ≤ k) (W : WorldT k) :
    trunc i h1 (trunc j h2 W) = trunc i (Nat.le_trans h1 h2) W := by
  simp only [trunc, entries_ofEntries, List.map_map]
  rfl

theorem WExt_trunc {k j : Nat} (h : j ≤ k) {W W' : WorldT k} (hx : WExt W W') :
    WExt (trunc j h W) (trunc j h W') := by
  obtain ⟨tail, ht⟩ := hx
  exact ⟨tail.map (restrictE j h), by simp [ht]⟩

/-! ## Allocation appends entries -/

def appendW {k : Nat} (W : WorldT k) (r : Role) (c : Ctr k) : WorldT k :=
  ofEntries (entries W ++ [(r, c)])

def appendWs {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) : WorldT k :=
  ofEntries (entries W ++ es)

theorem WExt_appendW {k : Nat} (W : WorldT k) (r : Role) (c : Ctr k) : WExt W (appendW W r c) :=
  ⟨[(r, c)], by simp [appendW]⟩

theorem WExt_appendWs {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) : WExt W (appendWs W es) :=
  ⟨es, by simp [appendWs]⟩

@[simp] theorem entries_appendWs {k} (W : WorldT k) (es : List (Role × Ctr k)) :
    entries (appendWs W es) = entries W ++ es := by simp [appendWs]

@[simp] theorem entries_appendW {k} (W : WorldT k) (r : Role) (c : Ctr k) :
    entries (appendW W r c) = entries W ++ [(r, c)] := by simp [appendW]

@[simp] theorem appendWs_nil {k : Nat} (W : WorldT k) : appendWs W [] = W := by
  simp [appendWs]

theorem appendWs_cons {k : Nat} (W : WorldT k) (e : Role × Ctr k) (es : List (Role × Ctr k)) :
    appendWs W (e :: es) = appendWs (appendW W e.1 e.2) es := by
  simp [appendWs, appendW]

/-- The role of the `i`-th appended location. -/
theorem roleAt_appendWs {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {i : Nat}
    (hi : i < es.length) :
    roleAt (appendWs W es) ((entries W).length + i) = some (es[i]'hi).1 := by
  simp only [roleAt, roles, entries_appendWs, List.map_append]
  rw [List.getElem?_append_right (by simp)]
  simp [hi]

/-- The role of an appended location past the old ones. -/
theorem roleAt_appendWs_ge {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {l : Nat}
    (hl : (entries W).length ≤ l) :
    roleAt (appendWs W es) l = (es.map Prod.fst)[l - (entries W).length]? := by
  simp only [roleAt, roles, entries_appendWs, List.map_append]
  rw [List.getElem?_append_right (by simpa using hl)]
  simp

/-! ## Which contracts are admissible -/

/-- A contract survives the world growing and admits only machine values. -/
def CtrAdm {k : Nat} (c : Ctr k) : Prop :=
  (∀ (j : Nat) (hj : j < k) (W W' : WorldT j), WExt W W' → ∀ v, c j hj W v → c j hj W' v) ∧
    ∀ (j : Nat) (hj : j < k) (W : WorldT j) v, c j hj W v → isVal v = true

def WorldAdm {k : Nat} (W : WorldT k) : Prop := ∀ l c, lookup W l = some c → CtrAdm c

theorem WorldAdm_trunc {k j : Nat} (h : j ≤ k) {W : WorldT k} (hA : WorldAdm W) :
    WorldAdm (trunc j h W) := by
  intro l c' hl
  obtain ⟨c, hc, rfl⟩ := lookup_trunc_inv h W l c' hl
  exact ⟨fun i hi U U' hx v hv => (hA l c hc).1 i (Nat.lt_of_lt_of_le hi h) U U' hx v hv,
    fun i hi U v hv => (hA l c hc).2 i (Nat.lt_of_lt_of_le hi h) U v hv⟩

theorem WorldAdm_appendWs {k : Nat} {W : WorldT k} {es : List (Role × Ctr k)}
    (hW : WorldAdm W) (hc : ∀ e ∈ es, CtrAdm e.2) : WorldAdm (appendWs W es) := by
  intro l d hl
  simp only [lookup, toList, entries_appendWs, List.map_append] at hl
  by_cases hlt : l < (entries W).length
  · rw [List.getElem?_append_left (by simpa using hlt)] at hl
    exact hW l d hl
  · rw [List.getElem?_append_right (by simp; omega)] at hl
    obtain ⟨e, he, rfl⟩ : ∃ e ∈ es, e.2 = d := by
      have := List.mem_of_getElem? hl
      simpa using this
    exact hc e he

/-! ## References and their validity -/

/-- A location reference a term holds: an object's identity, an object's slot
under a key, a store's element cell, or an object's field map, whose
typed-array length field the view store's length fixes. -/
inductive Ref where
  | ident (l : Nat)
  | slot (key : PropKey) (l : Nat)
  | elem (l : Nat)
  | fields (fs : List (PropKey × Nat))

/-- The references of an object's identity and fields. -/
def objRefs (fs : List (PropKey × Nat)) (i : Nat) : List Ref :=
  .ident i :: .fields fs :: fs.map (fun p => .slot p.1 p.2)

/-- The element cells a store lists. -/
def storeRefs (ls : List (Option Nat)) : List Ref :=
  ls.filterMap (fun o => o.map Ref.elem)

mutual
/-- Every location reference a term holds: objects' identities and slots, the
cells of stores, and those of the call descriptors' targets, receivers,
prefixes, captures and node expressions. -/
def refs : Tm → List Ref
  | .var _ => []
  | .invoke f r args => refs f ++ refs r ++ refsArgs args
  | .construct f args => refs f ++ refsArgs args
  | .letE a b => refs a ++ refs b
  | .nul => []
  | .undef => []
  | .tru => []
  | .fls => []
  | .num _ => []
  | .str _ => []
  | .bigint _ => []
  | .sym _ => []
  | .objAt fs .absent i => objRefs fs i
  | .objAt fs (.bound t r pre) i => objRefs fs i ++ (refs t ++ refs r ++ refsArgs pre)
  | .objAt fs (.graph _ E _ _ caps _ _) i => objRefs fs i ++ (refsArgs E ++ refsArgs caps)
  | .makeAt .absent _ xs => refsArgs xs
  | .makeAt (.bound t r pre) _ xs => (refs t ++ refs r ++ refsArgs pre) ++ refsArgs xs
  | .makeAt (.graph _ E _ _ caps _ _) _ xs => (refsArgs E ++ refsArgs caps) ++ refsArgs xs
  | .readAt _ a => refs a
  | .indexAt a key => refs a ++ refs key
  | .writeAt _ a b => refs a ++ refs b
  | .test _ a => refs a
  | .ite c a b => refs c ++ refs a ++ refs b
  | .arith _ a b => refs a ++ refs b
  | .arr ls => storeRefs ls
  | .arrLit xs => refsArgs xs
  | .elemAt a i => refs a ++ refs i
  | .setElem a i v => refs a ++ refs i ++ refs v
  | .lenOf a => refs a
  | .spread a => refs a
  | .throw a => refs a
  | .merge _ a b => refs a ++ refs b
  | .makeKey k a => refs k ++ refs a
  | .goto E _ _ L d => refsArgs E ++ refsArgs L ++ refs d
  | .frame E _ t L d _ _ => refsArgs E ++ refs t ++ refsArgs L ++ refs d
termination_by structural t => t

def refsArgs : List Tm → List Ref
  | [] => []
  | x :: xs => refs x ++ refsArgs xs
termination_by structural xs => xs
end

@[simp] theorem refsArgs_eq (xs : List Tm) : refsArgs xs = xs.flatMap refs := by
  induction xs <;> simp_all [refsArgs]

/-- The role a slot under `key` must have: an array store under `[]`, a view
store of some length under `[[viewElements]]`, and a field or a cell under
every other key. -/
def SlotRole (key : PropKey) : Option Role → Prop
  | some (.store .array) => key = arrayStoreKey
  | some (.store (.view _)) => key = viewElementsKey
  | some .field => key ≠ arrayStoreKey ∧ key ≠ viewElementsKey
  | some .cell => key ≠ arrayStoreKey ∧ key ≠ viewElementsKey
  | _ => False

/-- A typed array's length field: each `[[viewElements]]` slot of an object
is a view store of some length `N`, and the object's `[[viewLength]]` field
is a field location whose contract admits the single value `N`. -/
def ViewLengthOk {k : Nat} (W : WorldT k) (fs : List (PropKey × Nat)) : Prop :=
  ∀ e, (viewElementsKey, e) ∈ fs → ∃ N m c, roleAt W e = some (.store (.view N)) ∧
    fs.lookup viewLengthKey = some m ∧ roleAt W m = some .field ∧
      lookup W m = some c ∧ CtrStable c (.num (bitsOfNat N))

def RefOk {k : Nat} (W : WorldT k) : Ref → Prop
  | .ident l => roleAt W l = some .identity
  | .slot key l => SlotRole key (roleAt W l)
  | .elem l => roleAt W l = some .elem
  | .fields fs => ViewLengthOk W fs

/-- **Reference validity**: every location a term refers to has the role its
position demands. It reads the world only, never the heap. -/
def RefsOk {k : Nat} (W : WorldT k) (t : Tm) : Prop := ∀ r ∈ refs t, RefOk W r

/-- What each role's contents are, by category: a source value in F, C and E,
a store (of the view's length) in S, `null` in I. -/
def Cat : Role → Val → Prop
  | .field, v | .cell, v | .elem, v => isSourceVal v = true
  | .store .array, v => ∃ ls, v = .arr ls
  | .store (.view N), v => ∃ ls, v = .arr ls ∧ ls.length = N
  | .identity, v => v = .nul

/-- **The shape a role demands** of the contents of its location. -/
def Shape {k : Nat} (W : WorldT k) (r : Role) (u : Val) : Prop := Cat r u ∧ RefsOk W u

/-- **Structural satisfaction**: each location the world gives a role holds
contents of that role's shape. -/
def Shaped {k : Nat} (W : WorldT k) (h : Heap) : Prop :=
  ∀ l r, roleAt W l = some r → ∃ u, h[l]? = some u ∧ Shape W r u

/-- The contract part, as `Semantics/Heaps.lean` states it. -/
def HeapMeets (n : Nat) (W : WorldT n) (h : Heap) : Prop :=
  h.length = (toList W).length ∧
    ∀ l c, lookup W l = some c →
      ∃ v, h[l]? = some v ∧ ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v

/-- **Kinded heap satisfaction**: both parts of each entry. The structural
part is unindexed, so it holds at every budget, zero included. -/
def HeapOk (n : Nat) (W : WorldT n) (h : Heap) : Prop := HeapMeets n W h ∧ Shaped W h

/-! ## Validity is world-monotone and survives truncation -/

theorem SlotRole_mono {k} {W W' : WorldT k} (hx : WExt W W') {key : PropKey} {l : Nat}
    (h : SlotRole key (roleAt W l)) : SlotRole key (roleAt W' l) := by
  rcases hr : roleAt W l with _ | r
  · rw [hr] at h; cases h
  · rw [WExt_roleAt hx hr]; rw [hr] at h; exact h

theorem RefOk_mono {k} {W W' : WorldT k} (hx : WExt W W') : ∀ {r : Ref}, RefOk W r → RefOk W' r
  | .ident _, h => WExt_roleAt hx h
  | .slot _ _, h => SlotRole_mono hx h
  | .elem _, h => WExt_roleAt hx h
  | .fields _, h => fun e he => by
    obtain ⟨N, m, c, hr, hm, hmr, hml, hs⟩ := h e he
    exact ⟨N, m, c, WExt_roleAt hx hr, hm, WExt_roleAt hx hmr, WExt_lookup hx hml, hs⟩

theorem RefsOk_mono {k} {W W' : WorldT k} (hx : WExt W W') {t : Tm} (h : RefsOk W t) :
    RefsOk W' t := fun r hr => RefOk_mono hx (h r hr)

/-- **`Shape` is monotone in world extension**: extension keeps every role a
shape refers to. -/
theorem Shape_mono {k} {W W' : WorldT k} (hx : WExt W W') {r : Role} {u : Val}
    (h : Shape W r u) : Shape W' r u := ⟨h.1, RefsOk_mono hx h.2⟩

theorem RefOk_trunc {k j} (hj : j ≤ k) {W : WorldT k} : ∀ {r : Ref}, RefOk W r → RefOk (trunc j hj W) r
  | .ident _, h => by simpa [RefOk] using h
  | .slot _ _, h => by simpa [RefOk] using h
  | .elem _, h => by simpa [RefOk] using h
  | .fields _, h => fun e he => by
    obtain ⟨N, m, c, hr, hm, hmr, hml, hs⟩ := h e he
    exact ⟨N, m, _, by simpa using hr, hm, by simpa using hmr, lookup_trunc hj W m c hml,
      hs.restrict hj⟩

theorem RefsOk_trunc {k j} (hj : j ≤ k) {W : WorldT k} {t : Tm} (h : RefsOk W t) :
    RefsOk (trunc j hj W) t := fun r hr => RefOk_trunc hj (h r hr)

theorem Shape_trunc {k j} (hj : j ≤ k) {W : WorldT k} {r : Role} {u : Val} (h : Shape W r u) :
    Shape (trunc j hj W) r u := ⟨h.1, RefsOk_trunc hj h.2⟩

theorem Shaped_trunc {k j} (hj : j ≤ k) {W : WorldT k} {h : Heap} (hs : Shaped W h) :
    Shaped (trunc j hj W) h := fun l r hr => by
  obtain ⟨u, hu, hsh⟩ := hs l r (by simpa using hr)
  exact ⟨u, hu, Shape_trunc hj hsh⟩

theorem HeapMeets_trunc (n : Nat) (W : WorldT (n + 1)) (h : Heap)
    (hok : HeapMeets (n + 1) W h) : HeapMeets n (trunc n (Nat.le_succ n) W) h := by
  obtain ⟨hlen, hall⟩ := hok
  refine ⟨by simpa using hlen, ?_⟩
  intro l c hl
  obtain ⟨d, hd, rfl⟩ := lookup_trunc_inv (Nat.le_succ n) W l c hl
  obtain ⟨v, hv, hmem⟩ := hall l d hd
  refine ⟨v, hv, fun j hj => ?_⟩
  rw [trunc_trunc]
  exact hmem j (by omega)

/-- Heap satisfaction survives dropping a level, with the world truncated. -/
theorem HeapOk_trunc (n : Nat) (W : WorldT (n + 1)) (h : Heap)
    (hok : HeapOk (n + 1) W h) : HeapOk n (trunc n (Nat.le_succ n) W) h :=
  ⟨HeapMeets_trunc n W h hok.1, Shaped_trunc _ hok.2⟩

/-- At positive level, a stable location holds its single value. -/
theorem HeapOk.stable_value {n : Nat} {W : WorldT n} {h : Heap}
    {l : Nat} {c : Ctr n} {v : Val} (hh : HeapOk n W h)
    (hn : 0 < n) (hl : lookup W l = some c) (hc : CtrStable c v) :
    h[l]? = some v := by
  obtain ⟨u, hu, hm⟩ := hh.1.2 l c hl
  have he := hc 0 hn (trunc 0 (Nat.zero_le n) W) u (hm 0 hn)
  simpa [he] using hu

/-! ## Kinds are disjoint and partition the domain -/

/-- The locations of kind `k`: `K_W(k)`. -/
def K {n : Nat} (W : WorldT n) (k : Kind) (l : Nat) : Prop := kindAt W l = some k

/-- **Kinds are disjoint.** -/
theorem kinds_disjoint {n : Nat} (W : WorldT n) {k k' : Kind} (hne : k ≠ k') (l : Nat) :
    ¬ (K W k l ∧ K W k' l) := by
  rintro ⟨h1, h2⟩
  simp only [K] at h1 h2
  rw [h1] at h2; cases h2; exact hne rfl

theorem roleAt_lt {n} {W : WorldT n} {l : Nat} {r : Role} (h : roleAt W l = some r) :
    l < (entries W).length := by
  have := (List.getElem?_eq_some_iff.mp h).1; simpa using this

theorem roleAt_some {n} {W : WorldT n} {l : Nat} (h : l < (entries W).length) :
    ∃ r, roleAt W l = some r :=
  ⟨_, List.getElem?_eq_getElem (by simpa using h)⟩

theorem Cat_store_iff {r : Role} {ls : List (Option Nat)} (h : Cat r (.arr ls)) : r.kind = .store := by
  cases r with
  | field | cell | elem => simp [Cat, isSourceVal] at h
  | identity => simp [Cat] at h
  | store f => rfl

theorem RefsOk_arr {n} {W : WorldT n} {ls : List (Option Nat)} (h : RefsOk W (.arr ls)) :
    ∀ l, some l ∈ ls → K W .elem l := by
  intro l hl
  have := h (.elem l) (by
    simp only [refs, storeRefs]; exact List.mem_filterMap.mpr ⟨some l, hl, rfl⟩)
  simp [RefOk] at this; simp [K, kindAt, this, Role.kind]

/-- **Kinds partition a well-formed heap's domain**: each location has
exactly one kind; a location is a store location exactly when it holds a
store; and every store lists element cells only, which are locations of the
heap. -/
theorem HeapOk.kinds {n : Nat} {W : WorldT n} {h : Heap} (hok : HeapOk n W h) :
    (∀ l, l < h.length → ∃ k, K W k l ∧ ∀ k', K W k' l → k' = k) ∧
    (∀ l, K W .store l ↔ ∃ ls, h[l]? = some (Tm.arr ls)) ∧
    (∀ (s : Nat) (ls : List (Option Nat)), h[s]? = some (Tm.arr ls) →
      ∀ l, some l ∈ ls → K W .elem l ∧ l < h.length) := by
  have hlen : h.length = (entries W).length := by simpa using hok.1.1
  have store_of : ∀ (s : Nat) (ls : List (Option Nat)), h[s]? = some (Tm.arr ls) → ∃ r, roleAt W s = some r ∧ Shape W r (.arr ls) := by
    intro s ls hs
    have hlt : s < (entries W).length := by
      have := (List.getElem?_eq_some_iff.mp hs).1; omega
    obtain ⟨r, hr⟩ := roleAt_some hlt
    obtain ⟨u, hu, hsh⟩ := hok.2 s r hr
    rw [hs] at hu; cases hu
    exact ⟨r, hr, hsh⟩
  refine ⟨fun l hl => ?_, fun l => ⟨fun hk => ?_, fun ⟨ls, hs⟩ => ?_⟩, fun s ls hs l hl => ?_⟩
  · obtain ⟨r, hr⟩ := roleAt_some (show l < (entries W).length by omega)
    refine ⟨r.kind, by simp [K, kindAt, hr], fun k' hk' => ?_⟩
    simp [K, kindAt, hr] at hk'; exact hk'.symm
  · simp only [K, kindAt, Option.map_eq_some_iff] at hk
    obtain ⟨r, hr, hk⟩ := hk
    obtain ⟨u, hu, hc, -⟩ := hok.2 l r hr
    cases r with
    | store f =>
      cases f with
      | array => obtain ⟨ls, rfl⟩ := hc; exact ⟨ls, hu⟩
      | view N => obtain ⟨ls, rfl, -⟩ := hc; exact ⟨ls, hu⟩
    | _ => simp [Role.kind] at hk
  · obtain ⟨r, hr, hsh⟩ := store_of l ls hs
    simp [K, kindAt, hr, Cat_store_iff hsh.1]
  · obtain ⟨r, hr, hsh⟩ := store_of s ls hs
    have he := RefsOk_arr hsh.2 l hl
    refine ⟨he, ?_⟩
    simp only [K, kindAt, Option.map_eq_some_iff] at he
    obtain ⟨r', hr', -⟩ := he
    have := roleAt_lt hr'; omega

/-! ## What kinded satisfaction excludes -/

/-- **The audit's counter-heap is excluded.** In `[[1], 0, null]` the array
`z` holds its store at 0 and the object `o` its field `f` at 1, which `z`'s
store lists: location 1 would be both a field (or cell) location and an
element cell. No world, at any level, satisfies the heap with both values
valid. -/
theorem counterheap_excluded {n : Nat} (W : WorldT n) :
    ¬ (HeapOk n W [.arr [some 1], .num 0, .nul] ∧
      RefsOk W (.objAt [(arrayStoreKey, 0)] .absent 2) ∧
      RefsOk W (.objAt [(.str "f", 1)] .absent 2)) := by
  rintro ⟨hok, hz, ho⟩
  have h0 := (HeapOk.kinds hok).2.2 0 [some 1] rfl 1 (by simp)
  have h1 := ho (.slot (.str "f") 1) (by simp [refs, objRefs])
  simp only [RefOk] at h1
  simp only [K, kindAt, Option.map_eq_some_iff] at h0
  obtain ⟨r, hr, hk⟩ := h0.1
  rw [hr] at h1
  cases r <;> simp_all [SlotRole, Role.kind]

/-- **The dangling-store transition of `rootCells_not_invariant` is
excluded**: no kinded world, at any level, is satisfied by a heap of three
locations whose store at 0 lists location 5. -/
theorem dangling_excluded {n : Nat} (W : WorldT n) :
    ¬ HeapOk n W [.arr [some 5], .nul, .nul] := by
  intro hok
  have := (HeapOk.kinds hok).2.2 0 [some 5] rfl 5 (by simp)
  simp at this

end Verification.Kinds
