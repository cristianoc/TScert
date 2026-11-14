import Verification.Semantics.Calculus
/-!
# Stratified kinded worlds

A **world** says what each location is *for*: each location has a **role**,
fixed for its life, and a **contract**. The model of the note *Tolerant
frames* (§§2–3) partitions a heap's locations by kind (field locations F,
cells C, element cells E, store locations S, identity locations I): the role
refines the kind, and a location receives it when the typing rule that
justifies its allocation extends the world (docs/drafts/location-kinds.md).

A contract must be able to judge values against worlds, so worlds and
contracts are mutually dependent. The circularity is broken by stratifying on
a level:

    World k = Loc → Role × (contracts that inspect worlds at any level < k)

which is one well-founded recursion. `WorldT k` does not reduce
definitionally, so `entries`/`ofEntries` mediate; both round-trips are
immediate.

A contract is **uniform in the level** -- it accepts any `j < k` -- rather
than pinned to one level. Truncating a world to a lower level is then only a
weakening of the bound each contract accepts, and it keeps every role, so the
coherence laws are equalities. Extension appends entries and keeps every old
role and contract.

Not every contract is a type. `CtrAdm` requires a contract to survive the
world growing, and `WorldAdm` lifts that to a world.

The second half states **reference validity** (`RefsOk`): every location a
term refers to has the role its position demands, and the **shape** each role
demands of its contents (`Shape`); `Semantics/Heaps.lean` relates a heap to a
world by both.
-/
namespace Verification
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
under a key, a store's element cell, or an object's field map, whose view
metadata is valid as a whole (`ViewMetaOk`). -/
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

/-- **A view-length metadata location** of the fixed length `N`: a field
location whose contract admits the single value `N`. -/
def LengthMeta {k : Nat} (W : WorldT k) (m N : Nat) : Prop :=
  ∃ c, roleAt W m = some .field ∧ lookup W m = some c ∧ CtrStable c (.num (bitsOfNat N))

/-- **View metadata validity** of an object's field map. Every location the
map gives `[[viewLength]]` is a view-length metadata location of some fixed
length, whether or not the map names `[[viewElements]]` (a host object may
hold its length alone). Every location the map gives `[[viewElements]]` is a
view store of some length `N`, and the location the map's `[[viewLength]]`
finds is a view-length metadata location of that same `N`; and a map
naming `[[viewElements]]` or `[[viewLength]]` names `[[host]]`: the metadata
is a host object's (a typed array is one). -/
def ViewMetaOk {k : Nat} (W : WorldT k) (fs : List (PropKey × Nat)) : Prop :=
  (∀ m, (viewLengthKey, m) ∈ fs → ∃ N, LengthMeta W m N) ∧
    (∀ e, (viewElementsKey, e) ∈ fs → ∃ N m, roleAt W e = some (.store (.view N)) ∧
      fs.lookup viewLengthKey = some m ∧ LengthMeta W m N) ∧
    ∀ e, ((viewElementsKey, e) ∈ fs ∨ (viewLengthKey, e) ∈ fs) → (fs.lookup hostKey).isSome

def RefOk {k : Nat} (W : WorldT k) : Ref → Prop
  | .ident l => roleAt W l = some .identity
  | .slot key l => SlotRole key (roleAt W l)
  | .elem l => roleAt W l = some .elem
  | .fields fs => ViewMetaOk W fs

/-- **Reference validity**: every location a term refers to has the role its
position demands. It reads the world only, never the heap. -/
def RefsOk {k : Nat} (W : WorldT k) (t : Tm) : Prop := ∀ r ∈ refs t, RefOk W r

/-- **An environment's roots are valid**: every reference of every value it
holds has the role its position demands. A graph state's environment is
(`ControlFlow.StateRefs`). -/
def RootsOk {k : Nat} (W : WorldT k) (ρ : Env) : Prop := ∀ x, RefsOk W (ρ x)

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


/-! ## Validity is world-monotone and survives truncation -/

theorem SlotRole_mono {k} {W W' : WorldT k} (hx : WExt W W') {key : PropKey} {l : Nat}
    (h : SlotRole key (roleAt W l)) : SlotRole key (roleAt W' l) := by
  rcases hr : roleAt W l with _ | r
  · rw [hr] at h; cases h
  · rw [WExt_roleAt hx hr]; rw [hr] at h; exact h

theorem LengthMeta.mono {k} {W W' : WorldT k} (hx : WExt W W') {m N : Nat}
    (h : LengthMeta W m N) : LengthMeta W' m N :=
  let ⟨c, hr, hl, hs⟩ := h; ⟨c, WExt_roleAt hx hr, WExt_lookup hx hl, hs⟩

theorem LengthMeta.trunc {k j} (hj : j ≤ k) {W : WorldT k} {m N : Nat}
    (h : LengthMeta W m N) : LengthMeta (trunc j hj W) m N :=
  let ⟨c, hr, hl, hs⟩ := h; ⟨_, by simpa using hr, lookup_trunc hj W m c hl, hs.restrict hj⟩

theorem RefOk_mono {k} {W W' : WorldT k} (hx : WExt W W') : ∀ {r : Ref}, RefOk W r → RefOk W' r
  | .ident _, h => WExt_roleAt hx h
  | .slot _ _, h => SlotRole_mono hx h
  | .elem _, h => WExt_roleAt hx h
  | .fields _, h =>
    ⟨fun m hm => let ⟨N, hN⟩ := h.1 m hm; ⟨N, hN.mono hx⟩,
      fun e he => let ⟨N, m, hr, hm, hN⟩ := h.2.1 e he; ⟨N, m, WExt_roleAt hx hr, hm, hN.mono hx⟩, h.2.2⟩

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
  | .fields _, h =>
    ⟨fun m hm => let ⟨N, hN⟩ := h.1 m hm; ⟨N, hN.trunc hj⟩,
      fun e he => let ⟨N, m, hr, hm, hN⟩ := h.2.1 e he; ⟨N, m, by simpa using hr, hm, hN.trunc hj⟩, h.2.2⟩

theorem RefsOk_trunc {k j} (hj : j ≤ k) {W : WorldT k} {t : Tm} (h : RefsOk W t) :
    RefsOk (trunc j hj W) t := fun r hr => RefOk_trunc hj (h r hr)

theorem Shape_trunc {k j} (hj : j ≤ k) {W : WorldT k} {r : Role} {u : Val} (h : Shape W r u) :
    Shape (trunc j hj W) r u := ⟨h.1, RefsOk_trunc hj h.2⟩

theorem Shaped_trunc {k j} (hj : j ≤ k) {W : WorldT k} {h : Heap} (hs : Shaped W h) :
    Shaped (trunc j hj W) h := fun l r hr => by
  obtain ⟨u, hu, hsh⟩ := hs l r (by simpa using hr)
  exact ⟨u, hu, Shape_trunc hj hsh⟩


/-- **A context's references** are those of its hole's contents and those of
the context around the hole. -/
def CtxRefs (C : Tm → Tm) : Prop := ∀ t r, r ∈ refs (C t) ↔ r ∈ refs t ∨ r ∈ refs (C .undef)

theorem CtxRefs.ok {C : Tm → Tm} (hc : CtxRefs C) {k : Nat} {W : WorldT k} {t : Tm}
    (ht : RefsOk W t) (hC : RefsOk W (C .undef)) : RefsOk W (C t) :=
  fun r hr => ((hc t r).mp hr).elim (ht r) (hC r)

/-- The context's own references are among those of every filling. -/
theorem CtxRefs.frame {C : Tm → Tm} (hc : CtxRefs C) {k : Nat} {W : WorldT k} {t : Tm}
    (h : RefsOk W (C t)) : RefsOk W (C .undef) :=
  fun r hr => h r ((hc t r).mpr (.inr hr))

/-- The hole's references are among those of the filled context. -/
theorem CtxRefs.hole {C : Tm → Tm} (hc : CtxRefs C) {k : Nat} {W : WorldT k} {t : Tm}
    (h : RefsOk W (C t)) : RefsOk W t :=
  fun r hr => h r ((hc t r).mpr (.inl hr))

/-- Closes `CtxRefs C` for a context built from the term constructors: both
sides unfold to memberships in the constructors' reference lists. -/
macro "ctx_refs" : tactic => `(tactic| (intro t r; simp only [refs, refsArgs_eq, List.mem_append,
  List.mem_flatMap, List.mem_cons, List.flatMap_cons, List.flatMap_append, List.not_mem_nil, false_or,
  or_false, exists_eq_or_imp, List.nil_append, List.append_nil]; all_goals grind))

theorem refs_letE (a b : Tm) : refs (.letE a b) = refs a ++ refs b := by simp [refs]

@[simp] theorem RefsOk_nul {k : Nat} {W : WorldT k} : RefsOk W .nul := fun _ h => by simp [refs] at h
@[simp] theorem RefsOk_undef {k : Nat} {W : WorldT k} : RefsOk W .undef := fun _ h => by simp [refs] at h

/-- Validity passes to a term whose references are among a valid one's. -/
theorem RefsOk.sub {k : Nat} {W : WorldT k} {t t' : Tm} (h : RefsOk W t)
    (hsub : ∀ r ∈ refs t', r ∈ refs t) : RefsOk W t' := fun r hr => h r (hsub r hr)

theorem RefsOk_invoke {k : Nat} {W : WorldT k} {f r : Tm} {args : List Tm} :
    RefsOk W (.invoke f r args) ↔ RefsOk W f ∧ RefsOk W r ∧ ∀ a ∈ args, RefsOk W a := by
  simp only [RefsOk, refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
  constructor
  · intro h; exact ⟨fun x hx => h x (.inl (.inl hx)), fun x hx => h x (.inl (.inr hx)),
      fun a ha x hx => h x (.inr ⟨a, ha, hx⟩)⟩
  · rintro ⟨hf, hr, ha⟩ x ((hx | hx) | ⟨a, hm, hx⟩)
    · exact hf x hx
    · exact hr x hx
    · exact ha a hm x hx

theorem RefsOk_construct {k : Nat} {W : WorldT k} {f : Tm} {args : List Tm} :
    RefsOk W (.construct f args) ↔ RefsOk W f ∧ ∀ a ∈ args, RefsOk W a := by
  simp only [RefsOk, refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
  constructor
  · intro h; exact ⟨fun x hx => h x (.inl hx), fun a ha x hx => h x (.inr ⟨a, ha, hx⟩)⟩
  · rintro ⟨hf, ha⟩ x (hx | ⟨a, hm, hx⟩)
    · exact hf x hx
    · exact ha a hm x hx

theorem RefsOk_of_nil {k : Nat} {W : WorldT k} {t : Tm} (h : refs t = []) : RefsOk W t :=
  fun _ hr => by rw [h] at hr; cases hr

theorem binop_refs {op : Arith} {a b v : Tm} (h : binop op a b = some v) : refs v = [] := by
  obtain ⟨-, -, hv⟩ := binop_result h
  rcases hv with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

theorem codeUnitAt_refs (s : String) (b : UInt64) : refs (codeUnitAt s b) = [] := by
  unfold codeUnitAt; split <;> rfl

theorem WorldAdm_append {k : Nat} {W : WorldT k} {r : Role} {c : Ctr k}
    (hW : WorldAdm W) (hc : CtrAdm c) : WorldAdm (appendW W r c) := by
  have : appendW W r c = appendWs W [(r, c)] := rfl
  rw [this]; exact WorldAdm_appendWs hW (by simpa using hc)

theorem lookup_appendWs {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {i : Nat}
    (_hi : i < es.length) :
    lookup (appendWs W es) ((toList W).length + i) = (es.map Prod.snd)[i]? := by
  simp only [lookup, toList, entries_appendWs, List.map_append]
  rw [List.getElem?_append_right (by simp)]
  simp

end Verification
