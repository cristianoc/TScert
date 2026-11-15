import Verification.Semantics.SafeIntegers
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
world growing, and `WorldAdm` lifts that to a world, where besides every view
store has the canonical contract of its format and length (`ViewWorld`).

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

/-- The two forms of a store location (the note *Tolerant frames*, §2,
`array` and `view_N`): an ordinary array's store, or a typed array's view
store, whose format and length are fixed. -/
inductive StoreForm where
  | array
  | view (format : ViewFormat) (length : Nat)
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

/-- The three categories of a location (the note *Tolerant frames*, §3, the
class regions): value locations (field, cell, element and identity
locations), array stores and view stores. They partition the locations: a
role has exactly one, fixed with the role. -/
inductive Category where
  | value
  | array
  | view
  deriving DecidableEq, Repr

/-- A role's category, independent of the location's contents. -/
def Role.category : Role → Category
  | .store .array => .array
  | .store (.view ..) => .view
  | .field | .cell | .elem | .identity => .value

/-- A store location's category is a store's: an array's or a view's. -/
theorem Role.category_store {r : Role} : r.kind = .store ↔ r.category ≠ .value := by
  cases r with
  | store f => cases f <;> simp [Role.kind, Role.category]
  | _ => simp [Role.kind, Role.category]

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

theorem roleAt_appendWs_lt {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {l : Nat}
    (hl : l < (entries W).length) : roleAt (appendWs W es) l = roleAt W l := by
  simp only [roleAt, roles, entries_appendWs, List.map_append]
  rw [List.getElem?_append_left (by simpa using hl)]

theorem lookup_appendWs_lt {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {l : Nat}
    (hl : l < (entries W).length) : lookup (appendWs W es) l = lookup W l := by
  simp only [lookup, toList, entries_appendWs, List.map_append]
  rw [List.getElem?_append_left (by simpa using hl)]

theorem lookup_appendWs_ge {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {i : Nat} :
    lookup (appendWs W es) ((entries W).length + i) = (es.map Prod.snd)[i]? := by
  simp only [lookup, toList, entries_appendWs, List.map_append]
  rw [List.getElem?_append_right (by simp)]
  simp

/-! ## The canonical contract of a view store

A typed array's view store lists one element cell per index (`Cat`,
`StoreForm.view`). Its cells hold numbers of the store's format, and its
contract admits every replacement a write through any typed array may make:
every view store of its format and length whose cells are such cells (the
note *Tolerant frames*, (W2): "the contract of a view store admits every
such store"). A world whose every view-store location has this canonical
contract is a **view world** (`ViewWorld`); an admissible world is one
(`WorldAdm.view`). -/

/-- The integers an integer format stores: `0` to `2^8 - 1`, `0` to
`2^16 - 1`, `-2^31` to `2^31 - 1`; `float64` stores every number. -/
def ViewFormat.range : ViewFormat → Option (Int × Int)
  | .uint8 => some (0, 255)
  | .uint16 => some (0, 65535)
  | .int32 => some (-2147483648, 2147483647)
  | .float64 => none

/-- **The values a format stores**: a number, an integer in the format's
range where it has one. -/
def ViewFormat.Stored (f : ViewFormat) (v : Val) : Prop :=
  ∃ b, v = .num b ∧ ∀ lo hi, f.range = some (lo, hi) → ∃ i, SafeIntegers.SafeInt b i ∧ lo ≤ i ∧ i ≤ hi

theorem ViewFormat.Stored.isVal {f : ViewFormat} {v : Val} (h : f.Stored v) : isVal v = true := by
  obtain ⟨b, rfl, -⟩ := h; rfl

/-- A cell of a view store of format `f` in `U`: an element cell whose
contract admits exactly the values `f` stores, at every level it inspects. -/
def ViewCell {j : Nat} (U : WorldT j) (f : ViewFormat) (c : Nat) : Prop :=
  roleAt U c = some .elem ∧
    ∃ d, lookup U c = some d ∧ ∀ i (hi : i < j) (U' : WorldT i) u, d i hi U' u ↔ f.Stored u

theorem ViewCell.mono {j : Nat} {U U' : WorldT j} (hx : WExt U U') {f : ViewFormat} {c : Nat}
    (h : ViewCell U f c) : ViewCell U' f c := by
  obtain ⟨hr, d, hd, hiff⟩ := h
  exact ⟨WExt_roleAt hx hr, d, WExt_lookup hx hd, hiff⟩

theorem ViewCell.trunc {k j : Nat} (hj : j ≤ k) {W : WorldT k} {f : ViewFormat} {c : Nat}
    (h : ViewCell W f c) : ViewCell (Verification.trunc j hj W) f c := by
  obtain ⟨hr, d, hd, hiff⟩ := h
  exact ⟨by simpa using hr, _, lookup_trunc hj W c d hd, fun i hi U' u => hiff i _ U' u⟩

/-- **The canonical contract of a view store** of format `f` and length `N`:
every view store of that format and length whose cells are cells of the
format. -/
def viewStoreCtr (k : Nat) (f : ViewFormat) (N : Nat) : Ctr k :=
  fun _ _ U v => ∃ cs, v = .viewStore f cs ∧ cs.length = N ∧ ∀ c ∈ cs, ViewCell U f c

/-- A contract is the canonical one of a view store of format `f` and length
`N`, at every level it inspects. -/
def CanonicalView {k : Nat} (c : Ctr k) (f : ViewFormat) (N : Nat) : Prop :=
  ∀ j (hj : j < k) U v, c j hj U v ↔ viewStoreCtr k f N j hj U v

/-- **A view world**: every view-store location has the canonical contract
of its format and length. -/
def ViewWorld {k : Nat} (W : WorldT k) : Prop :=
  ∀ l f N, roleAt W l = some (.store (.view f N)) → ∃ c, lookup W l = some c ∧ CanonicalView c f N

theorem ViewWorld.trunc {k j : Nat} (hj : j ≤ k) {W : WorldT k} (hW : ViewWorld W) :
    ViewWorld (Verification.trunc j hj W) := by
  intro l f N hr
  obtain ⟨c, hc, hiff⟩ := hW l f N (by simpa using hr)
  exact ⟨_, lookup_trunc hj W l c hc, fun i hi U v => hiff i _ U v⟩

/-- **Extension keeps a view world** where each appended view-store entry
has the canonical contract. -/
theorem ViewWorld.appendWs {k : Nat} {W : WorldT k} {es : List (Role × Ctr k)} (hW : ViewWorld W)
    (hes : ∀ e ∈ es, ∀ f N, e.1 = .store (.view f N) → CanonicalView e.2 f N) :
    ViewWorld (Verification.appendWs W es) := by
  intro l f N hr
  by_cases hl : l < (entries W).length
  · rw [roleAt_appendWs_lt W es hl] at hr
    obtain ⟨c, hc, hiff⟩ := hW l f N hr
    exact ⟨c, by rw [lookup_appendWs_lt W es hl]; exact hc, hiff⟩
  · have hge : (entries W).length ≤ l := by omega
    rw [roleAt_appendWs_ge W es hge] at hr
    obtain ⟨i, rfl⟩ : ∃ i, l = (entries W).length + i := ⟨l - (entries W).length, by omega⟩
    simp only [Nat.add_sub_cancel_left, List.getElem?_map, Option.map_eq_some_iff] at hr
    obtain ⟨e, he, hef⟩ := hr
    refine ⟨e.2, ?_, hes e (List.mem_of_getElem? he) f N hef⟩
    rw [lookup_appendWs_ge]; simp [he]

/-- Entries none of which is a view store keep a view world. -/
theorem ViewWorld.appendWs_plain {k : Nat} {W : WorldT k} {es : List (Role × Ctr k)} (hW : ViewWorld W)
    (hes : ∀ e ∈ es, ∀ f N, e.1 ≠ .store (.view f N)) : ViewWorld (Verification.appendWs W es) :=
  hW.appendWs fun e he f N h => absurd h (hes e he f N)

/-! ## Which worlds are admissible -/

/-- **An admissible world**: every contract survives the world growing and
admits only machine values (`CtrAdm`), and every view store has the
canonical contract of its format and length (`ViewWorld`, the note
*Tolerant frames*, (W2)). It reads as its contracts' admissibility where a
function is expected. -/
structure WorldAdm {k : Nat} (W : WorldT k) : Prop where
  ctr : ∀ l c, lookup W l = some c → CtrAdm c
  view : ViewWorld W

instance {k : Nat} {W : WorldT k} : CoeFun (WorldAdm W) (fun _ => ∀ l c, lookup W l = some c → CtrAdm c) :=
  ⟨WorldAdm.ctr⟩

theorem WorldAdm_trunc {k j : Nat} (h : j ≤ k) {W : WorldT k} (hA : WorldAdm W) :
    WorldAdm (trunc j h W) := by
  refine ⟨fun l c' hl => ?_, hA.view.trunc h⟩
  obtain ⟨c, hc, rfl⟩ := lookup_trunc_inv h W l c' hl
  exact ⟨fun i hi U U' hx v hv => (hA l c hc).1 i (Nat.lt_of_lt_of_le hi h) U U' hx v hv,
    fun i hi U v hv => (hA l c hc).2 i (Nat.lt_of_lt_of_le hi h) U v hv⟩

/-- **Extension keeps an admissible world** where each appended contract is
admissible and each appended view store's contract is canonical. -/
theorem WorldAdm_appendWs {k : Nat} {W : WorldT k} {es : List (Role × Ctr k)}
    (hW : WorldAdm W) (hc : ∀ e ∈ es, CtrAdm e.2)
    (hv : ∀ e ∈ es, ∀ f N, e.1 = .store (.view f N) → CanonicalView e.2 f N) : WorldAdm (appendWs W es) := by
  refine ⟨fun l d hl => ?_, hW.view.appendWs hv⟩
  simp only [lookup, toList, entries_appendWs, List.map_append] at hl
  by_cases hlt : l < (entries W).length
  · rw [List.getElem?_append_left (by simpa using hlt)] at hl
    exact hW l d hl
  · rw [List.getElem?_append_right (by simp; omega)] at hl
    obtain ⟨e, he, rfl⟩ : ∃ e ∈ es, e.2 = d := by
      have := List.mem_of_getElem? hl
      simpa using this
    exact hc e he

/-- Extension by entries none of which is a view store keeps an admissible
world where each appended contract is admissible. -/
theorem WorldAdm_appendWs_plain {k : Nat} {W : WorldT k} {es : List (Role × Ctr k)}
    (hW : WorldAdm W) (hc : ∀ e ∈ es, CtrAdm e.2) (hp : ∀ e ∈ es, ∀ f N, e.1 ≠ .store (.view f N)) :
    WorldAdm (appendWs W es) :=
  WorldAdm_appendWs hW hc fun e he f N h => absurd h (hp e he f N)

/-! ## References and their validity -/

/-- A location reference a term holds: an object's identity, an object's slot
under a key, a store's element cell, or a typed array's view store of its
format and length. -/
inductive Ref where
  | ident (l : Nat)
  | slot (key : PropKey) (l : Nat)
  | elem (l : Nat)
  /-- A typed array's view store, and whether the typed array owns no
  array-store slot (`arrayStoreKey`): a typed array has one store, the
  one its descriptor names. -/
  | view (l : Nat) (format : ViewFormat) (length : Nat) (plain : Bool)

/-- The references of an object's identity and fields. -/
def objRefs (fs : List (PropKey × Nat)) (i : Nat) : List Ref :=
  .ident i :: fs.map (fun p => .slot p.1 p.2)

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
  | .objAt fs (.view s f n) i => objRefs fs i ++ [.view s f n (fs.lookup arrayStoreKey).isNone]
  | .objAt fs (.bound t r pre) i => objRefs fs i ++ (refs t ++ refs r ++ refsArgs pre)
  | .objAt fs (.graph _ E _ _ caps _ _) i => objRefs fs i ++ (refsArgs E ++ refsArgs caps)
  | .makeAt .absent _ xs => refsArgs xs
  | .makeAt (.view s f n) ns xs => .view s f n (!ns.contains arrayStoreKey) :: refsArgs xs
  | .makeAt (.bound t r pre) _ xs => (refs t ++ refs r ++ refsArgs pre) ++ refsArgs xs
  | .makeAt (.graph _ E _ _ caps _ _) _ xs => (refsArgs E ++ refsArgs caps) ++ refsArgs xs
  | .readAt _ a => refs a
  | .indexAt a key => refs a ++ refs key
  | .writeAt _ a b => refs a ++ refs b
  | .test _ a => refs a
  | .ite c a b => refs c ++ refs a ++ refs b
  | .arith _ a b => refs a ++ refs b
  | .arr ls => storeRefs ls
  | .viewStore _ cs => cs.map Ref.elem
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

/-- The role a slot under `key` must have: an array store under `[]`, and a
field or a cell under every other key. No slot holds a view store: a typed
array names its view store by its descriptor (`Ref.view`). -/
def SlotRole (key : PropKey) : Option Role → Prop
  | some (.store .array) => key = arrayStoreKey
  | some .field => key ≠ arrayStoreKey
  | some .cell => key ≠ arrayStoreKey
  | _ => False

/-- A reference's validity (the note *Tolerant frames*, (W3)): an identity
is an identity location, a slot a location of its key's role, a listed cell
an element cell, and a typed array's view store a view store of the
typed array's format and length, of a typed array owning no array-store
slot. -/
def RefOk {k : Nat} (W : WorldT k) : Ref → Prop
  | .ident l => roleAt W l = some .identity
  | .slot key l => SlotRole key (roleAt W l)
  | .elem l => roleAt W l = some .elem
  | .view l f n plain => plain = true ∧ roleAt W l = some (.store (.view f n))

/-- **Reference validity**: every location a term refers to has the role its
position demands. It reads the world only, never the heap. -/
def RefsOk {k : Nat} (W : WorldT k) (t : Tm) : Prop := ∀ r ∈ refs t, RefOk W r

/-- **An environment's roots are valid**: every reference of every value it
holds has the role its position demands. A graph state's environment is
(`ControlFlow.StateRefs`). -/
def RootsOk {k : Nat} (W : WorldT k) (ρ : Env) : Prop := ∀ x, RefsOk W (ρ x)

/-- What each role's contents are (the note *Tolerant frames*, (W2)): a
source value in F, C and E; an array's store in an array store; in a view
store of form `view_N`, a view store of its format listing a cell at each of
its `N` indices, so with no hole; `null` in I. -/
def Cat : Role → Val → Prop
  | .field, v | .cell, v | .elem, v => isSourceVal v = true
  | .store .array, v => ∃ ls, v = .arr ls
  | .store (.view f N), v => ∃ cs, v = .viewStore f cs ∧ cs.length = N
  | .identity, v => v = .nul

/-- **The shape a role demands** of the contents of its location. -/
def Shape {k : Nat} (W : WorldT k) (r : Role) (u : Val) : Prop := Cat r u ∧ RefsOk W u

/-- **Structural satisfaction**: each location the world gives a role holds
contents of that role's shape. -/
def Shaped {k : Nat} (W : WorldT k) (h : Heap) : Prop :=
  ∀ l r, roleAt W l = some r → ∃ u, h[l]? = some u ∧ Shape W r u

/-! ## The category of contents -/

/-- **The category of a location's contents** (the note *Tolerant frames*,
§3, the class regions; parity-interfaces I1), read from the contents alone:
an array's store, a view store, or any other value. Total on contents. -/
def contentsCategory : Val → Category
  | .arr _ => .array
  | .viewStore .. => .view
  | _ => .value

/-- The entries a store lists, in index order, an array's or a view
store's, a view store's every one present. -/
def storeEntries : Val → Option (List (Option Nat))
  | .arr ls => some ls
  | .viewStore _ cs => some (cs.map some)
  | _ => none

/-- **Contents of a role's category**: what a role's shape admits is of the
role's category (`Cat`). -/
theorem Cat.category {r : Role} {u : Val} (h : Cat r u) : contentsCategory u = r.category := by
  cases r with
  | field | cell | elem => cases u <;> simp_all [Cat, isSourceVal, contentsCategory, Role.category]
  | identity => subst h; rfl
  | store f =>
    cases f with
    | array => obtain ⟨ls, rfl⟩ := h; rfl
    | view => obtain ⟨cs, rfl, -⟩ := h; rfl

/-- **The contents category is the role category** of every allocated
location of a structurally satisfied heap (parity-interfaces I1, the
connecting theorem). -/
theorem Shaped.category {k : Nat} {W : WorldT k} {h : Heap} (hs : Shaped W h) {l : Nat} {r : Role}
    {u : Val} (hr : roleAt W l = some r) (hu : h[l]? = some u) : contentsCategory u = r.category := by
  obtain ⟨u', hu', hsh⟩ := hs l r hr
  rw [hu] at hu'; cases hu'
  exact hsh.1.category


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
  | .view _ _ _ _, h => ⟨h.1, WExt_roleAt hx h.2⟩

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
  | .view _ _ _ _, h => by simpa [RefOk] using h

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
    (hW : WorldAdm W) (hc : CtrAdm c) (hr : ∀ f N, r ≠ .store (.view f N)) : WorldAdm (appendW W r c) := by
  have : appendW W r c = appendWs W [(r, c)] := rfl
  rw [this]; exact WorldAdm_appendWs_plain hW (by simpa using hc) (by simpa using hr)

theorem lookup_appendWs {k : Nat} (W : WorldT k) (es : List (Role × Ctr k)) {i : Nat}
    (_hi : i < es.length) :
    lookup (appendWs W es) ((toList W).length + i) = (es.map Prod.snd)[i]? := by
  simp only [lookup, toList, entries_appendWs, List.map_append]
  rw [List.getElem?_append_right (by simp)]
  simp

end Verification
