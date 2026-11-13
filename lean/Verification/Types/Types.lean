import Verification.Semantics.Worlds
import Verification.Semantics.StorageRoles
/-!
# Semantic types

A type is a family of approximations indexed by a budget, judged against a world
of the same level. `Adm` says which families are types: downward closed with the
world truncated to match, and stable under the world growing.

A record is built from *semantic* field types and compares each stored
contract with its field's type at strictly lower budget. Nothing syntactic is
involved, so a type parameter under a field is interpreted rather than ignored.
-/
namespace Verification

/-- World-indexed predicates, shared by value and argument-list contracts. -/
abbrev WorldFamily (α : Type) := (k : Nat) → WorldT k → α → Prop
abbrev Fam := WorldFamily Val
abbrev ArgFam := WorldFamily (List Val)

/-- Every semantic type restricts to a contract at any level. The contract can
observe only strictly lower levels; higher-level information is unavailable. -/
def res {k : Nat} (T : Fam) : Ctr k := fun j _ W' v => T j W' v

/-- **A record, built from semantic field types.** An object is a finite map
from field names to locations, fixed at allocation; the contract stored at a
named field's location is compared with that field's family, at strictly lower
budget. Taking the field types semantically rather than syntactically is what
makes the clause depend on the environment interpreting it, so a type parameter
under a field is interpreted rather than ignored.

Fields the type does not name are unconstrained, so a record type is open, as
TypeScript's structural types are; every field it does name keeps its exact
contract, which is what makes that openness sound and each field invariant.
The location a named field finds belongs to that key alone (`Owned`), as each
own data property of a JavaScript object is its own storage: so a write of a
named field leaves every other key of the object unchanged
(PROGRAM-TYPING.md, "Separation facts"). -/
abbrev Fields := List (Stored Fam)

/-- **Read capabilities**: a contents type per named key, granting no write
and so stating no role. -/
abbrev Views := List (PropKey × Fam)

/-- The read capability each storage position grants: its key and contents
type, whatever its role. -/
def Stored.views {α : Type} (fs : List (Stored α)) : List (PropKey × α) :=
  fs.map fun p => (p.1, p.2.2)

theorem Stored.mem_views {α : Type} {fs : List (Stored α)} {f : PropKey} {a : α} :
    (f, a) ∈ Stored.views fs ↔ ∃ s, (f, s, a) ∈ fs := by
  simp only [Stored.views, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨g, s, b⟩, hm, rfl, rfl⟩; exact ⟨s, hm⟩
  · rintro ⟨s, hm⟩; exact ⟨(f, s, a), hm, rfl, rfl⟩

@[simp] theorem Stored.views_withRole {α : Type} (s : StorageRole) (fs : List (PropKey × α)) :
    Stored.views (withRole s fs) = fs := by
  simp [Stored.views, withRole, Function.comp_def]

@[simp] theorem Stored.views_append {α : Type} (A B : List (Stored α)) :
    Stored.views (A ++ B) = Stored.views A ++ Stored.views B := by simp [Stored.views]

/-- **Not a host object** (`hostKey`): a primitive, a callable, or an
ordinary object. The families that grant a capability over an object's own
keys (an invariant field, a dictionary, an own-key bound) admit only these. -/
def NoHost (v : Val) : Prop := ∀ flds oid, v = .objAt flds .absent oid → flds.lookup hostKey = none

/-- A record over storage positions. Each position states the role its
location was allocated with (`StorageRole`); worlds of this development
record no role, so the record's meaning reads the key and the contents type,
and the role is what the kinded world checks
(`Kinds.Capability.ofRole`). -/
def recT (fs : Fields) : Fam := fun k W v =>
  ∃ (flds : List (PropKey × Nat)) (oid : Nat), v = .objAt flds .absent oid ∧
    (∀ (f : PropKey) (s : StorageRole) (T : Fam), (f, s, T) ∈ fs →
      ∀ l, flds.lookup f = some l → Owned flds f l) ∧
    ∀ (f : PropKey) (s : StorageRole) (T : Fam), (f, s, T) ∈ fs →
      ∃ (l : Nat) (c : Ctr k), flds.lookup f = some l ∧ lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u ↔ T j W' u

/-- A pair in a zip comes from one position of both lists. -/
theorem mem_zip_index {α β : Type} {as : List α} {bs : List β} {a : α} {b : β}
    (h : (a, b) ∈ as.zip bs) :
    ∃ (i : Nat) (hi : i < as.length) (hj : i < bs.length), as[i] = a ∧ bs[i] = b := by
  induction as generalizing bs with
  | nil => simp at h
  | cons x as ih =>
    cases bs with
    | nil => simp at h
    | cons y bs =>
      rw [List.zip_cons_cons] at h
      rcases List.mem_cons.mp h with he | h'
      · cases he
        exact ⟨0, by simp, by simp, rfl, rfl⟩
      · obtain ⟨i, hi, hj, h1, h2⟩ := ih h'
        exact ⟨i + 1, by simpa using hi, by simpa using hj, h1, h2⟩

/-- **The record a fresh allocation satisfies.** Each named field stands for the
location its position was given, under the contract stated for it there, with
the role the allocation chose for it. -/
theorem recT_alloc {n : Nat} {W : WorldT n} {ns : List PropKey} {ss : List StorageRole}
    {As : List Fam} {base : Nat}
    (hnd : ns.Nodup) (hlen : ns.length = As.length)
    (hl : ∀ (i : Nat) (hi : i < ns.length),
      lookup W (base + i) = some (res (As[i]'(hlen ▸ hi)))) :
    recT (ns.zip (ss.zip As)) n W (.objAt (slots base ns) .absent oid) := by
  refine ⟨slots base ns, oid, rfl, ?_⟩
  refine ⟨fun _ _ _ _ _ hl => owned_of_nodup (slots_nodup base ns) hl, ?_⟩
  intro f s T hm
  obtain ⟨i, hi, hj, rfl, hp⟩ := mem_zip_index hm
  have hT : T = As[i]'(by simp at hj; omega) := by
    rw [List.getElem_zip] at hp
    exact (congrArg Prod.snd hp).symm
  subst hT
  exact ⟨base + i, res (As[i]'(by simp at hj; omega)), lookup_slots hnd hi, hl i hi,
    fun _ _ _ _ => Iff.rfl⟩

/-- What a record type says about one of its fields. -/
theorem recT_at {fs : Fields} {f : PropKey} {s : StorageRole} {A : Fam} (hm : (f, s, A) ∈ fs)
    {k} {W : WorldT k} {v} (h : recT fs k W v) :
    ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr k) (oid : Nat),
      v = .objAt flds .absent oid ∧ flds.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u ↔ A j W' u := by
  obtain ⟨flds, oid, rfl, -, hfs⟩ := h
  obtain ⟨l, c, hl, hw, hag⟩ := hfs f s A hm
  exact ⟨flds, l, c, oid, rfl, hl, hw, hag⟩

/-- The location a record's named field finds belongs to that key alone. -/
theorem recT_owned {fs : Fields} {k : Nat} {W : WorldT k} {flds : List (PropKey × Nat)} {c : CallCode} {oid : Nat}
    (h : recT fs k W (.objAt flds c oid)) {f : PropKey} {s : StorageRole} {T : Fam}
    (hm : (f, s, T) ∈ fs) {l : Nat}
    (hl : flds.lookup f = some l) : Owned flds f l := by
  obtain ⟨flds', oid', he, hown, -⟩ := h
  cases he
  exact hown f s T hm l hl

def nulT : Fam := fun _ _ v => v = .nul

/-- The value a function body produces by completing rather than returning. -/
def undefT : Fam := fun _ _ v => v = .undef

/-- A cell that can actually change observably. -/
def boolT : Fam := fun _ _ v => v = .tru ∨ v = .fls

/-- Every number, at any spelling: the union of its singletons and nothing
more, and what arithmetic yields. -/
def numT : Fam := fun _ _ v => ∃ b, v = .num b

/-- Every string. As with numbers, the family is the union of its singletons. -/
def strT : Fam := fun _ _ v => ∃ s, v = .str s
/-- Every bigint, as the union of its singletons, as numbers are; and every
symbol, an opaque identity. -/
def bigintT : Fam := fun _ _ v => ∃ i, v = .bigint i
def symbolT : Fam := fun _ _ v => ∃ i, v = .sym i

/-! ## Inclusion and agreement -/

def topF : Fam := fun _ _ _ => True

/-- Inclusion of families, at every budget and world. -/
def FamLe {α : Type} (A B : WorldFamily α) : Prop := ∀ (n : Nat) (W : WorldT n) (v : α), A n W v → B n W v

def Agree {α : Type} (T U : WorldFamily α) (n : Nat) : Prop := ∀ m, m < n → ∀ W v, T m W v ↔ U m W v

/-! ## Allocation -/

/-- Allocation cannot invalidate a reference claim: a future world keeps every
contract it already had. -/
theorem recT_mono (fs : Fields) (k : Nat) (W W' : WorldT k) (h : WExt W W')
    (v : Val) (hv : recT fs k W v) : recT fs k W' v := by
  obtain ⟨flds, oid, rfl, hnd, hfs⟩ := hv
  refine ⟨flds, oid, rfl, hnd, ?_⟩
  intro f s T hm
  obtain ⟨l, c, hf, hl, hag⟩ := hfs f s T hm
  exact ⟨l, c, hf, WExt_lookup h hl, hag⟩

/-! ## Admissibility -/


structure Adm {α : Type} (T : WorldFamily α) : Prop where
  down : ∀ (n : Nat) (W : WorldT (n + 1)) (v : α),
    T (n + 1) W v → T n (trunc n (Nat.le_succ n) W) v
  mono : ∀ (n : Nat) (W W' : WorldT n), WExt W W' → ∀ v, T n W v → T n W' v

theorem nulT_adm : Adm nulT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
theorem boolT_adm : Adm boolT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem numT_adm : Adm numT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem strT_adm : Adm strT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
theorem bigintT_adm : Adm bigintT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
theorem symbolT_adm : Adm symbolT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem topF_adm : Adm topF := ⟨fun _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩

/-- A reference is admissible whatever its element type is: the level drop is
absorbed by restricting the stored contract, and allocation only appends. -/
theorem recT_adm (fs : Fields) : Adm (recT fs) := by
  refine ⟨?_, fun n W W' hx v hv => recT_mono fs n W W' hx v hv⟩
  rintro n W v ⟨flds, oid, rfl, hnd, hfs⟩
  refine ⟨flds, oid, rfl, hnd, ?_⟩
  intro f s T hm
  obtain ⟨l, c, hf, hl, hag⟩ := hfs f s T hm
  refine ⟨l, _, hf, lookup_trunc (Nat.le_succ n) W l c hl, ?_⟩
  intro j hj W' u
  exact hag j (by omega) W' u

/-- **A read capability** on named fields. Each names a location whose stored
contract implies the stated family, so a read observes that family; nothing
here permits a write, and the backing invariant, which may be stronger, is
never retyped. A readonly view of a mutable cell is such a capability. -/
def viewT (fs : Views) : Fam := fun k W v =>
  ∀ (f : PropKey) (T : Fam), (f, T) ∈ fs →
    ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr k) (oid : Nat), v = .objAt flds .absent oid ∧
      flds.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → T j W' u

/-- A key of an object's map read one way for the object's life: owned at a
location whose contract admits one fixed value throughout all worlds and
levels, or not owned by an object without a prototype, which a read answers
`undefined` from the value alone (`Step.readMissing`). An object's map of
locations is part of its value, so which case holds never changes. -/
def StableAt {n : Nat} (W : WorldT n) (flds : List (PropKey × Nat)) (key : PropKey) : Prop :=
  match flds.lookup key with
  | some l => ∃ (c : Ctr n) (value : Val), lookup W l = some c ∧ CtrStable c value
  | none => flds.lookup CallArguments.protoField = none

/-- A present stable key supplies the location's stable contract needed by
`HeapObservations.stable_frame`. -/
theorem StableAt.present {n : Nat} {W : WorldT n} {flds : List (PropKey × Nat)} {key : PropKey}
    {l : Nat} (h : StableAt W flds key) (hl : flds.lookup key = some l) :
    ∃ (c : Ctr n) (value : Val), lookup W l = some c ∧ CtrStable c value := by
  simpa [StableAt, hl] using h

/-- The stable keys: each read one way for the object's life (`StableAt`), a
required one owned, since it is also a view, an optional one owned or not. -/
def stableKeysT (keys : List PropKey) : Fam := fun _ W v =>
  ∀ key ∈ keys, ∃ (flds : List (PropKey × Nat)) (oid : Nat),
    v = .objAt flds .absent oid ∧ StableAt W flds key

/-- A stated stable key's object and its reading of the key. -/
theorem stableKeysT_at {keys : List PropKey} {key : PropKey}
    {n : Nat} {W : WorldT n} {v : Val}
    (h : stableKeysT keys n W v) (hk : key ∈ keys) :
    ∃ (flds : List (PropKey × Nat)) (oid : Nat),
      v = .objAt flds .absent oid ∧ StableAt W flds key := h key hk

/-- Truncation restricts stable contracts; extension preserves them. -/
theorem stableKeysT_adm (keys : List PropKey) : Adm (stableKeysT keys) := by
  constructor
  · intro n W v h key hk
    obtain ⟨flds, oid, he, hs⟩ := h key hk
    refine ⟨flds, oid, he, ?_⟩
    unfold StableAt at hs ⊢
    split at hs
    · rename_i l _
      obtain ⟨c, value, hw, hc⟩ := hs
      exact ⟨_, value, lookup_trunc (Nat.le_succ n) W l c hw, hc.restrict (Nat.le_succ n)⟩
    · exact hs
  · intro n W U hx v h key hk
    obtain ⟨flds, oid, he, hs⟩ := h key hk
    refine ⟨flds, oid, he, ?_⟩
    unfold StableAt at hs ⊢
    split at hs
    · obtain ⟨c, value, hw, hc⟩ := hs
      exact ⟨c, value, WExt_lookup hx hw, hc⟩
    · exact hs

/-- Forgetting stable keys weakens their semantic requirement. -/
theorem stableKeysT_weaken {source target : List PropKey}
    (h : ∀ key ∈ target, key ∈ source) : FamLe (stableKeysT source) (stableKeysT target) :=
  fun _ _ _ hs key hk => hs key (h key hk)

/-- A conjunction states the stable keys of both operands. -/
theorem stableKeysT_append (left right : List PropKey) (n : Nat) (W : WorldT n) (v : Val) :
    stableKeysT (left ++ right) n W v ↔ stableKeysT left n W v ∧ stableKeysT right n W v := by
  simp only [stableKeysT, List.mem_append, or_imp, forall_and]

@[simp] theorem stableKeysT_nil (n : Nat) (W : WorldT n) (v : Val) :
    stableKeysT [] n W v := by
  intro key hk
  simp at hk

/-! ## Index keys -/

/-- A **canonical numeric key**: a string some number's `ToString` spells.
These are exactly the strings `s` with `ToString(ToNumber(s)) = s`, the keys
TypeScript's number index signature constrains: "0", "1.5", "-1", "1e+21",
"NaN", "Infinity", but not "01", "1.50" or "-0". They are the keys `o[n]`
reaches for a number `n` (`propertyKey`). -/
def NumericKey (s : String) : Prop := ∃ b : UInt64, numberToString b = s

/-- **The keys an index signature constrains**: every string key (`[k:
string]`), the canonical numeric ones (`[k: number]`), or every symbol key
(`[k: symbol]`). An index over a union of key types is one index per member,
each at the same value type, which together constrain the union's keys. -/
inductive IndexKeys where
  | strings
  | numeric
  | symbols
  deriving Repr, DecidableEq

/-- Whether a class admits a key. The string and symbol key spaces are
disjoint, so no string index reaches a symbol-keyed property. -/
def IndexKeys.Admits : IndexKeys → PropKey → Prop
  | .strings, .str _ => True
  | .numeric, .str s => NumericKey s
  | .symbols, .sym _ => True
  | _, _ => False

/-- One class within another: itself, or the canonical numeric keys within
the strings. -/
def IndexKeys.within (a b : IndexKeys) : Bool :=
  a == b || (a == .numeric && b == .strings)

theorem IndexKeys.within_admits {a b : IndexKeys} (h : a.within b = true) {k : PropKey}
    (hk : a.Admits k) : b.Admits k := by
  unfold within at h
  cases a <;> cases b <;> cases k <;> simp_all [Admits]

/-- Two classes that share a key: one is within the other. -/
def IndexKeys.overlaps (a b : IndexKeys) : Bool := a.within b || b.within a

theorem IndexKeys.overlaps_of_admits {a b : IndexKeys} {k : PropKey} (ha : a.Admits k)
    (hb : b.Admits k) : a.overlaps b = true := by
  cases a <;> cases b <;> cases k <;> simp_all [Admits, overlaps, within]

/-- The key `ToPropertyKey` of a number names is canonical numeric. -/
theorem numeric_admits_number (b : UInt64) : IndexKeys.numeric.Admits (.str (numberToString b)) :=
  ⟨b, rfl⟩

/-- A string's spelling begins as a number's does: a digit, or `-` and a digit. -/
def digitLead : List Char → Bool
  | c :: rest => c.isDigit || (c == '-' && (rest.head?.map Char.isDigit).getD false)
  | [] => false

/-- Whether a spelling begins with a digit. -/
def headDigit (l : List Char) : Bool := (l.head?.map Char.isDigit).getD false

private theorem repr_lead (n : Nat) : headDigit (toString n).toList = true := by
  have h : (toString n).toList = Nat.toDigits 10 n := by
    simp [toString, Nat.repr]
  rw [h]
  cases hd : Nat.toDigits 10 n with
  | nil => exact absurd hd Nat.toDigits_ne_nil
  | cons c rest =>
    have : c ∈ Nat.toDigits 10 n := by rw [hd]; exact List.mem_cons_self
    simpa [headDigit] using Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) this

private theorem decimalBody_head {digits : String} (hd : headDigit digits.toList = true) (d : Int) :
    headDigit (decimalBody digits d).toList = true := by
  cases hl : digits.toList with
  | nil => simp [hl, headDigit] at hd
  | cons c rest =>
  have hc : c.isDigit = true := by simpa [hl, headDigit] using hd
  unfold decimalBody
  simp only
  split
  · simp [headDigit, String.toList_append, hl, hc]
  · split
    · rename_i h
      have hn : 0 < (↑digits.length + d).toNat := by
        simp at h; omega
      obtain ⟨k, hk⟩ : ∃ k, (↑digits.length + d).toNat = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hn).symm⟩
      simp [headDigit, String.toList_append, hl, hc, hk]
    · split
      · simp [headDigit, String.toList_append]
      · split <;> simp_all [headDigit, String.toList_append]

/-- Every number's spelling is `NaN`, an infinity, or begins as a number's
spelling does. -/
theorem numberToString_shape (x : UInt64) :
    numberToString x = "NaN" ∨ numberToString x = "Infinity" ∨ numberToString x = "-Infinity" ∨
      digitLead (numberToString x).toList = true := by
  unfold numberToString
  simp only
  split
  · split
    · exact Or.inl rfl
    · split <;> simp
  · split
    · right; right; right; simp [digitLead]
    · right; right; right
      generalize shortestDigits _ _ _ = p
      obtain ⟨s, d⟩ := p
      have hb := decimalBody_head (repr_lead s) d
      generalize decimalBody (toString s) d = b at hb ⊢
      cases hl : b.toList with
      | nil => simp [hl, headDigit] at hb
      | cons c rest =>
        have hc : c.isDigit = true := by simpa [hl, headDigit] using hb
        split <;> simp [String.toList_append, hl, digitLead, hc]

/-- A key no number spells: not `NaN` nor an infinity, and not beginning as a
number's spelling does. Every identifier-like key is one. -/
def notNumericKey (s : String) : Bool :=
  s != "NaN" && s != "Infinity" && s != "-Infinity" && !digitLead s.toList

theorem notNumericKey_sound {s : String} (h : notNumericKey s = true) : ¬ NumericKey s := by
  rintro ⟨b, rfl⟩
  simp only [notNumericKey, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  rcases numberToString_shape b with e | e | e | e
  · exact h.1.1.1 e
  · exact h.1.1.2 e
  · exact h.1.2 e
  · rw [e] at h; cases h.2

/-- The number a key may spell, read as a JSON number; `NaN` and the
infinities by name. A candidate only: `numericKey?` checks it spells the key. -/
def numericKeyBits (s : String) : Option UInt64 :=
  if s == "NaN" then some 0x7ff8000000000000
  else if s == "Infinity" then some 0x7ff0000000000000
  else if s == "-Infinity" then some 0xfff0000000000000
  else match Lean.Json.parse s with
    | .ok (.num n) => some n.toFloat.toBits
    | _ => none

/-- Whether a key is canonical numeric, decided by a number that spells it. -/
def numericKey? (s : String) : Bool :=
  match numericKeyBits s with
  | some b => numberToString b == s
  | none => false

theorem numericKey?_sound {s : String} (h : numericKey? s = true) : NumericKey s := by
  unfold numericKey? at h
  split at h
  · exact ⟨_, beq_iff_eq.mp h⟩
  · cases h

/-- Whether a class surely admits a key, decided: what a read of a named key
through an index needs. -/
def IndexKeys.surely : IndexKeys → PropKey → Bool
  | .strings, .str _ => true
  | .numeric, .str s => numericKey? s
  | .symbols, .sym _ => true
  | _, _ => false

theorem IndexKeys.surely_admits {K : IndexKeys} {k : PropKey} (h : K.surely k = true) : K.Admits k := by
  cases K <;> cases k <;> simp_all [surely, Admits, numericKey?_sound]

/-- Whether a class may admit a key, decided: false only for a key it
provably does not, which is what an object's field needs to leave an index
unconstrained. -/
def IndexKeys.may : IndexKeys → PropKey → Bool
  | .numeric, .str s => !notNumericKey s
  | K, k => K.surely k

theorem IndexKeys.may_of_admits {K : IndexKeys} {k : PropKey} (h : K.Admits k) : K.may k = true := by
  cases K <;> cases k <;> simp_all [may, surely, Admits]
  rename_i s
  cases hn : notNumericKey s
  · rfl
  · exact absurd h (notNumericKey_sound hn)

/-- **An index view**: an index signature's read capability. The object has no
prototype, and every *present* own field under a key the class `K` admits
has a contract implying `A`. The map of locations is finite, while the
signature ranges over every admitted key. An absent key has no location and
is read as `undefined` by `Step.readMissing`, which needs the object to have
no prototype: a dictionary has none. The actual cell contract may be stricter
than `A`. The plain-object restriction is the same one used by `recT` and
`viewT`. -/
def dictViewT (K : IndexKeys) (A : Fam) : Fam := fun k W v =>
  ∃ (flds : List (PropKey × Nat)) (oid : Nat), v = .objAt flds .absent oid ∧
    (flds.lookup CallArguments.protoField = none ∧ flds.lookup hostKey = none) ∧
    ∀ (f : PropKey) (l : Nat), flds.lookup f = some l → K.Admits f →
      ∃ c : Ctr k, lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → A j W' u

/-- **A writable index** constrains every *present* own field under a key the
class admits as an invariant field is constrained: its location's contract
agrees with `A` below the level, so a write of an `A` value to it keeps every
alias's guarantee. Like the view, it has no prototype and says nothing of an
absent key. The calculus adds no key to an existing object; that TypeScript
lets code holding the dictionary add keys at `A` is the trust boundary
([Source index signatures](../../../docs/SOURCE-CONTRACTS.md#index-signatures)). -/
def dictCellT (K : IndexKeys) (A : Fam) : Fam := fun k W v =>
  ∃ (flds : List (PropKey × Nat)) (oid : Nat), v = .objAt flds .absent oid ∧
    (flds.lookup CallArguments.protoField = none ∧ flds.lookup hostKey = none) ∧
    ∀ (f : PropKey) (l : Nat), flds.lookup f = some l → K.Admits f →
      ∃ c : Ctr k, lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u ↔ A j W' u

/-- A writable index grants its read: an agreeing contract implies `A`. -/
theorem dictCellT_view {K : IndexKeys} {A : Fam} {k : Nat} {W : WorldT k} {v : Val}
    (h : dictCellT K A k W v) : dictViewT K A k W v := by
  obtain ⟨flds, oid, rfl, hp, hf⟩ := h
  refine ⟨flds, oid, rfl, hp, fun f l hl hk => ?_⟩
  obtain ⟨c, hc, hag⟩ := hf f l hl hk
  exact ⟨c, hc, fun j hj W' u hu => (hag j hj W' u).mp hu⟩

/-- An index view over a class gives one over any class within it. -/
theorem dictViewT_within {K K' : IndexKeys} (hw : K'.within K = true) {A : Fam} {k : Nat}
    {W : WorldT k} {v : Val} (h : dictViewT K A k W v) : dictViewT K' A k W v := by
  obtain ⟨flds, oid, rfl, hp, hf⟩ := h
  exact ⟨flds, oid, rfl, hp, fun f l hl hk => hf f l hl (IndexKeys.within_admits hw hk)⟩

/-- So does a writable index. -/
theorem dictCellT_within {K K' : IndexKeys} (hw : K'.within K = true) {A : Fam} {k : Nat}
    {W : WorldT k} {v : Val} (h : dictCellT K A k W v) : dictCellT K' A k W v := by
  obtain ⟨flds, oid, rfl, hp, hf⟩ := h
  exact ⟨flds, oid, rfl, hp, fun f l hl hk => hf f l hl (IndexKeys.within_admits hw hk)⟩

/-- A readable slot provides an upper bound. A writable slot additionally
accepts every member of that bound, without changing the backing invariant. -/
def SlotContract (readonly : Bool) (P Q : Prop) : Prop :=
  (P → Q) ∧ (readonly = false → Q → P)

theorem SlotContract.refl (r : Bool) (P : Prop) : SlotContract r P P :=
  ⟨id, fun _ => id⟩

theorem SlotContract.congr {r : Bool} {P Q R : Prop}
    (h : SlotContract r P Q) (e : Q ↔ R) : SlotContract r P R :=
  ⟨fun p => e.mp (h.1 p), fun hr r => h.2 hr (e.mpr r)⟩

theorem SlotContract.weaken {r s : Bool} {P Q R : Prop}
    (h : SlotContract r P Q) (mode : s = false → r = false)
    (read : Q → R) (write : s = false → R → Q) : SlotContract s P R :=
  ⟨fun p => read (h.1 p), fun hs r => h.2 (mode hs) (write hs r)⟩

/-- **An optional field**: its key, whether it is readonly, and its type. A
readonly one is a view that may be absent. -/
structure OptionalField (α : Type) where
  key : PropKey
  readonly : Bool
  /-- The role of the key's location where the object has it. -/
  role : StorageRole
  type : α
  deriving Repr, DecidableEq

def OptionalField.map {α β : Type} (f : α → β) (o : OptionalField α) : OptionalField β :=
  ⟨o.key, o.readonly, o.role, f o.type⟩

/-- **Optional fields.** Each named key, when the object has it, stands for a
location whose contract is the stated type, as a required field's is, or, for
a readonly one, implies it, as a view's does (`SlotContract`); an absent key is
not constrained, and `Step.readMissing` reads it as `undefined`, which needs
the object to have no prototype: an object lacking one of its optional keys has
none. Presence is fixed: an object's map of locations is fixed at allocation,
so whether a key is present never changes. The plain-object restriction is the
one `recT` uses. -/
def optT (fs : List (OptionalField Fam)) : Fam := fun k W v =>
  ∃ (flds : List (PropKey × Nat)) (oid : Nat), v = .objAt flds .absent oid ∧
    (∀ o ∈ fs, o.readonly = false → ∀ l, flds.lookup o.key = some l → Owned flds o.key l) ∧
    (∀ o ∈ fs, flds.lookup o.key = none → flds.lookup CallArguments.protoField = none) ∧
    ∀ o ∈ fs, ∀ l, flds.lookup o.key = some l →
      ∃ c : Ctr k, lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val),
          SlotContract o.readonly (c j hj W' u) (o.type j W' u)

/-- **An own-key bound**: a finite statement about which keys an object may
own. With `among`, its own keys are among `keys`, as a fresh literal's are
exactly its fields'; without, none of its own keys is among `keys`, as no
array owns a key its prototype provides. Record types are open, so only a
bound says a key is absent, and so that a read of it continues at the
prototype. -/
structure KeyBound where
  among : Bool
  keys : List PropKey
  deriving Repr, DecidableEq

/-- Whether a bound lets the object own a key. -/
def KeyBound.admits (b : KeyBound) (f : PropKey) : Bool := b.keys.contains f == b.among

/-- The object's own keys are the ones the bound admits. Keys are fixed at
allocation, so the bound holds in every world. -/
def ownKeysT (b : KeyBound) : Fam := fun _ _ v =>
  ∃ (flds : List (PropKey × Nat)) (oid : Nat), v = .objAt flds .absent oid ∧ ∀ p ∈ flds, b.admits p.1 = true

theorem ownKeysT_adm (b : KeyBound) : Adm (ownKeysT b) :=
  ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

/-- Own keys are a fact about the field map, whatever the identity. -/
theorem ownKeysT_reid {b : KeyBound} {k : Nat} {W : WorldT k} {flds : List (PropKey × Nat)}
    {oid : Nat} (h : ownKeysT b k W (.objAt flds .absent oid)) (oid' : Nat) :
    ownKeysT b k W (.objAt flds .absent oid') := by
  obtain ⟨_, _, he, hall⟩ := h
  cases he
  exact ⟨flds, oid', rfl, hall⟩

/-- A key the bound does not admit is not the object's own. -/
theorem ownKeysT_lookup {b : KeyBound} {k : Nat} {W : WorldT k}
    {flds : List (PropKey × Nat)} (h : ownKeysT b k W (.objAt flds .absent oid))
    {f : PropKey} (hf : b.admits f = false) : flds.lookup f = none := by
  obtain ⟨flds', oid, he, hk⟩ := h
  cases he
  cases hl : flds.lookup f with
  | none => rfl
  | some l =>
    exfalso
    induction flds with
    | nil => simp [List.lookup] at hl
    | cons p ps ih =>
      obtain ⟨g, m⟩ := p
      rw [List.lookup_cons] at hl
      split at hl
      · rename_i he
        have : f = g := by simpa using he
        subst this
        have := hk _ List.mem_cons_self
        simp_all
      · exact ih (fun q hq => hk q (List.mem_cons_of_mem _ hq)) hl

/-- A present own key is one the bound admits. -/
theorem ownKeysT_admits {b : KeyBound} {k : Nat} {W : WorldT k}
    {flds : List (PropKey × Nat)} (h : ownKeysT b k W (.objAt flds .absent oid))
    {f : PropKey} {l : Nat} (hl : flds.lookup f = some l) : b.admits f = true := by
  cases hb : b.admits f
  · rw [ownKeysT_lookup h hb] at hl
    cases hl
  · rfl

/-- A key the model keeps for itself: the prototype and the array store. No
code adds one as a property; an object owning a property JavaScript spells so
is not one the model represents. -/
def modelKey (k : PropKey) : Bool := k == CallArguments.protoField || k == arrayStoreKey

/-- A bound keeps a class's keys: a key of the class added to an object
leaves the bound true of it. A bound listing keys keeps none (it excludes every
key it does not list); one excluding keys keeps a class admitting none of
them but the model's own. -/
def KeyBound.keeps (K : KeyBound) (C : IndexKeys) : Bool :=
  !K.among && K.keys.all fun k => modelKey k || !C.may k

/-- No optional field constrains a plain object. -/
theorem optT_nil {k} {W : WorldT k} {flds : List (PropKey × Nat)} :
    optT [] k W (.objAt flds .absent oid) :=
  ⟨flds, oid, rfl, fun _ hm => by simp at hm, fun _ hm => by simp at hm, fun _ hm => by simp at hm⟩

/-- What optional fields say of one present key: its location's contract is
the field's type, or implies it for a readonly field. -/
theorem optT_present {fs : List (OptionalField Fam)} {o : OptionalField Fam} (hm : o ∈ fs)
    {k} {W : WorldT k} {flds : List (PropKey × Nat)} (h : optT fs k W (.objAt flds .absent oid))
    {l : Nat} (hl : flds.lookup o.key = some l) :
    ∃ c : Ctr k, lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val),
        SlotContract o.readonly (c j hj W' u) (o.type j W' u) := by
  obtain ⟨flds', oid, heq, -, -, hf⟩ := h
  cases heq
  exact hf o hm l hl

/-- The location a writable optional key finds belongs to that key alone. -/
theorem optT_owned {fs : List (OptionalField Fam)} {o : OptionalField Fam} (hm : o ∈ fs)
    (hro : o.readonly = false)
    {k} {W : WorldT k} {flds : List (PropKey × Nat)} (h : optT fs k W (.objAt flds .absent oid))
    {l : Nat} (hl : flds.lookup o.key = some l) : Owned flds o.key l := by
  obtain ⟨flds', oid, heq, hown, -⟩ := h
  cases heq
  exact hown o hm hro l hl

/-- An object lacking one of its optional keys has no prototype, so the
key reads `undefined`. -/
theorem optT_no_proto {fs : List (OptionalField Fam)} {o : OptionalField Fam} (hm : o ∈ fs)
    {k} {W : WorldT k}
    {flds : List (PropKey × Nat)} (h : optT fs k W (.objAt flds .absent oid))
    (hl : flds.lookup o.key = none) :
    flds.lookup CallArguments.protoField = none := by
  obtain ⟨flds', oid, heq, -, hp, -⟩ := h
  cases heq
  exact hp o hm hl

theorem optT_append (A B : List (OptionalField Fam)) (k : Nat) (W : WorldT k) (v : Val) :
    optT (A ++ B) k W v ↔ optT A k W v ∧ optT B k W v := by
  constructor
  · rintro ⟨flds, oid, rfl, hw, hp, h⟩
    exact ⟨⟨flds, oid, rfl, fun o hm => hw o (List.mem_append_left _ hm),
        fun o hm => hp o (List.mem_append_left _ hm),
        fun o hm => h o (List.mem_append_left _ hm)⟩,
      ⟨flds, oid, rfl, fun o hm => hw o (List.mem_append_right _ hm),
        fun o hm => hp o (List.mem_append_right _ hm),
        fun o hm => h o (List.mem_append_right _ hm)⟩⟩
  · rintro ⟨⟨flds, oid, rfl, hwa, hpa, ha⟩, ⟨flds', oid, he, hwb, hpb, hb⟩⟩
    cases he
    refine ⟨flds, oid, rfl, fun o hm => ?_, fun o hm => ?_, fun o hm => ?_⟩
    · rcases List.mem_append.mp hm with hm | hm
      · exact hwa o hm
      · exact hwb o hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact hpa o hm
      · exact hpb o hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ha o hm
    · exact hb o hm

/-- A dictionary's read guarantee is guarded by the world level, including
when its element type is a recursive graph label. -/
theorem dictViewT_congr {K : IndexKeys} {A B : Fam} {k : Nat} (h : Agree A B k)
    (W : WorldT k) (v : Val) : dictViewT K A k W v ↔ dictViewT K B k W v := by
  constructor <;> rintro ⟨flds, oid, rfl, hp, hf⟩ <;> refine ⟨flds, oid, rfl, hp, ?_⟩
  · intro f l hl hk
    obtain ⟨c, hc, hA⟩ := hf f l hl hk
    exact ⟨c, hc, fun j hj W' u hu => (h j hj W' u).mp (hA j hj W' u hu)⟩
  · intro f l hl hk
    obtain ⟨c, hc, hB⟩ := hf f l hl hk
    exact ⟨c, hc, fun j hj W' u hu => (h j hj W' u).mpr (hB j hj W' u hu)⟩

/-- A writable index's contract is guarded by the world level too. -/
theorem dictCellT_congr {K : IndexKeys} {A B : Fam} {k : Nat} (h : Agree A B k)
    (W : WorldT k) (v : Val) : dictCellT K A k W v ↔ dictCellT K B k W v := by
  constructor <;> rintro ⟨flds, oid, rfl, hp, hf⟩ <;> refine ⟨flds, oid, rfl, hp, ?_⟩
  · intro f l hl hk
    obtain ⟨c, hc, hA⟩ := hf f l hl hk
    exact ⟨c, hc, fun j hj W' u => (hA j hj W' u).trans (h j hj W' u)⟩
  · intro f l hl hk
    obtain ⟨c, hc, hB⟩ := hf f l hl hk
    exact ⟨c, hc, fun j hj W' u => (hB j hj W' u).trans (h j hj W' u).symm⟩

/-- A dictionary view supplies a contract for a key only when that key is
present. Looking up an arbitrary string cannot use this witness alone. -/
theorem dictViewT_present {K : IndexKeys} {A : Fam} {k : Nat} {W : WorldT k}
    {fs : List (PropKey × Nat)} (hd : dictViewT K A k W (.objAt fs .absent oid))
    {f : PropKey} (hk : K.Admits f) {l : Nat} (hl : fs.lookup f = some l) :
    ∃ c : Ctr k, lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → A j W' u := by
  obtain ⟨fs', oid, heq, -, hf⟩ := hd
  cases heq
  exact hf f l hl hk

/-- A dictionary has no prototype, so a key it lacks reads `undefined`. -/
theorem dictViewT_no_proto {K : IndexKeys} {A : Fam} {k : Nat} {W : WorldT k}
    {fs : List (PropKey × Nat)} (hd : dictViewT K A k W (.objAt fs .absent oid)) :
    fs.lookup CallArguments.protoField = none := by
  obtain ⟨fs', oid, heq, hp, -⟩ := hd
  cases heq
  exact hp.1

/-- A dictionary is no host object. -/
theorem dictViewT_noHost {K : IndexKeys} {A : Fam} {k : Nat} {W : WorldT k} {v : Val}
    (hd : dictViewT K A k W v) : NoHost v := by
  obtain ⟨fs', oid, rfl, hp, -⟩ := hd
  intro flds oid' he
  cases he
  exact hp.2

private theorem slots_names (base : Nat) (ns : List PropKey) :
    (slots base ns).map Prod.fst = ns := by
  induction ns generalizing base with
  | nil => simp [slots]
  | cons name rest ih => simp [slots, ih]

/-- An own-key bound the host key is not among: one listing keys without
it, or one excluding it. Its objects are ordinary. -/
def KeyBound.closed (K : KeyBound) : Bool := !K.admits hostKey

theorem KeyBound.closed_lookup {K : KeyBound} (hK : K.closed = true) {n : Nat} {W : WorldT n}
    {flds : List (PropKey × Nat)} {oid : Nat} (h : ownKeysT K n W (.objAt flds .absent oid)) :
    flds.lookup hostKey = none :=
  ownKeysT_lookup h (by simpa [KeyBound.closed] using hK)

/-- A fresh object's own keys are exactly the names it allocated. -/
theorem ownKeysT_slots {K : KeyBound} {k : Nat} {W : WorldT k} {base : Nat}
    {ns : List PropKey} (h : ∀ n ∈ ns, K.admits n = true) :
    ownKeysT K k W (.objAt (slots base ns) .absent oid) := by
  refine ⟨slots base ns, oid, rfl, fun p hp => h _ ?_⟩
  have := List.mem_map_of_mem (f := Prod.fst) hp
  rwa [slots_names] at this

/-- A record owning no key but its fields, and no prototype, is a writable
index over a class whose every field agrees with the index's contract: an
object allocated with exactly those fields is a dictionary from the start. -/
theorem dictCellT_of_recT {fs : Fields} {flds : List (PropKey × Nat)} {K : IndexKeys} {A : Fam}
    {k : Nat} {W : WorldT k} (hrec : recT fs k W (.objAt flds .absent oid))
    (hown : ∀ f l, flds.lookup f = some l → ∃ s T, (f, s, T) ∈ fs)
    (hproto : flds.lookup CallArguments.protoField = none) (hhost : flds.lookup hostKey = none)
    (hA : ∀ f s T, (f, s, T) ∈ fs → K.Admits f →
      ∀ (j : Nat) (_hj : j < k) (W' : WorldT j) (u : Val), T j W' u ↔ A j W' u) :
    dictCellT K A k W (.objAt flds .absent oid) := by
  refine ⟨flds, oid, rfl, ⟨hproto, hhost⟩, fun f l hl hk => ?_⟩
  obtain ⟨s, T, hT⟩ := hown f l hl
  obtain ⟨flds', oid, he, -, hfs⟩ := hrec
  cases he
  obtain ⟨l', c, hl', hc, hag⟩ := hfs f s T hT
  rw [hl] at hl'
  cases hl'
  exact ⟨c, hc, fun j hj W' u => (hag j hj W' u).trans (hA f s T hT hk j hj W' u)⟩

/-- A fresh object owns exactly the keys it allocated. -/
theorem slots_lookup_mem {base : Nat} {ns : List PropKey} {f : PropKey} {l : Nat}
    (h : (slots base ns).lookup f = some l) : f ∈ ns := by
  have hown : ownKeysT ⟨true, ns⟩ 0 (ofList []) (.objAt (slots base ns) .absent 0) :=
    ownKeysT_slots fun n hn => by simp [KeyBound.admits, hn]
  simpa [KeyBound.admits] using ownKeysT_admits hown h

/-- A fresh object lacks every key it did not allocate. -/
theorem slots_lookup_none {base : Nat} {ns : List PropKey} {f : PropKey} (h : f ∉ ns) :
    (slots base ns).lookup f = none := by
  cases hl : (slots base ns).lookup f with
  | none => rfl
  | some l => exact absurd (slots_lookup_mem hl) h

theorem viewT_at {fs : Views} {f : PropKey} {A : Fam} (hm : (f, A) ∈ fs)
    {k} {W : WorldT k} {v} (h : viewT fs k W v) :
    ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr k) (oid : Nat),
      v = .objAt flds .absent oid ∧ flds.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → A j W' u := h f A hm

theorem viewT_append (A B : Views) (k : Nat) (W : WorldT k) (v : Val) :
    viewT (A ++ B) k W v ↔ viewT A k W v ∧ viewT B k W v := by
  simp only [viewT, List.mem_append, or_imp, forall_and]

/-- The key of an array's `length`, a property the model keeps in the array's
store rather than at a location. -/
def lengthKey : PropKey := .str "length"

/-- **An array's `length`, read through a view.** An object owning the array
store has its `length`, an own data property in JavaScript, in its store: a
view of `length` at `T` admits it where every possible length is in `T`,
read below the level, since `push` and `pop` change it. -/
def arrayLenT (T : Fam) : Fam := fun k _ v =>
  (∃ flds oid, v = .objAt flds .absent oid ∧ (flds.lookup arrayStoreKey).isSome = true) ∧
    ∀ (j : Nat), j < k → ∀ (W' : WorldT j) (b : UInt64), T j W' (.num b)

/-- **A record's read capabilities**: each a view (`viewT`), and a view of
`length` met by an array as well (`arrayLenT`). -/
def viewsT (fs : Views) : Fam := fun k W v =>
  ∀ (f : PropKey) (T : Fam), (f, T) ∈ fs → viewT [(f, T)] k W v ∨ (f = lengthKey ∧ arrayLenT T k W v)

theorem viewT_single {f : PropKey} {A : Fam} {k} {W : WorldT k} {v}
    (h : ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr k) (oid : Nat),
      v = .objAt flds .absent oid ∧ flds.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → A j W' u) :
    viewT [(f, A)] k W v := fun g B hg => by
  simp only [List.mem_singleton, Prod.mk.injEq] at hg
  obtain ⟨rfl, rfl⟩ := hg
  exact h

theorem viewsT_of_viewT {fs : Views} {k} {W : WorldT k} {v} (h : viewT fs k W v) : viewsT fs k W v :=
  fun f T hm => .inl (viewT_single (h f T hm))

/-- A view at a key other than `length` is at a location. -/
theorem viewsT_at {fs : Views} {f : PropKey} {A : Fam} (hm : (f, A) ∈ fs) (hf : f ≠ lengthKey)
    {k} {W : WorldT k} {v} (h : viewsT fs k W v) :
    ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr k) (oid : Nat),
      v = .objAt flds .absent oid ∧ flds.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → A j W' u := by
  rcases h f A hm with h | ⟨rfl, -⟩
  · exact viewT_at (List.mem_singleton_self _) h
  · exact absurd rfl hf

/-- A view of an object owning no array store is at a location. -/
theorem viewsT_at_plain {fs : Views} {f : PropKey} {A : Fam} (hm : (f, A) ∈ fs)
    {k} {W : WorldT k} {flds : List (PropKey × Nat)} {oid : Nat}
    (hs : flds.lookup arrayStoreKey = none) (h : viewsT fs k W (.objAt flds .absent oid)) :
    ∃ (flds' : List (PropKey × Nat)) (l : Nat) (c : Ctr k) (oid' : Nat),
      Tm.objAt flds .absent oid = .objAt flds' .absent oid' ∧ flds'.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → A j W' u := by
  rcases h f A hm with h | ⟨-, ⟨flds', oid', he, hst⟩, -⟩
  · exact viewT_at (List.mem_singleton_self _) h
  · cases he; rw [hs] at hst; cases hst

theorem viewsT_append (A B : Views) (k : Nat) (W : WorldT k) (v : Val) :
    viewsT (A ++ B) k W v ↔ viewsT A k W v ∧ viewsT B k W v := by
  simp only [viewsT, List.mem_append, or_imp, forall_and]

/-- A tuple contract on an array store: the required positions' families, the
optional positions', and what any further position must hold, if any may. -/
inductive ArrayPresence where
  | dense | readable | sparse
  deriving DecidableEq, Repr

structure TupleF where
  required : List Fam
  optional : List Fam
  rest : Option Fam
  readonly : Bool := false
  presence : ArrayPresence

/-- The family a tuple contract states for an index: a required position's,
an optional position's, or the rest's where any further position may be. -/
def positionFam (T : TupleF) (i : Nat) : Option Fam :=
  match T.required[i]? with
  | some A => some A
  | none => match T.optional[i - T.required.length]? with
    | some A => some A
    | none => if T.required.length + T.optional.length ≤ i then T.rest else none

/-- Presence is observed at the same depth as the element contract. Readable
stores may have a hole exactly where reading `undefined` meets that contract. -/
def StorePresence (T : TupleF) (ls : List (Option Nat)) (j : Nat) : Prop :=
  match T.presence with
  | .dense => none ∉ ls
  | .sparse => True
  | .readable => ∀ i, ls[i]? = some none → ∀ A, positionFam T i = some A →
      ∀ U : WorldT j, A j U .undef

theorem StorePresence.of_dense {T : TupleF} {ls : List (Option Nat)}
    (h : none ∉ ls) (j : Nat) : StorePresence T ls j := by
  cases hp : T.presence with
  | dense => simpa [StorePresence, hp] using h
  | sparse => simp [StorePresence, hp]
  | readable =>
    simp only [StorePresence, hp]
    intro i hi
    exact False.elim (h (List.mem_of_getElem? hi))

/-- **A store under a tuple contract.** Every required position has a location
under its family (or implying it for a readonly contract); an optional
position is a location under the same capability; a further position exists
only under a rest family, and holds a location under it. `StorePresence`
distinguishes physical density, safe hole reads, and unconstrained holes.
At depth zero no element can be observed; presence is guarded at the same
depth as the element families.
Required positions always exist. Lengths follow: at least the required
positions, at most `maxArrayLength`, and no more than the optional ones
without a rest. -/
def listT (T : TupleF) : Fam := fun k W v =>
  ∃ ls : List (Option Nat), v = .arr ls ∧ (∀ j, j < k → StorePresence T ls j) ∧ T.required.length ≤ ls.length ∧
    ls.length ≤ maxArrayLength ∧
    (T.rest = none → ls.length ≤ T.required.length + T.optional.length) ∧
    (∀ (i : Nat) (A : Fam), T.required[i]? = some A → ∃ (l : Nat) (c : Ctr k),
      ls[i]? = some (some l) ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), SlotContract T.readonly (c j hj W' u) (A j W' u)) ∧
    (∀ (i : Nat) (A : Fam) (l : Nat), T.optional[i]? = some A →
      ls[T.required.length + i]? = some (some l) → ∃ c : Ctr k, lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), SlotContract T.readonly (c j hj W' u) (A j W' u)) ∧
    (∀ (i l : Nat), T.required.length + T.optional.length ≤ i → ls[i]? = some (some l) →
      ∃ (E : Fam) (c : Ctr k), T.rest = some E ∧ lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), SlotContract T.readonly (c j hj W' u) (E j W' u))

theorem listT_adm (T : TupleF) : Adm (listT T) := by
  refine ⟨?_, ?_⟩
  · rintro n W v ⟨ls, rfl, hd, hlen, hmax, hbound, hreq, hopt, hrest⟩
    refine ⟨ls, rfl, (fun j hj => hd j (by omega)), hlen, hmax, hbound, ?_, ?_, ?_⟩
    · intro i A hA
      obtain ⟨l, c, hl, hw, hag⟩ := hreq i A hA
      exact ⟨l, _, hl, lookup_trunc (Nat.le_succ n) W l c hw, fun j hj W' u => hag j (by omega) W' u⟩
    · intro i A l hA hl
      obtain ⟨c, hw, hag⟩ := hopt i A l hA hl
      exact ⟨_, lookup_trunc (Nat.le_succ n) W l c hw, fun j hj W' u => hag j (by omega) W' u⟩
    · intro i l hi hl
      obtain ⟨E, c, hE, hw, hag⟩ := hrest i l hi hl
      exact ⟨E, _, hE, lookup_trunc (Nat.le_succ n) W l c hw, fun j hj W' u => hag j (by omega) W' u⟩
  · rintro n W W' hx v ⟨ls, rfl, hd, hlen, hmax, hbound, hreq, hopt, hrest⟩
    refine ⟨ls, rfl, hd, hlen, hmax, hbound, ?_, ?_, ?_⟩
    · intro i A hA
      obtain ⟨l, c, hl, hw, hag⟩ := hreq i A hA
      exact ⟨l, c, hl, WExt_lookup hx hw, hag⟩
    · intro i A l hA hl
      obtain ⟨c, hw, hag⟩ := hopt i A l hA hl
      exact ⟨c, WExt_lookup hx hw, hag⟩
    · intro i l hi hl
      obtain ⟨E, c, hE, hw, hag⟩ := hrest i l hi hl
      exact ⟨E, c, hE, WExt_lookup hx hw, hag⟩

theorem elemSlots_getElem? (base n i : Nat) :
    (elemSlots base n)[i]? = if i < n then some (some (base + i)) else none := by
  simp only [elemSlots, List.getElem?_map]
  by_cases hi : i < n
  · rw [List.getElem?_eq_getElem (by simpa using hi)]
    simp [hi, List.getElem_range]
  · rw [List.getElem?_eq_none (by simpa using hi)]
    simp [hi]

theorem placeAt_getElem? (ls : List (Option Nat)) (k m i : Nat) :
    (placeAt ls k m)[i]? = if i = k then some (some m)
      else if i < ls.length then ls[i]? else if i < k + 1 then some none else none := by
  unfold placeAt
  have hlen : (ls ++ List.replicate (k + 1 - ls.length) none).length = ls.length + (k + 1 - ls.length) := by
    simp [List.length_append, List.length_replicate]
  by_cases hik : i = k
  · subst hik
    rw [List.getElem?_set_self]
    simp only [if_true]
    have : i < ls.length + (i + 1 - ls.length) := by omega
    simp [this]
  · rw [List.getElem?_set_ne (Ne.symm hik)]
    simp only [hik, if_false]
    by_cases hi : i < ls.length
    · simp [List.getElem?_append_left hi, hi]
    · simp only [hi, if_false]
      rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
      by_cases hk : i < k + 1
      · simp only [hk, if_true]; simp; omega
      · simp only [hk, if_false]; simp; omega

/-- Placing at most at the end leaves a dense store dense: every position is
the placed one, or one the store already had. -/
theorem placeAt_dense {ls : List (Option Nat)} {k m : Nat} (hd : none ∉ ls) (hk : k ≤ ls.length) :
    none ∉ placeAt ls k m := by
  intro hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  rw [placeAt_getElem?] at hi
  split at hi
  · cases hi
  · split at hi
    · exact hd (List.mem_of_getElem? hi)
    · split at hi
      · rename_i h1 h2 h3; omega
      · cases hi

theorem StorePresence.grow {T : TupleF} {ls : List (Option Nat)} {k m j : Nat}
    (h : StorePresence T ls j) (hk : k ≤ ls.length) : StorePresence T (placeAt ls k m) j := by
  cases hp : T.presence with
  | dense => simpa [StorePresence, hp] using placeAt_dense (m := m) (by simpa [StorePresence, hp] using h) hk
  | sparse => simp [StorePresence, hp]
  | readable =>
    simp only [StorePresence, hp] at h ⊢
    intro i hi A hA U
    rw [placeAt_getElem?] at hi
    split at hi
    · cases hi
    · split at hi
      · exact h i hi A hA U
      · split at hi
        · rename_i h1 h2 h3; omega
        · cases hi

theorem elemSlots_dense (base n : Nat) : none ∉ elemSlots base n := by
  simp [elemSlots]

theorem placeAt_length (ls : List (Option Nat)) (k m : Nat) :
    (placeAt ls k m).length = ls.length + (k + 1 - ls.length) := by
  simp [placeAt, List.length_set, List.length_append, List.length_replicate]

/-- **The store a literal allocates.** Each position's location holds the
contract of its family, in order, so the store meets any tuple contract whose
positions those families are, and whose bounds the count respects. -/
theorem listT_alloc {n : Nat} {W : WorldT n} {T : TupleF} {As : List Fam} {base : Nat}
    (hreq : T.required.length ≤ As.length) (hmax : As.length ≤ maxArrayLength)
    (hbound : T.rest = none → As.length ≤ T.required.length + T.optional.length)
    (hpos : ∀ i A, As[i]? = some A → positionFam T i = some A)
    (hl : ∀ (i : Nat) (hi : i < As.length), lookup W (base + i) = some (res (As[i]'hi))) :
    listT T n W (.arr (elemSlots base As.length)) := by
  have hpos' : ∀ (i : Nat) (hi : i < As.length), positionFam T i = some (As[i]'hi) :=
    fun i hi => hpos i _ (List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩)
  refine ⟨_, rfl, (fun j _ => StorePresence.of_dense (elemSlots_dense _ _) j), by simp [elemSlots, hreq],
    by simp [elemSlots, hmax], fun hn => by simpa [elemSlots] using hbound hn, ?_, ?_, ?_⟩
  · intro i A hA
    have hi : i < As.length := by
      have := (List.getElem?_eq_some_iff.mp hA).1; omega
    refine ⟨base + i, res (As[i]'hi), by simp [elemSlots_getElem?, hi], hl i hi, ?_⟩
    have := hpos' i hi
    simp only [positionFam, hA, Option.some.injEq] at this
    subst this
    exact fun _ _ _ _ => SlotContract.refl _ _
  · intro i A l hA hl'
    rw [elemSlots_getElem?] at hl'
    split at hl'
    · rename_i hlt
      cases Option.some.inj (Option.some.inj hl')
      refine ⟨res (As[T.required.length + i]'hlt), hl _ hlt, ?_⟩
      have := hpos' _ hlt
      have hr : T.required[T.required.length + i]? = none := List.getElem?_eq_none (by omega)
      simp only [positionFam, hr, Nat.add_sub_cancel_left, hA, Option.some.injEq] at this
      subst this
      exact fun _ _ _ _ => SlotContract.refl _ _
    · contradiction
  · intro i l hi hl'
    rw [elemSlots_getElem?] at hl'
    split at hl'
    · rename_i hlt
      cases Option.some.inj (Option.some.inj hl')
      have := hpos' i hlt
      have hr : T.required[i]? = none := List.getElem?_eq_none (by omega)
      have ho : T.optional[i - T.required.length]? = none := List.getElem?_eq_none (by omega)
      simp only [positionFam, hr, ho, hi, if_true] at this
      exact ⟨_, res (As[i]'hlt), this, hl i hlt, fun _ _ _ _ => SlotContract.refl _ _⟩
    · contradiction

/-- **A grown store.** Placing a fresh location under the position's family at
the end keeps the tuple contract: every other position is as before, the
bounds still hold because the position is one the contract names, and the
store stays dense because nothing is skipped. -/
theorem listT_grow {n : Nat} {W : WorldT n} {T : TupleF} {ls : List (Option Nat)} {k m : Nat} {A : Fam}
    (h : listT T n W (.arr ls)) (hpos : positionFam T k = some A)
    (hhole : (ls[k]?).bind id = none) (hk : k ≤ ls.length) (hkmax : k < maxArrayLength)
    (hm : lookup W m = some (res A)) :
    listT T n W (.arr (placeAt ls k m)) := by
  obtain ⟨ls', he, hd, hlen, hmax, hbound, hreq, hopt, hrest⟩ := h
  cases he
  have hnamed : T.rest = none → k < T.required.length + T.optional.length := by
    intro hn
    simp only [positionFam] at hpos
    split at hpos
    · rename_i hk; have := (List.getElem?_eq_some_iff.mp hk).1; omega
    · split at hpos
      · rename_i hk; have := (List.getElem?_eq_some_iff.mp hk).1; omega
      · split at hpos
        · rw [hn] at hpos; cases hpos
        · cases hpos
  refine ⟨_, rfl, (fun j hj => StorePresence.grow (hd j hj) hk), by rw [placeAt_length]; omega,
    by rw [placeAt_length]; omega, fun hn => by rw [placeAt_length]; have := hbound hn; have := hnamed hn; omega, ?_, ?_, ?_⟩
  · intro i A' hA
    obtain ⟨l, c, hl, hw, hag⟩ := hreq i A' hA
    have hik : i ≠ k := by
      rintro rfl
      simp [hl] at hhole
    have hi : i < ls.length := (List.getElem?_eq_some_iff.mp hl).1
    exact ⟨l, c, by rw [placeAt_getElem?]; simp only [hik, hi, if_false, if_true]; exact hl, hw, hag⟩
  · intro i A' l hA hl
    rw [placeAt_getElem?] at hl
    split at hl
    · rename_i hik
      cases Option.some.inj (Option.some.inj hl)
      subst hik
      have hr : T.required[T.required.length + i]? = none := List.getElem?_eq_none (by omega)
      simp only [positionFam, hr, Nat.add_sub_cancel_left, hA, Option.some.injEq] at hpos
      subst hpos
      exact ⟨res A', hm, fun _ _ _ _ => SlotContract.refl _ _⟩
    · split at hl
      · exact hopt i A' l hA hl
      · split at hl <;> cases hl
  · intro i l hi hl
    rw [placeAt_getElem?] at hl
    split at hl
    · rename_i hik
      cases Option.some.inj (Option.some.inj hl)
      subst hik
      have hr : T.required[i]? = none := List.getElem?_eq_none (by omega)
      have ho : T.optional[i - T.required.length]? = none := List.getElem?_eq_none (by omega)
      simp only [positionFam, hr, ho, hi, if_true] at hpos
      exact ⟨A, res A, hpos, hm, fun _ _ _ _ => SlotContract.refl _ _⟩
    · split at hl
      · exact hrest i l hi hl
      · split at hl <;> cases hl

theorem viewT_adm (fs : Views) : Adm (viewT fs) := by
  refine ⟨?_, ?_⟩
  · intro n W v h f T hm
    obtain ⟨flds, l, c, oid, rfl, hf, hl, hag⟩ := h f T hm
    exact ⟨flds, l, _, oid, rfl, hf, lookup_trunc (Nat.le_succ n) W l c hl,
      fun j hj W' u => hag j (by omega) W' u⟩
  · intro n W W' hx v h f T hm
    obtain ⟨flds, l, c, oid, rfl, hf, hl, hag⟩ := h f T hm
    exact ⟨flds, l, c, oid, rfl, hf, WExt_lookup hx hl, hag⟩

theorem arrayLenT_adm (T : Fam) : Adm (arrayLenT T) :=
  ⟨fun _ _ _ h => ⟨h.1, fun j hj W' n => h.2 j (by omega) W' n⟩, fun _ _ _ _ _ h => h⟩

theorem viewsT_adm (fs : Views) : Adm (viewsT fs) := by
  refine ⟨?_, ?_⟩
  · intro n W v h f T hm
    rcases h f T hm with h | ⟨hf, h⟩
    · exact .inl ((viewT_adm _).down n W v h)
    · exact .inr ⟨hf, (arrayLenT_adm T).down n W v h⟩
  · intro n W W' hx v h f T hm
    rcases h f T hm with h | ⟨hf, h⟩
    · exact .inl ((viewT_adm _).mono n W W' hx v h)
    · exact .inr ⟨hf, (arrayLenT_adm T).mono n W W' hx v h⟩

theorem optT_adm (fs : List (OptionalField Fam)) : Adm (optT fs) := by
  refine ⟨?_, ?_⟩
  · intro n W v h
    obtain ⟨flds, oid, rfl, hw, hp, hf⟩ := h
    refine ⟨flds, oid, rfl, hw, hp, ?_⟩
    intro o hm l hl
    obtain ⟨c, hc, hag⟩ := hf o hm l hl
    exact ⟨_, lookup_trunc (Nat.le_succ n) W l c hc,
      fun j hj W' u => hag j (by omega) W' u⟩
  · intro n W W' hx v h
    obtain ⟨flds, oid, rfl, hw, hp, hf⟩ := h
    refine ⟨flds, oid, rfl, hw, hp, ?_⟩
    intro o hm l hl
    obtain ⟨c, hc, hag⟩ := hf o hm l hl
    exact ⟨c, WExt_lookup hx hc, hag⟩

theorem dictViewT_adm (K : IndexKeys) (A : Fam) : Adm (dictViewT K A) := by
  refine ⟨?_, ?_⟩
  · intro n W v h
    obtain ⟨flds, oid, rfl, hp, hf⟩ := h
    refine ⟨flds, oid, rfl, hp, ?_⟩
    intro f l hl hk
    obtain ⟨c, hc, hag⟩ := hf f l hl hk
    exact ⟨_, lookup_trunc (Nat.le_succ n) W l c hc,
      fun j hj W' u hu => hag j (by omega) W' u hu⟩
  · intro n W W' hx v h
    obtain ⟨flds, oid, rfl, hp, hf⟩ := h
    refine ⟨flds, oid, rfl, hp, ?_⟩
    intro f l hl hk
    obtain ⟨c, hc, hag⟩ := hf f l hl hk
    exact ⟨c, WExt_lookup hx hc, hag⟩

theorem dictCellT_adm (K : IndexKeys) (A : Fam) : Adm (dictCellT K A) := by
  refine ⟨?_, ?_⟩
  · intro n W v h
    obtain ⟨flds, oid, rfl, hp, hf⟩ := h
    refine ⟨flds, oid, rfl, hp, ?_⟩
    intro f l hl hk
    obtain ⟨c, hc, hag⟩ := hf f l hl hk
    exact ⟨_, lookup_trunc (Nat.le_succ n) W l c hc,
      fun j hj W' u => hag j (by omega) W' u⟩
  · intro n W W' hx v h
    obtain ⟨flds, oid, rfl, hp, hf⟩ := h
    refine ⟨flds, oid, rfl, hp, ?_⟩
    intro f l hl hk
    obtain ⟨c, hc, hag⟩ := hf f l hl hk
    exact ⟨c, WExt_lookup hx hc, hag⟩

theorem Adm.down_le {α : Type} {A : WorldFamily α} (hA : Adm A) :
    ∀ (n i : Nat) (h : i ≤ n) (W : WorldT n) (v : α), A n W v → A i (trunc i h W) v := by
  intro n
  induction n with
  | zero =>
    intro i h W v hv
    have hi : i = 0 := by omega
    subst hi; rw [trunc_id]; exact hv
  | succ p ih =>
    intro i h W v hv
    by_cases hip : i = p + 1
    · subst hip; rw [trunc_id]; exact hv
    · have hle : i ≤ p := by omega
      have := ih i hle (trunc p (Nat.le_succ p) W) v (hA.down p W v hv)
      rwa [trunc_trunc] at this

/-! ## Types whose members are values -/


/-- One admissibility operation for both values and argument lists. -/
theorem Adm.transfer {α : Type} {A : WorldFamily α} (hA : Adm A)
    {n W v} (h : A n W v) (j : Nat) (hj : j ≤ n) (U : WorldT j)
    (hx : WExt (trunc j hj W) U) : A j U v :=
  hA.mono j _ U hx v (hA.down_le n j hj W v h)

theorem Adm.of_transfer {α : Type} {A : WorldFamily α}
    (h : ∀ {n W v}, A n W v → ∀ j (hj : j ≤ n) U,
      WExt (trunc j hj W) U → A j U v) : Adm A :=
  ⟨fun n W v hv => h hv n (Nat.le_succ n) _ (WExt_refl _),
   fun n W U hx v hv => h hv n (Nat.le_refl n) U (by simpa only [trunc_id] using hx)⟩

/-- A type whose members are values. Needed wherever a term must beta-reduce or
be stored. -/
def ValOnly (A : Fam) : Prop := ∀ (j : Nat) (W : WorldT j) (a : Val), A j W a → isVal a = true

theorem nulT_valOnly : ValOnly nulT := fun _ _ _ h => by rw [show _ = Tm.nul from h]; rfl

/-! ## Pointwise union and intersection

Union and intersection of families are the set operations at each index.
Both preserve admissibility. They are *not* guards: `F(X) = X ∪ A` is only
non-expansive, so a recursive node `μX. X ∨ null` is excluded the same way
`μX. X` is — flatten unions, recurse only through `ref` / `arr`. -/

def unionT (A B : Fam) : Fam := fun n W v => A n W v ∨ B n W v

def interT (A B : Fam) : Fam := fun n W v => A n W v ∧ B n W v

theorem unionT_adm (A B : Fam) (hA : Adm A) (hB : Adm B) : Adm (unionT A B) := by
  constructor
  · intro n W v hv
    rcases hv with h | h
    · exact Or.inl (hA.down n W v h)
    · exact Or.inr (hB.down n W v h)
  · intro n W W' hx v hv
    rcases hv with h | h
    · exact Or.inl (hA.mono n W W' hx v h)
    · exact Or.inr (hB.mono n W W' hx v h)

theorem interT_adm (A B : Fam) (hA : Adm A) (hB : Adm B) : Adm (interT A B) := by
  constructor
  · intro n W v hv
    exact ⟨hA.down n W v hv.1, hB.down n W v hv.2⟩
  · intro n W W' hx v hv
    exact ⟨hA.mono n W W' hx v hv.1, hB.mono n W W' hx v hv.2⟩

end Verification
