import Verification.Semantics.ClosedFootprints
import Verification.Semantics.SafeIntegers
import Verification.Semantics.Linear

/-! Index facts: what a slot holds as an array index, a length, a bound by a
store's length, a safe integer or a linear fact (PROGRAM-TYPING.md, "Writes at
a checked index"; ARITHMETIC.md, "Linear facts"). Heap knowledge carries them as atoms
(`HeapKnowledge.IndexAtom`); a signature states its precondition with them
(`CallEffects.Effect.pre`). -/
namespace Verification.HeapKnowledge

/-- **The entry state** of a run (the note "Tolerant frames", §6,
"Triples"): the environment and the heap the command started in. Facts are
satisfied relative to it (`IndexFact.HoldsAt`), and it is the same at every
state of one run. -/
structure EntryState where
  env : Env
  heap : Heap

variable {ε : EntryState}

/-- The safe integer a value is, where it is one (`SafeIntegers.safeIntOfBits`). -/
def intValue : Val → Option Int
  | .num b => SafeIntegers.safeIntOfBits b
  | _ => none

/-- The integers an environment's slots hold, `0` where a slot holds no safe
integer: the valuation the linear facts are read at. -/
def valuation (ρ : Env) (s : Nat) : Int := (intValue (ρ s)).getD 0

theorem intValue_safe {v : Val} {i : Int} (h : intValue v = some i) : ∃ b, v = .num b ∧ SafeIntegers.SafeInt b i := by
  cases v <;> simp only [intValue, reduceCtorEq] at h
  exact ⟨_, rfl, SafeIntegers.safeIntOfBits_sound h⟩

theorem intValue_num {b : UInt64} {i : Int} (h : SafeIntegers.SafeInt b i) : intValue (.num b) = some i :=
  SafeIntegers.safeIntOfBits_complete h

/-- What a term reads of the value its path ends at: the safe integer it is
(`value`), the length of its array store (`length`), the length of
the typed array it is (`view`), or the count of UTF-16 code units of the
string it is (`strLength`). -/
inductive Term.Kind where
  | value
  | length
  | view
  | strLength
  deriving DecidableEq, Repr, Hashable

/-- A term of a linear fact (ARITHMETIC.md, "Linear facts"): a root slot,
a path of named data fields read in turn from the value it holds, and what
the term reads of the value the path ends at (`Term.Kind`): the safe integer
it is; the length of its array store, as the calculus's `lenOf` gives it
(`Step.lenV`), at most `maxArrayLength`; or the length of the typed
array it is, the safe integer at least `0` the location of its
`viewLengthKey` holds (`viewLengthOf`); or the count of UTF-16 code units of
the string it is, at most `maxStringLength` (`strLengthOf`). The empty path
reads the slot's value itself. -/
structure Term where
  kind : Term.Kind
  slot : Nat
  path : List String
  atEntry : Bool := false
  deriving DecidableEq, Repr

/-- A term's kind, slot and path, which a term's hash reads. -/
structure Term.Root where
  kind : Term.Kind
  slot : Nat
  path : List String
  deriving Hashable

/-- A term's hash: its kind's, slot's and path's, with its entry mark mixed
in for an entry term. It is consistent with equality: equal terms have equal
fields, so equal hashes. A collision identifies no keys: the caches keep
their keys and compare them by equality. -/
instance : Hashable Term where
  hash t := let r : UInt64 := hash (Term.Root.mk t.kind t.slot t.path)
    if t.atEntry then mixHash r 1 else r

namespace Term

/-- The safe integer a slot holds. -/
def value (s : Nat) : Term := ⟨.value, s, [], false⟩
/-- The length of the array store a slot holds. -/
def length (s : Nat) : Term := ⟨.length, s, [], false⟩
/-- The length of the string a slot holds. -/
def strLength (s : Nat) : Term := ⟨.strLength, s, [], false⟩

/-- Whether a term reads no current heap: an entry term, which reads the
entry state, or a slot's own value, or the length of the string it is. -/
def envOnly (t : Term) : Bool :=
  t.atEntry || ((t.kind == .value || t.kind == .strLength) && t.path.isEmpty)

def Kind.code : Kind → Nat
  | .value => 0
  | .length => 1
  | .view => 2
  | .strLength => 3

/-- A term's place by slot and kind, which normal forms sort by. -/
def code (t : Term) : Nat := 8 * t.slot + 2 * t.kind.code + (if t.atEntry then 1 else 0)

/-- Paths in lexicographic order, the empty path first. -/
def pathBefore : List String → List String → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: p, b :: q => decide (a < b) || (a == b && pathBefore p q)

/-- An order on terms: by slot and kind, then by path. -/
def before (a b : Term) : Bool := a.code < b.code || (a.code == b.code && pathBefore a.path b.path)

instance : LT Term := ⟨fun a b => a.before b = true⟩

instance : DecidableRel (α := Term) (· < ·) := fun a b => inferInstanceAs (Decidable (a.before b = true))

/-- The slots of the current environment a term reads: none of an entry
term, its slot of any other. -/
def slots (t : Term) : List Nat := if t.atEntry then [] else [t.slot]

/-- The slots of the entry environment a term reads: its slot of an entry
term, none of any other. -/
def entrySlots (t : Term) : List Nat := if t.atEntry then [t.slot] else []

theorem mem_slots {t : Term} {s : Nat} : s ∈ t.slots ↔ t.atEntry = false ∧ s = t.slot := by
  unfold slots; cases t.atEntry <;> simp

/-- The term with its slot renamed, where the map names one. -/
def mapM (f : Nat → Option Nat) (t : Term) : Option Term :=
  if t.atEntry then some t else (f t.slot).map fun s => { t with slot := s }

/-- A renamed term: an entry term as it is, any other with its slot renamed. -/
theorem mapM_cases {f : Nat → Option Nat} {t t' : Term} (h : t.mapM f = some t') :
    (t.atEntry = true ∧ t' = t) ∨ (t.atEntry = false ∧ f t.slot = some t'.slot ∧ t' = { t with slot := t'.slot }) := by
  unfold mapM at h
  cases he : t.atEntry
  · simp only [he, Bool.false_eq_true, if_false, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact .inr ⟨rfl, hs, rfl⟩
  · simp only [he, if_true, Option.some.injEq] at h
    exact .inl ⟨rfl, h.symm⟩

theorem mapM_slot {f : Nat → Option Nat} {t t' : Term} (h : t.mapM f = some t') (he : t.atEntry = false) :
    f t.slot = some t'.slot := by
  rcases mapM_cases h with ⟨h1, -⟩ | ⟨-, h2, -⟩
  · rw [he] at h1; cases h1
  · exact h2

/-- A renamed term reads the images of the slots its source reads. -/
theorem mapM_slots {f : Nat → Option Nat} {t t' : Term} (h : t.mapM f = some t') :
    ∀ y ∈ t'.slots, ∃ x ∈ t.slots, f x = some y := by
  intro y hy
  rcases mapM_cases h with ⟨he, rfl⟩ | ⟨he, hs, h3⟩
  · simp [slots, he] at hy
  · rw [h3] at hy
    simp only [slots, he, Bool.false_eq_true, if_false, List.mem_singleton] at hy
    subst hy
    exact ⟨t.slot, by simp [slots, he], hs⟩

theorem mapM_atEntry {f : Nat → Option Nat} {t t' : Term} (h : t.mapM f = some t') : t'.atEntry = t.atEntry := by
  rcases mapM_cases h with ⟨-, rfl⟩ | ⟨-, -, h3⟩
  · rfl
  · rw [h3]

/-- The term with its slot renamed by a total map. -/
def mapM' (f : Nat → Nat) (t : Term) : Term := if t.atEntry then t else { t with slot := f t.slot }

theorem mapM_eq (f : Nat → Nat) : Term.mapM (some ∘ f) = some ∘ mapM' f := by
  funext t; obtain ⟨k, s, p, a⟩ := t; cases a <;> rfl

/-- **The term with its entry slot translated**, where the map names one: the
change of entry frame (a call substitution, a frame with a receiver in front
read past it). A current term is left as it is; renaming current slots
within one invocation is `mapM`, which leaves every entry term as it is. -/
def mapEntry (g : Nat → Option Nat) (t : Term) : Option Term :=
  if t.atEntry then (g t.slot).map fun s => { t with slot := s } else some t

theorem mapEntry_cases {g : Nat → Option Nat} {t t' : Term} (h : t.mapEntry g = some t') :
    (t.atEntry = false ∧ t' = t) ∨ (t.atEntry = true ∧ g t.slot = some t'.slot ∧ t' = { t with slot := t'.slot }) := by
  unfold mapEntry at h
  cases he : t.atEntry
  · simp only [he, Bool.false_eq_true, if_false, Option.some.injEq] at h
    exact .inl ⟨rfl, h.symm⟩
  · simp only [he, if_true, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact .inr ⟨rfl, hs, rfl⟩

end Term

/-- **The read bridge, one field.** Where the object `o` owns `f` at a location
holding `v`, the path `f :: p` read from `o` reads what `p` reads from `v`. -/
theorem readPath_cons {h : Heap} {fs : List (PropKey × Nat)} {c : CallCode} {oid l : Nat} {v : Val} {f : String}
    {p : List String} (hl : fs.lookup (.str f) = some l) (hv : h[l]? = some v) :
    readPath h (.objAt fs c oid) (f :: p) = readPath h v p := by
  simp only [readPath, hl, hv]

/-- A heap extension keeps what a path reads: each location it reads lies in
the old heap. -/
theorem readPath_extend {h : Heap} (vs : List Val) :
    ∀ {v : Val} {p : List String} {w : Val}, readPath h v p = some w → readPath (h ++ vs) v p = some w := by
  intro v p
  induction p generalizing v with
  | nil => intro w hw; exact hw
  | cons f p ih =>
    intro w hw
    cases v with
    | objAt fs c oid =>
      simp only [readPath] at hw ⊢
      split at hw
      · rename_i l hl
        split at hw
        · rename_i u hu
          simp only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hu).1, hu]
          exact ih hw
        · cases hw
      · cases hw
    | _ => simp [readPath] at hw

/-- What a guard compares the value a path reads with (ARITHMETIC.md,
"Guarded clauses"): `null` or `undefined`. -/
inductive GuardTag where
  | null
  | undef
  | tru
  | fls
  deriving DecidableEq, Repr, Hashable

/-- The value a guard tag names. -/
def GuardTag.val : GuardTag → Val
  | .null => .nul
  | .undef => .undef
  | .tru => .tru
  | .fls => .fls

/-- The value a guard's path reads from a value: each step the read of a
string key, the location's value where the object owns the key, `undefined`
where it owns neither the key nor a prototype (`HeapFacts.ReadGave`). A
missing intermediate object reads nothing. -/
def readGuard (h : Heap) : Val → List String → Option Val
  | v, [] => some v
  | .objAt fs _ _, f :: p => match fs.lookup (.str f) with
    | some l => match h[l]? with
      | some v => readGuard h v p
      | none => none
    | none => if fs.lookup CallArguments.protoField = none then readGuard h .undef p else none
  | _, _ :: _ => none

/-- A heap extension keeps what a guard's path reads. -/
theorem readGuard_extend {h : Heap} (vs : List Val) :
    ∀ {v : Val} {p : List String} {w : Val}, readGuard h v p = some w → readGuard (h ++ vs) v p = some w := by
  intro v p
  induction p generalizing v with
  | nil => intro w hw; exact hw
  | cons f p ih =>
    intro w hw
    cases v with
    | objAt fs c oid =>
      simp only [readGuard] at hw ⊢
      split at hw
      · rename_i l hl
        split at hw
        · rename_i u hu
          simp only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hu).1, hu]
          exact ih hw
        · cases hw
      · split at hw
        · rename_i hp
          simp only [hp, ite_true]
          exact ih hw
        · cases hw
    | _ => simp [readGuard] at hw

/-- Whether a change keeps what a guard's path reads: the empty path reads
the slot alone; one field, its location where `first` keeps it, or an
absent key. -/
def guardKept (first : Nat → String → Bool) (s : Nat) : List String → Bool
  | [] => true
  | [g] => first s g
  | _ => false

theorem readGuard_kept {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {s : Nat} {p : List String} {v : Val}
    (hf : ∀ s g fs cd o l v, first s g = true → ρ s = .objAt fs cd o → fs.lookup (.str g) = some l →
      h[l]? = some v → h'[l]? = some v)
    (hk : guardKept first s p = true) (hv : readGuard h (ρ s) p = some v) : readGuard h' (ρ s) p = some v := by
  match p, hk with
  | [], _ => exact hv
  | [g], hk =>
    simp only [guardKept] at hk
    cases hs : ρ s with
    | objAt fs cd o =>
      rw [hs] at hv
      simp only [readGuard] at hv ⊢
      split at hv
      · rename_i l hl
        split at hv
        · rename_i u hu
          simp only [hf s g fs cd o l u hk hs hl hu]
          exact hv
        · cases hv
      · exact hv
    | _ => rw [hs] at hv; simp [readGuard] at hv

/-- A path of at most one field whose first location `first` keeps reads
what it read. -/
theorem readPath_guardKept {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {s : Nat} {p : List String} {v : Val}
    (hf : ∀ s g fs cd o l v, first s g = true → ρ s = .objAt fs cd o → fs.lookup (.str g) = some l →
      h[l]? = some v → h'[l]? = some v)
    (hk : guardKept first s p = true) (hv : readPath h (ρ s) p = some v) : readPath h' (ρ s) p = some v := by
  match p, hk with
  | [], _ => exact hv
  | [g], hk =>
    simp only [guardKept] at hk
    cases hs : ρ s with
    | objAt fs cd o =>
      rw [hs] at hv
      simp only [readPath] at hv ⊢
      split at hv
      · rename_i l hl
        split at hv
        · rename_i u hu
          simp only [hf s g fs cd o l u hk hs hl hu]
          exact hv
        · cases hv
      · cases hv
    | _ => rw [hs] at hv; simp [readPath] at hv

/-- The length of the array store a value holds, read in the heap, where it
is at most `maxArrayLength`. -/
def lengthOf (h : Heap) (v : Val) : Option Int :=
  match Footprints.storeOf v with
  | some s => match h[s]? with
    | some (.arr ls) => if ls.length ≤ maxArrayLength then some (ls.length : Int) else none
    | _ => none
  | none => none

theorem lengthOf_store {h : Heap} {v : Val} {n : Int} (hl : lengthOf h v = some n) :
    ∃ s ls, Footprints.storeOf v = some s ∧ h[s]? = some (.arr ls) ∧ n = (ls.length : Int) ∧
      ls.length ≤ maxArrayLength := by
  unfold lengthOf at hl
  split at hl
  · rename_i s hs
    split at hl
    · rename_i ls hls
      split at hl
      · cases hl; exact ⟨s, ls, hs, hls, rfl, by assumption⟩
      · cases hl
    · cases hl
  · cases hl

theorem lengthOf_of_store {h : Heap} {v : Val} {s : Nat} {ls : List (Option Nat)} (hs : Footprints.storeOf v = some s)
    (hl : h[s]? = some (.arr ls)) (hm : ls.length ≤ maxArrayLength) : lengthOf h v = some (ls.length : Int) := by
  simp only [lengthOf, hs, hl, hm, ite_true]

/-- The length of the typed array a value is, read in the heap: the
value is an object owning `hostKey`, a host object, whose field map gives
`viewLengthKey` a location holding a safe integer at least `0`. -/
def viewLengthOf (h : Heap) : Val → Option Int
  | .objAt fs _ _ =>
    if (fs.lookup hostKey).isSome then
      match fs.lookup viewLengthKey with
      | some l => match h[l]? with
        | some (.num b) => match SafeIntegers.safeIntOfBits b with
          | some n => if 0 ≤ n then some n else none
          | none => none
        | _ => none
      | none => none
    else none
  | _ => none

theorem viewLengthOf_range {h : Heap} {v : Val} {n : Int} (hv : viewLengthOf h v = some n) :
    0 ≤ n ∧ n ≤ 2 ^ 53 - 1 := by
  unfold viewLengthOf at hv
  split at hv
  · split at hv
    · split at hv
      · split at hv
        · rename_i b _
          split at hv
          · rename_i m hm
            split at hv
            · cases hv
              rename_i h0
              have hb := (SafeIntegers.safeIntOfBits_sound hm).1
              have : (n.natAbs : Int) = n := Int.natAbs_of_nonneg h0
              exact ⟨h0, by omega⟩
            · cases hv
          · cases hv
        · cases hv
      · cases hv
    · cases hv
  · cases hv

/-- A heap extension keeps the typed-array length of what a value is: its
location lies in the old heap. -/
theorem viewLengthOf_extend {h : Heap} (vs : List Val) {v : Val} {n : Int} (hl : viewLengthOf h v = some n) :
    viewLengthOf (h ++ vs) v = some n := by
  unfold viewLengthOf at hl ⊢
  split at hl
  · split at hl
    · split at hl
      · rename_i l _
        split at hl
        · rename_i b hb
          rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hb).1, hb]
          simp_all
        · cases hl
      · cases hl
    · cases hl
  · cases hl

/-- The length of the string a value is: its count of UTF-16 code units,
where that is at most `maxStringLength`, the most a JavaScript string holds. -/
def strLengthOf : Val → Option Int
  | .str s => if (utf16Units s).length ≤ maxStringLength then some (utf16Units s).length else none
  | _ => none

theorem strLengthOf_range {v : Val} {n : Int} (hv : strLengthOf v = some n) :
    0 ≤ n ∧ n ≤ 2 ^ 53 - 1 := by
  unfold strLengthOf at hv
  split at hv
  · split at hv
    · cases hv; rename_i hl; simp only [maxStringLength] at hl; omega
    · cases hv
  · cases hv

/-- What a kind of term reads of a value. -/
def kindValue (h : Heap) : Term.Kind → Val → Option Int
  | .value, v => intValue v
  | .length, v => lengthOf h v
  | .view, v => viewLengthOf h v
  | .strLength, v => strLengthOf v

/-- The integer a term denotes, where it denotes one: what its kind reads of
the value its path reads from its slot's value. -/
def termAt (ρ : Env) (h : Heap) (t : Term) : Option Int :=
  (readPath h (ρ t.slot) t.path).bind (kindValue h t.kind)

/-- The integer a term denotes, where it denotes one (the note "Tolerant
frames", section 6, "Triples"): an entry term `old(t)` what `t` denotes at
the entry state, any other term what it denotes at `ρ`, `h`. -/
def termValue (ε : EntryState) (ρ : Env) (h : Heap) (t : Term) : Option Int :=
  if t.atEntry then termAt ε.env ε.heap t else termAt ρ h t

theorem termValue_now {ρ : Env} {h : Heap} {t : Term} (he : t.atEntry = false) :
    termValue ε ρ h t = termAt ρ h t := by
  simp only [termValue, he, Bool.false_eq_true, if_false]

theorem termValue_atEntry {ρ : Env} {h : Heap} {t : Term} (he : t.atEntry = true) :
    termValue ε ρ h t = termAt ε.env ε.heap t := by
  simp only [termValue, he, if_true]

/-- **An entry term reads the entry state alone**: it denotes the same at
every environment and heap. -/
theorem termValue_entry_invariant {ρ ρ' : Env} {h h' : Heap} {t : Term} (he : t.atEntry = true) :
    termValue ε ρ h t = termValue ε ρ' h' t := by
  rw [termValue_atEntry he, termValue_atEntry he]

theorem termValue_entry_some {ρ ρ' : Env} {h h' : Heap} {t : Term} {n : Int} (he : t.atEntry = true)
    (ht : termValue ε ρ h t = some n) : termValue ε ρ' h' t = some n := by
  rw [← termValue_entry_invariant (ρ := ρ) (h := h) he]; exact ht

theorem termValue_nil {ρ : Env} {h : Heap} {k : Term.Kind} {s : Nat} :
    termValue ε ρ h ⟨k, s, [], false⟩ = kindValue h k (ρ s) := rfl

@[simp] theorem termValue_value {ρ : Env} {h : Heap} {s : Nat} : termValue ε ρ h (.value s) = intValue (ρ s) := rfl
@[simp] theorem termValue_length {ρ : Env} {h : Heap} {s : Nat} : termValue ε ρ h (.length s) = lengthOf h (ρ s) := rfl
@[simp] theorem termValue_strLength {ρ : Env} {h : Heap} {s : Nat} : termValue ε ρ h (.strLength s) = strLengthOf (ρ s) := rfl

theorem termValue_slot {ρ ρ' : Env} {h : Heap} {t : Term} {s : Nat} (hs : ρ' s = ρ t.slot)
    (he : t.atEntry = false) :
    termValue ε ρ' h { t with slot := s } = termValue ε ρ h t := by
  simp only [termValue, he, Bool.false_eq_true, if_false, termAt, hs]

/-- A term reads the current environment at its current slot only. -/
theorem termValue_congr {ρ ρ' : Env} {h : Heap} {t : Term} (hs : t.atEntry = false → ρ t.slot = ρ' t.slot) :
    termValue ε ρ h t = termValue ε ρ' h t := by
  cases he : t.atEntry
  · simp only [termValue, he, Bool.false_eq_true, if_false, termAt, hs he]
  · exact termValue_entry_invariant he

/-- A term reads the entry environment at its entry slot only, and the
entry heap. -/
theorem termValue_congr_entry {ε' : EntryState} {ρ : Env} {h : Heap} {t : Term} (hh : ε.heap = ε'.heap)
    (hs : t.atEntry = true → ε.env t.slot = ε'.env t.slot) : termValue ε ρ h t = termValue ε' ρ h t := by
  cases he : t.atEntry
  · rw [termValue_now he, termValue_now he]
  · simp only [termValue, he, if_true, termAt, hh, hs he]

/-- **A renamed term denotes what it did** where each renamed slot holds its
source slot's value: an entry term is not renamed. -/
theorem termValue_mapM {f : Nat → Option Nat} {ρ ρ' : Env} {h : Heap} {t t' : Term} (hm : t.mapM f = some t')
    (hf : t.atEntry = false → ∀ j, f t.slot = some j → ρ' j = ρ t.slot) :
    termValue ε ρ' h t' = termValue ε ρ h t := by
  rcases Term.mapM_cases hm with ⟨he, rfl⟩ | ⟨he, hs, h3⟩
  · exact termValue_entry_invariant he
  · rw [h3]; exact termValue_slot (hf he _ hs) he

/-- **An entry term translated to another entry frame denotes what it did**
where each translated entry slot holds its source slot's value there and the
entry heaps agree; a current term is not translated. -/
theorem termValue_mapEntry {ε' : EntryState} {g : Nat → Option Nat} {ρ : Env} {h : Heap} {t t' : Term}
    (hm : t.mapEntry g = some t') (hh : ε'.heap = ε.heap)
    (hg : t.atEntry = true → ∀ j, g t.slot = some j → ε'.env j = ε.env t.slot) :
    termValue ε' ρ h t' = termValue ε ρ h t := by
  rcases Term.mapEntry_cases hm with ⟨he, rfl⟩ | ⟨he, hs, h3⟩
  · rw [termValue_now he, termValue_now he]
  · rw [h3]
    simp only [termValue, he, if_true, termAt, hh, hg he _ hs]

theorem termValue_isSome {ρ : Env} {h : Heap} {t : Term} (ht : (termValue ε ρ h t).isSome) (he : t.atEntry = false) :
    ∃ v n, readPath h (ρ t.slot) t.path = some v ∧ kindValue h t.kind v = some n ∧ termValue ε ρ h t = some n := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ht
  rw [termValue_now he] at hn ⊢
  simp only [termAt, Option.bind_eq_some_iff] at hn
  obtain ⟨v, hv, hk⟩ := hn
  exact ⟨v, n, hv, hk, by simp [termAt, hv, hk]⟩

/-- A term that denotes an integer denotes what its kind reads of a value in
some heap: the current one, or the entry heap for an entry term. -/
theorem termValue_kind {ρ : Env} {h : Heap} {t : Term} (ht : (termValue ε ρ h t).isSome) :
    ∃ (H : Heap) (v : Val) (n : Int), kindValue H t.kind v = some n ∧ termValue ε ρ h t = some n := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ht
  unfold termValue termAt at hn
  split at hn
  · obtain ⟨v, -, hk⟩ := Option.bind_eq_some_iff.mp hn
    exact ⟨_, v, n, hk, by unfold termValue termAt; split <;> simp_all⟩
  · obtain ⟨v, -, hk⟩ := Option.bind_eq_some_iff.mp hn
    exact ⟨_, v, n, hk, by unfold termValue termAt; split <;> simp_all⟩

/-- The integers terms denote, `0` where one denotes none: the valuation the
linear facts are read at. -/
def termValuation (ε : EntryState) (ρ : Env) (h : Heap) (t : Term) : Int := (termValue ε ρ h t).getD 0

/-- A linear form over slots' values as one over value terms. -/
def valueForm (F : Linear.Form Nat) : Linear.Form Term := F.map fun p => (.value p.1, p.2)

/-- A linear fact over slots' values as one over value terms. -/
def valueFact : Linear.Fact Nat → Linear.Fact Term
  | .le F d => .le (valueForm F) d
  | .ne F d => .ne (valueForm F) d

theorem eval_valueForm (ρ : Env) (h : Heap) (F : Linear.Form Nat) :
    Linear.Form.eval (termValuation ε ρ h) (valueForm F) = Linear.Form.eval (valuation ρ) F := by
  induction F with
  | nil => rfl
  | cons p t ih => simp only [valueForm, List.map_cons, Linear.Form.eval] at ih ⊢; rw [ih]; rfl

theorem holds_valueFact {ρ : Env} {h : Heap} {F : Linear.Fact Nat} :
    (valueFact F).Holds (termValuation ε ρ h) ↔ F.Holds (valuation ρ) := by
  cases F <;> simp only [valueFact, Linear.Fact.Holds, eval_valueForm]

theorem vars_valueFact (F : Linear.Fact Nat) : (valueFact F).vars = F.vars.map .value := by
  cases F <;> simp [valueFact, Linear.Fact.vars, valueForm, Function.comp_def]

/-- A heap extension keeps the length of what a value is: a store lies in the
old heap. -/
theorem lengthOf_extend {h : Heap} (vs : List Val) {v : Val} {n : Int} (hl : lengthOf h v = some n) :
    lengthOf (h ++ vs) v = some n := by
  obtain ⟨s, ls, hs, hls, rfl, hm⟩ := lengthOf_store hl
  exact lengthOf_of_store hs (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hls).1, hls]) hm

/-- A term reading the environment alone denotes the same in every heap. -/
theorem termValue_envOnly {ρ : Env} {h h' : Heap} {t : Term} (ht : t.envOnly = true) :
    termValue ε ρ h t = termValue ε ρ h' t := by
  cases he : t.atEntry
  · obtain ⟨k, s, p, a⟩ := t
    simp only at he; subst he
    simp only [Term.envOnly, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      List.isEmpty_iff] at ht
    obtain ⟨rfl | rfl, rfl⟩ := ht <;> rfl
  · exact termValue_entry_invariant he

theorem kindValue_extend {h : Heap} (vs : List Val) {k : Term.Kind} {v : Val} {n : Int} (hk : kindValue h k v = some n) :
    kindValue (h ++ vs) k v = some n := by
  cases k with
  | value => exact hk
  | length => exact lengthOf_extend vs hk
  | view => exact viewLengthOf_extend vs hk
  | strLength => exact hk

theorem termValue_extend {ρ : Env} {h : Heap} (vs : List Val) {t : Term} {n : Int} (ht : termValue ε ρ h t = some n) :
    termValue ε ρ (h ++ vs) t = some n := by
  cases he : t.atEntry
  · rw [termValue_now he] at ht ⊢
    simp only [termAt, Option.bind_eq_some_iff] at ht ⊢
    obtain ⟨v, hv, hk⟩ := ht
    exact ⟨v, readPath_extend vs hv, kindValue_extend vs hk⟩
  · rw [termValue_entry_invariant he]; exact ht

/-- A fact holds at a partial valuation: each of its variables denotes an
integer, and the fact holds of those integers. -/
def FactAt {V : Type} (val : V → Option Int) (F : Linear.Fact V) : Prop :=
  (∀ x ∈ F.vars, (val x).isSome) ∧ F.Holds (fun x => (val x).getD 0)

/-- A fact with its variables renamed, each to one denoting the same, holds
where the fact does. -/
theorem factAt_mapVars {V W : Type} {f : V → Option W} {val : V → Option Int} {val' : W → Option Int}
    {F : Linear.Fact V} {F' : Linear.Fact W} (hm : F.mapVars f = some F')
    (hf : ∀ x ∈ F.vars, ∀ y, f x = some y → val' y = val x) : FactAt val' F' ↔ FactAt val F := by
  have hv : ∀ x ∈ F.vars, ∀ y, f x = some y → (val' y).getD 0 = (val x).getD 0 := by
    intro x hx y hy; rw [hf x hx y hy]
  unfold FactAt
  rw [Linear.Fact.holds_mapVars hm hv]
  constructor
  · rintro ⟨hi, hh⟩
    refine ⟨fun x hx => ?_, hh⟩
    obtain ⟨y, hy, hfy⟩ := Linear.Fact.mapVars_vars_fwd hm x hx
    rw [← hf x hx y hfy]; exact hi y hy
  · rintro ⟨hi, hh⟩
    refine ⟨fun y hy => ?_, hh⟩
    obtain ⟨x, hx, hfx⟩ := Linear.Fact.mapVars_vars hm y hy
    rw [hf x hx y hfx]; exact hi x hx

/-- A fact holds at a valuation agreeing with another on its variables where
it holds at that one. -/
theorem factAt_congr {V : Type} {val val' : V → Option Int} {F : Linear.Fact V}
    (he : ∀ x ∈ F.vars, val' x = val x) (hF : FactAt val F) : FactAt val' F := by
  refine ⟨fun x hx => by rw [he x hx]; exact hF.1 x hx, ?_⟩
  exact (Linear.Fact.holds_congr (v' := fun x => (val' x).getD 0) (fun x hx => by simp only [he x hx])).mp hF.2

/-- A disjunction of linear facts, with each alternative requiring its own
variables to denote integers. -/
inductive LinearClause (V : Type) where
  | atom (fact : Linear.Fact V)
  | either (left right : LinearClause V)
  deriving DecidableEq, Repr, Hashable

namespace LinearClause

def vars : LinearClause V → List V
  | .atom F => F.vars
  | .either A B => A.vars ++ B.vars

def mapVars (f : V → Option W) : LinearClause V → Option (LinearClause W)
  | .atom F => (F.mapVars f).map .atom
  | .either A B => do pure (.either (← A.mapVars f) (← B.mapVars f))

def HoldsAt (val : V → Option Int) : LinearClause V → Prop
  | .atom F => FactAt val F
  | .either A B => A.HoldsAt val ∨ B.HoldsAt val

theorem mapVars_some (f : V → W) : ∀ F : LinearClause V, ∃ G, F.mapVars (some ∘ f) = some G
  | .atom F => by
    obtain ⟨G, hG⟩ := Linear.Fact.mapVars_some f F
    exact ⟨.atom G, by simp [mapVars, hG]⟩
  | .either A B => by
    obtain ⟨A', hA⟩ := mapVars_some f A
    obtain ⟨B', hB⟩ := mapVars_some f B
    exact ⟨.either A' B', by simp [mapVars, hA, hB]⟩

theorem mapVars_vars {f : V → Option W} :
    ∀ {F : LinearClause V} {G : LinearClause W}, F.mapVars f = some G → ∀ y ∈ G.vars, ∃ x ∈ F.vars, f x = some y
  | .atom F, G, hm, y, hy => by
    obtain ⟨G', hG, rfl⟩ := Option.map_eq_some_iff.mp hm
    exact Linear.Fact.mapVars_vars hG y hy
  | .either A B, G, hm, y, hy => by
    simp only [mapVars, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨A', hA, B', hB, rfl⟩ := hm
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨x, hx, h⟩ := mapVars_vars hA y hy; exact ⟨x, List.mem_append_left _ hx, h⟩
    · obtain ⟨x, hx, h⟩ := mapVars_vars hB y hy; exact ⟨x, List.mem_append_right _ hx, h⟩

theorem holdsAt_mapVars {f : V → Option W} {val : V → Option Int} {val' : W → Option Int}
    {F : LinearClause V} {G : LinearClause W} (hm : F.mapVars f = some G)
    (hf : ∀ x ∈ F.vars, ∀ y, f x = some y → val' y = val x) : G.HoldsAt val' ↔ F.HoldsAt val := by
  induction F generalizing G with
  | atom F =>
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.mp hm
    exact factAt_mapVars hG hf
  | either A B ihA ihB =>
    simp only [mapVars, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨A', hA, B', hB, rfl⟩ := hm
    exact or_congr (ihA hA fun x hx => hf x (List.mem_append_left _ hx))
      (ihB hB fun x hx => hf x (List.mem_append_right _ hx))

theorem holdsAt_congr {val val' : V → Option Int} {F : LinearClause V}
    (he : ∀ x ∈ F.vars, val' x = val x) (hF : F.HoldsAt val) : F.HoldsAt val' := by
  induction F with
  | atom F => exact factAt_congr he hF
  | either A B ihA ihB =>
    exact hF.imp (ihA fun x hx => he x (List.mem_append_left _ hx))
      (ihB fun x hx => he x (List.mem_append_right _ hx))

theorem holdsAt_extend {val val' : V → Option Int} {F : LinearClause V}
    (he : ∀ x ∈ F.vars, ∀ n, val x = some n → val' x = some n)
    (hF : F.HoldsAt val) : F.HoldsAt val' := by
  induction F with
  | atom F =>
    refine factAt_congr (fun x hx => ?_) hF
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hF.1 x hx)
    rw [hn]; exact he x hx n hn
  | either A B ihA ihB =>
    exact hF.imp (ihA fun x hx => he x (List.mem_append_left _ hx))
      (ihB fun x hx => he x (List.mem_append_right _ hx))

end LinearClause

/-- A variable of the body of a quantified clause (ARITHMETIC.md,
"Quantified clauses"): the bound index, the element at it, or a term. -/
inductive Bound where
  | index
  | elem
  | offset (delta : Nat)
  | project (kind : Term.Kind) (path : List String)
  | free (t : Term)
  deriving DecidableEq, Repr, Hashable

namespace Bound

/-- The variable with a term's slot renamed, where the map names one. -/
def mapM (f : Nat → Option Nat) : Bound → Option Bound
  | .index => some .index
  | .elem => some .elem
  | .offset d => some (.offset d)
  | .project k p => some (.project k p)
  | .free t => (t.mapM f).map .free

/-- The variable with a term's slot renamed by a total map. -/
def mapTotal (f : Nat → Nat) : Bound → Bound
  | .index => .index
  | .elem => .elem
  | .offset d => .offset d
  | .project k p => .project k p
  | .free t => .free (t.mapM' f)

theorem mapM_total (f : Nat → Nat) : Bound.mapM (some ∘ f) = some ∘ mapTotal f := by
  funext b; cases b with
  | free t => simp only [Function.comp_apply, mapM, mapTotal, Term.mapM_eq]; rfl
  | _ => rfl

/-- The term a variable denotes at an index `i` read of the slot `k` whose
element is the slot `r`'s value. -/
def inst (k r : Nat) : Bound → Term
  | .index => .value k
  | .elem => .value r
  | .offset _ => .value r
  | .project k p => ⟨k, r, p, false⟩
  | .free t => t

/-- The slots of the terms a variable names. -/
def slots : Bound → List Nat
  | .free t => t.slots
  | _ => []

/-- The variable with a term's entry slot translated, where the map names
one (`Term.mapEntry`). -/
def mapEntry (g : Nat → Option Nat) : Bound → Option Bound
  | .free t => (t.mapEntry g).map .free
  | b => some b

end Bound

/-- The location of the store of elements a value holds, which an element
fact and a quantified fact read: an array's store (`Footprints.storeOf`), or,
of a host object owning no store, the location of its `viewElementsKey`, a
typed array's elements (SOURCE-CONTRACTS.md, "Stated library types"). -/
def elementsOf : Val → Option Nat
  | v@(.objAt fs _ _) => match Footprints.storeOf v with
    | some s => some s
    | none => if (fs.lookup hostKey).isSome then fs.lookup viewElementsKey else none
  | v => Footprints.storeOf v

/-- An array's store is the store of elements it holds. -/
theorem elementsOf_store {v : Val} {s : Nat} (h : Footprints.storeOf v = some s) : elementsOf v = some s := by
  cases v <;> simp_all [elementsOf]

/-- The safe integer the element at index `i` of the store elements `ls` is,
where it is present and one. -/
def elementInt (h : Heap) (ls : List (Option Nat)) (i : Nat) : Option Int :=
  match ls[i]? with
  | some (some l) => h[l]?.bind intValue
  | _ => none

/-- Every listed element cell is allocated below `b`. This describes a
particular store view; a later store replacement needs a new proof. -/
def ElementsBelow (b : Nat) (ls : List (Option Nat)) : Prop :=
  ∀ l, some l ∈ ls → l < b

/-- Every listed element cell is at or above the allocation boundary `b`. -/
def ElementsAbove (b : Nat) (ls : List (Option Nat)) : Prop :=
  ∀ l, some l ∈ ls → b ≤ l

/-- Allocation reserves distinct cells, all past the old heap's end.
This is exactly the list returned by `Step.arrAlloc`. -/
theorem elemSlots_above (base n : Nat) : ElementsAbove base (elemSlots base n) := by
  intro l hl
  obtain ⟨i, _, hi⟩ := List.mem_map.mp hl
  simp only [Option.some.injEq] at hi
  omega

/-- A defined element remains defined with the same integer whenever the
location it reads keeps its contents. -/
theorem elementInt_frame {h h' : Heap} {ls : List (Option Nat)} {i : Nat} {z : Int}
    (he : elementInt h ls i = some z)
    (hf : ∀ l v, ls[i]? = some (some l) → h[l]? = some v → h'[l]? = some v) :
    elementInt h' ls i = some z := by
  simp only [elementInt] at he ⊢
  split at he
  · rename_i l hl
    simp only [Option.bind_eq_some_iff] at he ⊢
    obtain ⟨v, hv, hz⟩ := he
    exact ⟨v, hf l v hl hv, hz⟩
  · cases he

/-- What a body variable denotes at the index `i` of the store elements `ls`. -/
def boundValue (ε : EntryState) (ρ : Env) (h : Heap) (ls : List (Option Nat)) (i : Nat) : Bound → Option Int
  | .index => some (i : Int)
  | .elem => elementInt h ls i
  | .offset d => elementInt h ls (i + d)
  | .project k p => match ls[i]? with
    | some (some l) => h[l]?.bind fun v => termValue ε (fun _ => v) h ⟨k, 0, p, false⟩
    | _ => none
  | .free t => termValue ε ρ h t

/-- The region of a value (FOOTPRINTS.md, "Element regions"): a raw store
lists its element cells and has no store cell; an array object has its store
field's location and the cells the store there lists. -/
def RegionOf (h : Heap) (v : Val) (store : Option Nat) (cells : List (Option Nat)) : Prop :=
  (store = none ∧ v = .arr cells) ∨
    ∃ st, store = some st ∧ Footprints.storeOf v = some st ∧ h[st]? = some (.arr cells)

/-- A location of a region: its store cell or a listed element cell. -/
def InRegion (store : Option Nat) (cells : List (Option Nat)) (l : Nat) : Prop :=
  store = some l ∨ some l ∈ cells

/-- The values two paths read hold different array stores, where both hold
one (`!==` of two arrays, ARITHMETIC.md, "Store separation"): for two
arrays, `Footprints.StoreApart` (`PathStoresApart.storeApart`). -/
def PathStoresApart (h : Heap) (x : Val) (p : List String) (y : Val) (q : List String) : Prop :=
  ∃ u w, readPath h x p = some u ∧ readPath h y q = some w ∧
    ∀ s t, Footprints.storeOf u = some s → Footprints.storeOf w = some t → s ≠ t

theorem PathStoresApart.symm {h : Heap} {x y : Val} {p q : List String}
    (ha : PathStoresApart h x p y q) : PathStoresApart h y q x p := by
  obtain ⟨u, w, hu, hw, hne⟩ := ha
  exact ⟨w, u, hw, hu, fun s t hs ht he => hne t s ht hs he.symm⟩

theorem PathStoresApart.extend {h : Heap} {x y : Val} {p q : List String} (vs : List Val)
    (ha : PathStoresApart h x p y q) : PathStoresApart (h ++ vs) x p y q := by
  obtain ⟨u, w, hu, hw, hne⟩ := ha
  exact ⟨u, w, readPath_extend vs hu, readPath_extend vs hw, hne⟩

/-- Two values' regions share no location. -/
def RegionsApart (h : Heap) (u v : Val) : Prop :=
  ∃ sa xs sb ys, RegionOf h u sa xs ∧ RegionOf h v sb ys ∧
    ∀ l, InRegion sa xs l → ∀ m, InRegion sb ys m → l ≠ m

theorem regionOf_extend {h : Heap} {v : Val} {s xs} (vs : List Val) (hr : RegionOf h v s xs) :
    RegionOf (h ++ vs) v s xs := by
  rcases hr with hr | ⟨st, hs, hst, hx⟩
  · exact .inl hr
  · exact .inr ⟨st, hs, hst, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]; exact hx⟩

theorem regionsApart_extend {h : Heap} {u v : Val} (vs : List Val) (ha : RegionsApart h u v) :
    RegionsApart (h ++ vs) u v := by
  obtain ⟨sa, xs, sb, ys, hx, hy, hab⟩ := ha
  exact ⟨sa, xs, sb, ys, regionOf_extend vs hx, regionOf_extend vs hy, hab⟩

theorem regionsApart_symm {h : Heap} {u v : Val} (ha : RegionsApart h u v) : RegionsApart h v u := by
  obtain ⟨sa, xs, sb, ys, hx, hy, hab⟩ := ha
  exact ⟨sb, ys, sa, xs, hy, hx, fun l hl m hm he => hab m hm l hl he.symm⟩

/-- An array object's region has its store cell. -/
theorem regionOf_store {h : Heap} {v : Val} {s xs l} (hr : RegionOf h v s xs)
    (hs : Footprints.storeOf v = some l) : s = some l := by
  rcases hr with ⟨-, rfl⟩ | ⟨st, rfl, hst, -⟩
  · simp [Footprints.storeOf, Footprints.fieldsOf] at hs
  · rw [hst] at hs; exact hs

/-- A region's value determines it, in a given heap. -/
theorem regionOf_unique {h : Heap} {v : Val} {s s' xs xs'} (hr : RegionOf h v s xs) (hr' : RegionOf h v s' xs') :
    s = s' ∧ xs = xs' := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨st, rfl, hst, hx⟩ <;> rcases hr' with ⟨rfl, he⟩ | ⟨st', rfl, hst', hx'⟩
  · cases he; exact ⟨rfl, rfl⟩
  · simp [Footprints.storeOf, Footprints.fieldsOf] at hst'
  · subst he; simp [Footprints.storeOf, Footprints.fieldsOf] at hst
  · rw [hst] at hst'; cases hst'; rw [hx] at hx'; cases hx'; exact ⟨rfl, rfl⟩

/-- An index fact (DESIGN of the guarded write, PROGRAM-TYPING.md, "Writes at
a checked index"): the slot `k` holds a number that is an array index
(`index`); the slot `n` holds the length of the store the array in slot `x`
holds (`length`); the slot `k` holds an array index at most that length
(`bound`), below it where `strict`; the slot `k` holds a safe integer (`int`);
the slot `k` holds the double `2^53`, past the safe integers (`pastSafe`);
the slots of a linear
fact denote integers meeting it (`linear`, ARITHMETIC.md, "Linear
facts"), its terms (`Term`) rooted at slots. `index`, `int` and a linear fact
of slots' values read no heap; the others read the locations their terms or
the array's store field read. A guarded fact (`guarded`, ARITHMETIC.md,
"Guarded clauses") holds where the path `path` from the slot `slot` reads a
value (`readGuard`) that is the tag's, or its body holds. An element fact
(`element`, ARITHMETIC.md, "Quantified clauses") states that the slot
`value` holds what the store of the array in slot `array` holds at the index
the slot `index` holds, below its length: the present element's value, or
`undefined` at a hole. A quantified fact (`every`) states, of the array the
path `path` reads from the slot `slot`, that for every index `i` with
`0 ≤ i < stop` each fact of its body holds, its variables the index, the
element at it (a present safe integer) and terms, each denoting an integer.
A region fact (`apart`, FOOTPRINTS.md, "Element regions") states that the
regions of the values in slots `slot` and `other` share no location
(`RegionsApart`). A store separation (`storeApart`, ARITHMETIC.md, "Store
separation") states that the values the paths `path` and `otherPath` read
from the slots `slot` and `other` hold different array stores
(`PathStoresApart`). -/
inductive IndexFact where
  | index (slot : Nat)
  | length (array length : Nat)
  | bound (array index : Nat) (strict : Bool)
  | int (slot : Nat)
  | pastSafe (slot : Nat)
  | linear (fact : Linear.Fact Term)
  | either (left right : IndexFact)
  | guarded (slot : Nat) (path : List String) (tag : GuardTag) (body : IndexFact)
  | element (value array index : Nat)
  | every (slot : Nat) (path : List String) (stop : Term) (body : List (LinearClause Bound))
  | apart (slot other : Nat)
  | storeApart (slot : Nat) (path : List String) (other : Nat) (otherPath : List String)
  deriving DecidableEq, Repr, Hashable

namespace IndexFact

/-- The slots a fact names. -/
def slots : IndexFact → List Nat
  | .index k => [k]
  | .length x n => [x, n]
  | .bound x k _ => [x, k]
  | .int k => [k]
  | .pastSafe k => [k]
  | .linear F => F.vars.flatMap Term.slots
  | .either A B => A.slots ++ B.slots
  | .guarded s _ _ B => s :: B.slots
  | .element v x k => [v, x, k]
  | .every s _ stop body => s :: stop.slots ++ body.flatMap fun F => F.vars.flatMap Bound.slots
  | .apart a b => [a, b]
  | .storeApart a _ b _ => [a, b]

/-- The slots of the entry environment a fact reads, by its entry terms. -/
def entrySlots : IndexFact → List Nat
  | .linear F => F.vars.flatMap Term.entrySlots
  | .either A B => A.entrySlots ++ B.entrySlots
  | .guarded _ _ _ B => B.entrySlots
  | .every _ _ stop body => stop.entrySlots ++ body.flatMap fun F => F.vars.flatMap fun
      | .free t => t.entrySlots
      | _ => []
  | _ => []

/-- A quantified fact's body with each term's slot renamed, where the map
names every one. -/
def mapBody (f : Nat → Option Nat) : List (LinearClause Bound) → Option (List (LinearClause Bound))
  | [] => some []
  | F :: t => do pure ((← F.mapVars (Bound.mapM f)) :: (← mapBody f t))

theorem mapBody_pairs {f : Nat → Option Nat} :
    ∀ {body body' : List (LinearClause Bound)}, mapBody f body = some body' →
      (∀ F' ∈ body', ∃ F ∈ body, F.mapVars (Bound.mapM f) = some F') ∧
      (∀ F ∈ body, ∃ F' ∈ body', F.mapVars (Bound.mapM f) = some F')
  | [], body', h => by simp only [mapBody, Option.some.injEq] at h; subst h; simp
  | F :: t, body', h => by
    simp only [mapBody, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨G, hG, t', ht, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mapBody_pairs ht
    refine ⟨fun F' hF' => ?_, fun F0 hF0 => ?_⟩
    · rcases List.mem_cons.mp hF' with rfl | hF'
      · exact ⟨F, List.mem_cons_self .., hG⟩
      · obtain ⟨F1, hF1, hm⟩ := h1 F' hF'; exact ⟨F1, List.mem_cons_of_mem _ hF1, hm⟩
    · rcases List.mem_cons.mp hF0 with rfl | hF0
      · exact ⟨G, List.mem_cons_self .., hG⟩
      · obtain ⟨F1, hF1, hm⟩ := h2 F0 hF0; exact ⟨F1, List.mem_cons_of_mem _ hF1, hm⟩

theorem mapBody_some (f : Nat → Nat) : ∀ body : List (LinearClause Bound), ∃ body', mapBody (some ∘ f) body = some body'
  | [] => ⟨[], rfl⟩
  | F :: t => by
    obtain ⟨G, hG⟩ := LinearClause.mapVars_some (Bound.mapTotal f) F
    obtain ⟨t', ht⟩ := mapBody_some f t
    refine ⟨G :: t', ?_⟩
    simp only [mapBody, Bound.mapM_total, hG, ht]
    rfl

/-- The fact with each slot renamed by a partial map, where it maps every slot. -/
def mapM (f : Nat → Option Nat) : IndexFact → Option IndexFact
  | .index k => (f k).map .index
  | .length x n => do pure (.length (← f x) (← f n))
  | .bound x k st => do pure (.bound (← f x) (← f k) st)
  | .int k => (f k).map .int
  | .pastSafe k => (f k).map .pastSafe
  | .linear F => (F.mapVars (Term.mapM f)).map .linear
  | .either A B => do pure (.either (← A.mapM f) (← B.mapM f))
  | .guarded s p t B => do pure (.guarded (← f s) p t (← B.mapM f))
  | .element v x k => do pure (.element (← f v) (← f x) (← f k))
  | .every s p stop body => do
    pure (.every (← f s) p (← stop.mapM f) (← mapBody f body))
  | .apart a b => do pure (.apart (← f a) (← f b))
  | .storeApart a p b q => do pure (.storeApart (← f a) p (← f b) q)

/-- The fact with each slot renamed. -/
def map (f : Nat → Nat) (F : IndexFact) : IndexFact := (F.mapM (some ∘ f)).getD F

def HoldsAt (ε : EntryState) : IndexFact → Env → Heap → Prop
  | .index k, ρ, _ => ∃ b i, ρ k = .num b ∧ indexOfBits b = some i
  | .length x n, ρ, h => ∃ s ls, Footprints.storeOf (ρ x) = some s ∧ h[s]? = some (.arr ls) ∧
      ρ n = .num (bitsOfNat ls.length) ∧ ls.length ≤ maxArrayLength
  | .bound x k st, ρ, h => ∃ s ls b i, Footprints.storeOf (ρ x) = some s ∧ h[s]? = some (.arr ls) ∧
      ρ k = .num b ∧ indexOfBits b = some i ∧ i + (if st then 1 else 0) ≤ ls.length
  | .int k, ρ, _ => (intValue (ρ k)).isSome
  | .pastSafe k, ρ, _ => ρ k = .num SafeIntegers.pastSafeBits
  | .linear F, ρ, h => (∀ t ∈ F.vars, (termValue ε ρ h t).isSome) ∧ F.Holds (termValuation ε ρ h)
  | .either A B, ρ, h => A.HoldsAt ε ρ h ∨ B.HoldsAt ε ρ h
  | .guarded s p t B, ρ, h => ∃ v, readGuard h (ρ s) p = some v ∧ (v = t.val ∨ B.HoldsAt ε ρ h)
  | .element v x k, ρ, h => ∃ s ls b, ∃ i : Nat, elementsOf (ρ x) = some s ∧ h[s]? = some (.arr ls) ∧
      ρ k = .num b ∧ SafeIntegers.SafeInt b (i : Int) ∧ i < ls.length ∧
      (∀ l, ls[i]? = some (some l) → h[l]? = some (ρ v)) ∧ (ls[i]? = some none → ρ v = .undef)
  | .every s p stop body, ρ, h => ∃ w st ls n, readPath h (ρ s) p = some w ∧ elementsOf w = some st ∧
      h[st]? = some (.arr ls) ∧ termValue ε ρ h stop = some n ∧
      ∀ i : Nat, (i : Int) < n → ∀ F ∈ body, F.HoldsAt (boundValue ε ρ h ls i)
  | .apart a b, ρ, h => RegionsApart h (ρ a) (ρ b)
  | .storeApart a p b q, ρ, h => PathStoresApart h (ρ a) p (ρ b) q



/-- A quantified clause is framed by its array path, store, bound and body values. -/
theorem every_frame {s p stop body ρ h h'}
    (he : (IndexFact.every s p stop body).HoldsAt ε ρ h)
    (hp : ∀ w, readPath h (ρ s) p = some w → readPath h' (ρ s) p = some w)
    (hs : ∀ w st ls, readPath h (ρ s) p = some w → elementsOf w = some st →
      h[st]? = some (.arr ls) → h'[st]? = some (.arr ls))
    (hn : ∀ z, termValue ε ρ h stop = some z → termValue ε ρ h' stop = some z)
    (hb : ∀ w st ls, readPath h (ρ s) p = some w → elementsOf w = some st →
      h[st]? = some (.arr ls) → ∀ F ∈ body, ∀ i b, b ∈ F.vars → ∀ z,
      boundValue ε ρ h ls i b = some z → boundValue ε ρ h' ls i b = some z) :
    (IndexFact.every s p stop body).HoldsAt ε ρ h' := by
  obtain ⟨w, st, ls, z, hw, hst, hls, hz, hall⟩ := he
  exact ⟨w, st, ls, z, hp w hw, hst, hs w st ls hw hst hls, hn z hz,
    fun i hi F hF => LinearClause.holdsAt_extend (hb w st ls hw hst hls F hF i) (hall i hi F hF)⟩


theorem holdsAt_mapM {F F' : IndexFact} {f : Nat → Option Nat} {ρ ρ' : Env} {h : Heap}
    (hm : F.mapM f = some F') (hf : ∀ s ∈ F.slots, ∀ t, f s = some t → ρ' t = ρ s) :
    F'.HoldsAt ε ρ' h ↔ F.HoldsAt ε ρ h := by
  induction F generalizing F' with
  | either A B ihA ihB =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨A', hA, B', hB, rfl⟩ := hm
    exact or_congr (ihA hA (fun x hx y hy => hf x (by simp [slots, hx]) y hy))
      (ihB hB (fun x hx y hy => hf x (by simp [slots, hx]) y hy))
  | apart a b =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨a', ha, b', hb, rfl⟩ := hm
    simp only [HoldsAt, hf a (by simp [slots]) a' ha, hf b (by simp [slots]) b' hb]
  | storeApart a p b q =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨a', ha, b', hb, rfl⟩ := hm
    simp only [HoldsAt, hf a (by simp [slots]) a' ha, hf b (by simp [slots]) b' hb]
  | guarded s p t B ih =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨s', hs, B', hB, rfl⟩ := hm
    have hB' := ih hB (fun x hx y hy => hf x (by simp [slots, hx]) y hy)
    simp only [HoldsAt, hf s (by simp [slots]) s' hs, hB']
  | element v x k =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨v', hv, x', hx, k', hk, rfl⟩ := hm
    simp only [HoldsAt, hf v (by simp [slots]) v' hv, hf x (by simp [slots]) x' hx, hf k (by simp [slots]) k' hk]
  | every s p stop body =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨s', hs, stop', hstop, body', hbody, rfl⟩ := hm
    have hs' := hf s (by simp [slots]) s' hs
    have hst : termValue ε ρ' h stop' = termValue ε ρ h stop :=
      termValue_mapM hstop fun he j hj => hf stop.slot (by simp [slots, Term.slots, he]) j hj
    obtain ⟨hb1, hb2⟩ := mapBody_pairs hbody
    have hval : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body, ∀ F', F.mapVars (Bound.mapM f) = some F' →
        (F'.HoldsAt (boundValue ε ρ' h ls i) ↔ F.HoldsAt (boundValue ε ρ h ls i)) := by
      intro ls i F hF F' hm
      refine LinearClause.holdsAt_mapVars hm fun x hx y hy => ?_
      cases x with
      | index => cases hy; rfl
      | elem => cases hy; rfl
      | offset _ => cases hy; rfl
      | project _ _ => cases hy; rfl
      | free t =>
        simp only [Bound.mapM, Option.map_eq_some_iff] at hy
        obtain ⟨t', ht', rfl⟩ := hy
        simp only [boundValue]
        refine termValue_mapM ht' fun he j hj => hf t.slot ?_ j hj
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨F, hF,
          List.mem_flatMap.mpr ⟨.free t, hx, by simp [Bound.slots, Term.slots, he]⟩⟩))
    simp only [HoldsAt, hs', hst]
    constructor
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      refine ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F hF => ?_⟩
      obtain ⟨F', hF', hm⟩ := hb2 F hF
      exact (hval ls i F hF F' hm).mp (hall i hi F' hF')
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      refine ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F' hF' => ?_⟩
      obtain ⟨F, hF, hm⟩ := hb1 F' hF'
      exact (hval ls i F hF F' hm).mpr (hall i hi F hF)
  | index k =>
    simp only [mapM, Option.map_eq_some_iff] at hm
    obtain ⟨t, ht, rfl⟩ := hm
    simp only [HoldsAt, hf k (by simp [slots]) t ht]
  | length x n =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨x', hx, n', hn, rfl⟩ := hm
    simp only [HoldsAt, hf x (by simp [slots]) x' hx, hf n (by simp [slots]) n' hn]
  | bound x k st =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨x', hx, k', hk, rfl⟩ := hm
    simp only [HoldsAt, hf x (by simp [slots]) x' hx, hf k (by simp [slots]) k' hk]
  | int k =>
    simp only [mapM, Option.map_eq_some_iff] at hm
    obtain ⟨t, ht, rfl⟩ := hm
    simp only [HoldsAt, hf k (by simp [slots]) t ht]
  | pastSafe k =>
    simp only [mapM, Option.map_eq_some_iff] at hm
    obtain ⟨t, ht, rfl⟩ := hm
    simp only [HoldsAt, hf k (by simp [slots]) t ht]
  | linear G =>
    simp only [mapM, Option.map_eq_some_iff] at hm
    obtain ⟨G', hG, rfl⟩ := hm
    simp only [HoldsAt]
    -- A renamed term denotes what its source denotes: its slot holds the same value.
    have hterm : ∀ x ∈ G.vars, ∀ y, x.mapM f = some y → termValue ε ρ' h y = termValue ε ρ h x :=
      fun x hx y hy => termValue_mapM hy fun he j hj =>
        hf x.slot (List.mem_flatMap.mpr ⟨x, hx, by simp [Term.slots, he]⟩) j hj
    have hv : ∀ x ∈ G.vars, ∀ y, x.mapM f = some y → termValuation ε ρ' h y = termValuation ε ρ h x := by
      intro x hx y hy; simp only [termValuation, hterm x hx y hy]
    rw [Linear.Fact.holds_mapVars hG hv]
    constructor
    · rintro ⟨hi, hh⟩
      refine ⟨fun x hx => ?_, hh⟩
      obtain ⟨y, hy, hfy⟩ := Linear.Fact.mapVars_vars_fwd hG x hx
      rw [← hterm x hx y hfy]; exact hi y hy
    · rintro ⟨hi, hh⟩
      refine ⟨fun y hy => ?_, hh⟩
      obtain ⟨x, hx, hfx⟩ := Linear.Fact.mapVars_vars hG y hy
      rw [hterm x hx y hfx]; exact hi x hx

/-- A linear fact with its terms restated, each by a term denoting the same,
holds where the fact does. -/
theorem holdsAt_linear_mapVars {F F' : Linear.Fact Term} {f : Term → Option Term} {ρ : Env} {h : Heap}
    (hm : F.mapVars f = some F') (hf : ∀ x ∈ F.vars, ∀ y, f x = some y → termValue ε ρ h y = termValue ε ρ h x) :
    (linear F').HoldsAt ε ρ h ↔ (linear F).HoldsAt ε ρ h := by
  have hv : ∀ x ∈ F.vars, ∀ y, f x = some y → termValuation ε ρ h y = termValuation ε ρ h x := by
    intro x hx y hy; simp only [termValuation, hf x hx y hy]
  simp only [HoldsAt]
  rw [Linear.Fact.holds_mapVars hm hv]
  constructor
  · rintro ⟨hi, hh⟩
    refine ⟨fun x hx => ?_, hh⟩
    obtain ⟨y, hy, hfy⟩ := Linear.Fact.mapVars_vars_fwd hm x hx
    rw [← hf x hx y hfy]; exact hi y hy
  · rintro ⟨hi, hh⟩
    refine ⟨fun y hy => ?_, hh⟩
    obtain ⟨x, hx, hfx⟩ := Linear.Fact.mapVars_vars hm y hy
    rw [hf x hx y hfx]; exact hi x hx

/-- A term read at the current state: `old(t)` as `t`. -/
def _root_.Verification.HeapKnowledge.Term.toNow (t : Term) : Term := { t with atEntry := false }

/-- At the entry state, `old(t)` denotes what `t` does. -/
theorem termValue_toNow {ρ : Env} {h : Heap} (hρ : ε.env = ρ) (hh : ε.heap = h) (t : Term) :
    termValue ε ρ h t.toNow = termValue ε ρ h t := by
  cases he : t.atEntry
  · obtain ⟨k, s, p, a⟩ := t; simp only at he; subst he; rfl
  · rw [termValue_now rfl, termValue_atEntry he]
    simp only [Term.toNow, termAt, hρ, hh]

/-- A body variable read at the current state. -/
def _root_.Verification.HeapKnowledge.Bound.toNow : Bound → Bound
  | .free t => .free t.toNow
  | b => b

/-- The fact read at the entry state itself: each entry term `old(t)`
restated as `t` (the current term at the same slot), in every fact form
whose terms are terms, a quantified fact's bound and body included. -/
def toNow : IndexFact → IndexFact
  | .linear F => .linear ((F.mapVars fun t => some t.toNow).getD F)
  | .either A B => .either A.toNow B.toNow
  | .guarded s p t B => .guarded s p t B.toNow
  | .every s p stop body => .every s p stop.toNow (body.map fun C => (C.mapVars (some ∘ Bound.toNow)).getD C)
  | F => F

/-- **At the entry state, `old(t)` is `t`**: where the current environment
and heap are the entry state's, a fact holds exactly where its restatement
without entry terms does. -/
theorem holdsAt_toNow {F : IndexFact} (hρ : ε.env = ρ) (hh : ε.heap = h) :
    F.toNow.HoldsAt ε ρ h ↔ F.HoldsAt ε ρ h := by
  induction F with
  | linear G =>
    obtain ⟨G', hG⟩ := Linear.Fact.mapVars_some Term.toNow G
    have hG' : G.mapVars (fun t => some t.toNow) = some G' := hG
    simp only [toNow, hG', Option.getD_some]
    exact holdsAt_linear_mapVars hG' fun x _ y hy => by cases hy; exact termValue_toNow hρ hh x
  | either A B ihA ihB => exact or_congr ihA ihB
  | guarded s p t B ih => simp only [toNow, HoldsAt, ih]
  | every s p stop body =>
    have hb : ∀ (ls : List (Option Nat)) (i : Nat) (C : LinearClause Bound),
        ((C.mapVars (some ∘ Bound.toNow)).getD C).HoldsAt (boundValue ε ρ h ls i) ↔ C.HoldsAt (boundValue ε ρ h ls i) := by
      intro ls i C
      obtain ⟨C', hC⟩ := LinearClause.mapVars_some Bound.toNow C
      rw [hC, Option.getD_some]
      refine LinearClause.holdsAt_mapVars hC fun x _ y hy => ?_
      cases hy
      cases x with
      | free t => exact termValue_toNow hρ hh t
      | _ => rfl
    simp only [toNow, HoldsAt, termValue_toNow hρ hh stop]
    constructor
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      exact ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi C hC => (hb ls i C).mp (hall i hi _ (List.mem_map_of_mem hC))⟩
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      refine ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi C' hC' => ?_⟩
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
      exact (hb ls i C).mpr (hall i hi C hC)
  | _ => exact Iff.rfl

/-- A fact read at the current state names no entry term. -/
theorem entrySlots_toNow (F : IndexFact) : F.toNow.entrySlots = [] := by
  induction F with
  | linear G =>
    obtain ⟨G', hG⟩ := Linear.Fact.mapVars_some Term.toNow G
    have hG' : G.mapVars (fun t => some t.toNow) = some G' := hG
    simp only [toNow, hG', Option.getD_some, entrySlots, List.flatMap_eq_nil_iff]
    intro y hy
    obtain ⟨x, -, hx⟩ := Linear.Fact.mapVars_vars hG' y hy
    cases hx
    simp [Term.entrySlots, Term.toNow]
  | either A B ihA ihB => simp [toNow, entrySlots, ihA, ihB]
  | guarded s p t B ih => simp [toNow, entrySlots, ih]
  | every s p stop body =>
    simp only [toNow, entrySlots, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
    refine ⟨by simp [Term.entrySlots, Term.toNow], fun C' hC' => ?_⟩
    obtain ⟨C, -, rfl⟩ := List.mem_map.mp hC'
    obtain ⟨D, hD⟩ := LinearClause.mapVars_some Bound.toNow C
    rw [hD, Option.getD_some]
    intro b hb
    obtain ⟨x, -, hx⟩ := LinearClause.mapVars_vars hD b hb
    cases hx
    cases x <;> simp [Bound.toNow, Term.entrySlots, Term.toNow]
  | _ => rfl

/-- The entry terms a fact names. -/
def entryTerms : IndexFact → List Term
  | .linear F => F.vars.filter (·.atEntry)
  | .either A B => A.entryTerms ++ B.entryTerms
  | .guarded _ _ _ B => B.entryTerms
  | .every _ _ stop body => (if stop.atEntry then [stop] else []) ++ body.flatMap fun C => C.vars.filterMap fun
      | .free t => if t.atEntry then some t else none
      | _ => none
  | _ => []

/-- The identity `t = old(t)` of an entry term `old(t)`: the linear facts
`t - old(t) ≤ 0` and `old(t) - t ≤ 0`. -/
def identity (t : Term) : List IndexFact :=
  [.linear (.le [(t.toNow, 1), (t, -1)] 0), .linear (.le [(t, 1), (t.toNow, -1)] 0)]

/-- **At the entry state, `old(t)` and `t` denote the same wherever `t` is
defined** (proved, by `termValue_toNow`, the term form of `holdsAt_toNow`):
where the current environment and heap are the entry state's and `t`
denotes an integer, each fact of its identity holds. -/
theorem identity_holds {t : Term} {ρ : Env} {h : Heap} (hρ : ε.env = ρ) (hh : ε.heap = h)
    (hd : (termValue ε ρ h t.toNow).isSome) : ∀ F ∈ identity t, F.HoldsAt ε ρ h := by
  have he : termValue ε ρ h t = termValue ε ρ h t.toNow := (termValue_toNow hρ hh t).symm
  have hd' : (termValue ε ρ h t).isSome := he ▸ hd
  intro F hF
  simp only [identity, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;>
  · refine ⟨fun x hx => ?_, ?_⟩
    · simp only [Linear.Fact.vars, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl <;> assumption
    · simp only [Linear.Fact.Holds, Linear.Form.eval, termValuation, he]
      omega

/-- A total renaming renames every fact. -/
theorem mapM_total (f : Nat → Nat) : ∀ F : IndexFact, ∃ G, F.mapM (some ∘ f) = some G
  | .index k => ⟨_, rfl⟩
  | .length x n => ⟨_, rfl⟩
  | .bound x k st => ⟨_, rfl⟩
  | .int k => ⟨_, rfl⟩
  | .pastSafe k => ⟨_, rfl⟩
  | .linear G => by
    obtain ⟨G', h⟩ := Linear.Fact.mapVars_some (Term.mapM' f) G
    exact ⟨.linear G', by simp only [mapM, Term.mapM_eq, h, Option.map_some]⟩
  | .either A B => by
    obtain ⟨A', hA⟩ := mapM_total f A
    obtain ⟨B', hB⟩ := mapM_total f B
    exact ⟨.either A' B', by simp [mapM, hA, hB]⟩
  | .guarded s p t B => by
    obtain ⟨B', hB⟩ := mapM_total f B
    exact ⟨.guarded (f s) p t B', by simp [mapM, hB]⟩
  | .element v x k => ⟨_, rfl⟩
  | .every s p stop body => by
    obtain ⟨body', hb⟩ := mapBody_some f body
    have hst : Term.mapM (some ∘ f) stop = some (Term.mapM' f stop) := congrFun (Term.mapM_eq f) stop
    exact ⟨.every (f s) p (Term.mapM' f stop) body', by simp only [mapM, hb, hst]; rfl⟩
  | .apart a b => ⟨_, rfl⟩
  | .storeApart a p b q => ⟨_, rfl⟩

/-- A fact reads its slots' values alone. -/
theorem holdsAt_map {F : IndexFact} {f : Nat → Nat} {ρ ρ' : Env} {h : Heap}
    (hf : ∀ s ∈ F.slots, ρ' (f s) = ρ s) : (F.map f).HoldsAt ε ρ' h ↔ F.HoldsAt ε ρ h := by
  obtain ⟨G, hG⟩ := mapM_total f F
  simp only [map, hG, Option.getD_some]
  exact holdsAt_mapM hG (fun s hs t ht => by cases ht; exact hf s hs)

/-- A heap extension preserves a fact: the store lies in the old heap. -/
theorem holdsAt_extend {F : IndexFact} {ρ : Env} {h : Heap} (vs : List Val) (hF : F.HoldsAt ε ρ h) :
    F.HoldsAt ε ρ (h ++ vs) := by
  induction F with
  | either A B ihA ihB => exact hF.imp ihA ihB
  | apart a b => exact regionsApart_extend vs hF
  | storeApart a p b q => exact PathStoresApart.extend vs hF
  | guarded s p t B ih =>
    obtain ⟨v, hv, hor⟩ := hF
    exact ⟨v, readGuard_extend vs hv, hor.imp id ih⟩
  | element v x k =>
    obtain ⟨s, ls, b, i, hs, hl, hk, hi, hlt, hp, hh⟩ := hF
    have hl' : (h ++ vs)[s]? = some (.arr ls) := by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl
    refine ⟨s, ls, b, i, hs, hl', hk, hi, hlt, fun l hli => ?_, hh⟩
    have := hp l hli
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp this).1]; exact this
  | every s p stop body =>
    obtain ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩ := hF
    refine ⟨w, st, ls, n, readPath_extend vs hw, hsto,
      by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hls).1]; exact hls,
      termValue_extend vs hn, fun i hi F hF => ?_⟩
    have hA := hall i hi F hF
    refine LinearClause.holdsAt_extend (fun x hx m hm => ?_) hA
    cases x with
    | index => exact hm
    | elem | offset _ =>
      simp only [boundValue, elementInt] at hm ⊢
      split at hm
      · rename_i l _
        simp only [Option.bind_eq_some_iff] at hm ⊢
        obtain ⟨u, hu, hi'⟩ := hm
        exact ⟨u, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hu).1]; exact hu, hi'⟩
      · cases hm
    | project k p =>
      simp only [boundValue] at hm ⊢
      split at hm
      · rename_i l _
        obtain ⟨v, hv, ht⟩ := Option.bind_eq_some_iff.mp hm
        exact Option.bind_eq_some_iff.mpr ⟨v, by
          rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv,
          termValue_extend vs ht⟩
      · cases hm
    | free t => exact termValue_extend (ε := ε) vs hm
  | index k => exact hF
  | length x n =>
    obtain ⟨s, ls, hs, hl, hn⟩ := hF
    exact ⟨s, ls, hs, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl, hn⟩
  | bound x k st =>
    obtain ⟨s, ls, b, i, hs, hl, hk, hi, hle⟩ := hF
    exact ⟨s, ls, b, i, hs, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl,
      hk, hi, hle⟩
  | int k => exact hF
  | pastSafe k => exact hF
  | linear G =>
    obtain ⟨hi, hh⟩ := hF
    have heq : ∀ t ∈ G.vars, termValue ε ρ (h ++ vs) t = termValue ε ρ h t := by
      intro t ht
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hi t ht)
      rw [hn, termValue_extend vs hn]
    refine ⟨fun t ht => by rw [heq t ht]; exact hi t ht, ?_⟩
    rw [Linear.Fact.holds_congr (v' := termValuation ε ρ h) (fun t ht => by simp only [termValuation, heq t ht])]
    exact hh

/-- A fact reads the values of the slots it names alone. -/
theorem holdsAt_congr {F : IndexFact} {ρ ρ' : Env} {h : Heap} (hs : ∀ s ∈ F.slots, ρ s = ρ' s) :
    F.HoldsAt ε ρ h ↔ F.HoldsAt ε ρ' h := by
  induction F with
  | either A B ihA ihB =>
    exact or_congr (ihA (fun x hx => hs x (by simp [slots, hx])))
      (ihB (fun x hx => hs x (by simp [slots, hx])))
  | apart a b =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2]
  | storeApart a p b q =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2]
  | guarded s p t B ih =>
    simp only [slots, List.mem_cons, forall_eq_or_imp] at hs
    simp only [HoldsAt, hs.1, ih hs.2]
  | element v x k =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2.1, hs.2.2]
  | every s p stop body =>
    have h0 : ρ s = ρ' s := hs s (by simp [slots])
    have hst : termValue ε ρ h stop = termValue ε ρ' h stop :=
      termValue_congr fun he => hs stop.slot (by simp [slots, Term.slots, he])
    have hb : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body,
        ∀ x ∈ F.vars, boundValue ε ρ' h ls i x = boundValue ε ρ h ls i x := by
      intro ls i F hF x hx
      cases x with
      | index => rfl
      | elem => rfl
      | offset _ => rfl
      | project _ _ => rfl
      | free t =>
        simp only [boundValue]
        exact (termValue_congr fun he => hs t.slot (List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨F, hF, List.mem_flatMap.mpr ⟨.free t, hx, by simp [Bound.slots, Term.slots, he]⟩⟩)))).symm
    simp only [HoldsAt, h0, hst]
    constructor
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      exact ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F hF => LinearClause.holdsAt_congr (hb ls i F hF) (hall i hi F hF)⟩
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      exact ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F hF =>
        LinearClause.holdsAt_congr (fun x hx => (hb ls i F hF x hx).symm) (hall i hi F hF)⟩
  | index k => simp only [slots, List.mem_singleton, forall_eq] at hs; simp only [HoldsAt, hs]
  | length x n =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2]
  | bound x k st =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2]
  | int k => simp only [slots, List.mem_singleton, forall_eq] at hs; simp only [HoldsAt, hs]
  | pastSafe k => simp only [slots, List.mem_singleton, forall_eq] at hs; simp only [HoldsAt, hs]
  | linear G =>
    simp only [slots] at hs
    simp only [HoldsAt]
    have heq : ∀ t ∈ G.vars, termValue ε ρ h t = termValue ε ρ' h t := fun t ht =>
      termValue_congr fun he => hs t.slot (List.mem_flatMap.mpr ⟨t, ht, by simp [Term.slots, he]⟩)
    rw [Linear.Fact.holds_congr (v' := termValuation ε ρ' h) (fun t ht => by simp only [termValuation, heq t ht])]
    exact ⟨fun ⟨a, b⟩ => ⟨fun t hm => heq t hm ▸ a t hm, b⟩, fun ⟨a, b⟩ => ⟨fun t hm => (heq t hm).symm ▸ a t hm, b⟩⟩

/-- **A fact reads the entry state at its entry slots only**: it holds at
one entry state where it holds at another with the same heap and the same
values at its entry slots. -/
theorem holdsAt_congr_entry {F : IndexFact} {ε' : EntryState} {ρ : Env} {h : Heap} (hh : ε.heap = ε'.heap)
    (hs : ∀ s ∈ F.entrySlots, ε.env s = ε'.env s) : F.HoldsAt ε ρ h ↔ F.HoldsAt ε' ρ h := by
  induction F with
  | either A B ihA ihB =>
    exact or_congr (ihA fun s h => hs s (List.mem_append_left _ h)) (ihB fun s h => hs s (List.mem_append_right _ h))
  | guarded s p t B ih => simp only [HoldsAt, ih hs]
  | linear G =>
    have heq : ∀ t ∈ G.vars, termValue ε ρ h t = termValue ε' ρ h t := fun t ht =>
      termValue_congr_entry hh fun he => hs t.slot (List.mem_flatMap.mpr ⟨t, ht, by simp [Term.entrySlots, he]⟩)
    simp only [HoldsAt]
    rw [Linear.Fact.holds_congr (v' := termValuation ε' ρ h) (fun t ht => by simp only [termValuation, heq t ht])]
    exact ⟨fun ⟨a, b⟩ => ⟨fun t hm => heq t hm ▸ a t hm, b⟩, fun ⟨a, b⟩ => ⟨fun t hm => (heq t hm).symm ▸ a t hm, b⟩⟩
  | every s p stop body =>
    have hst : termValue ε ρ h stop = termValue ε' ρ h stop :=
      termValue_congr_entry hh fun he => hs stop.slot (List.mem_append_left _ (by simp [Term.entrySlots, he]))
    have hb : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body,
        ∀ x ∈ F.vars, boundValue ε' ρ h ls i x = boundValue ε ρ h ls i x := by
      intro ls i F hF x hx
      cases x with
      | free t =>
        simp only [boundValue]
        exact (termValue_congr_entry hh fun he => hs t.slot (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨F, hF, List.mem_flatMap.mpr ⟨.free t, hx, by simp [Term.entrySlots, he]⟩⟩))).symm
      | _ => rfl
    simp only [HoldsAt, hst]
    constructor
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      exact ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F hF => LinearClause.holdsAt_congr (hb ls i F hF) (hall i hi F hF)⟩
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      exact ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F hF =>
        LinearClause.holdsAt_congr (fun x hx => (hb ls i F hF x hx).symm) (hall i hi F hF)⟩
  | _ => exact Iff.rfl

/-- **A fact with no entry term reads no entry state.** -/
theorem holdsAt_entry {F : IndexFact} (hF : F.entrySlots = []) (ε' : EntryState) {ρ : Env} {h : Heap} :
    F.HoldsAt ε ρ h ↔ F.HoldsAt ε' ρ h := by
  induction F with
  | either A B ihA ihB =>
    simp only [entrySlots, List.append_eq_nil_iff] at hF
    exact or_congr (ihA hF.1) (ihB hF.2)
  | guarded s p t B ih => simp only [HoldsAt, ih hF]
  | linear G =>
    have hn : ∀ t ∈ G.vars, t.atEntry = false := fun t ht => by
      cases he : t.atEntry
      · rfl
      · have : t.slot ∈ (linear G).entrySlots := List.mem_flatMap.mpr ⟨t, ht, by simp [Term.entrySlots, he]⟩
        rw [hF] at this; cases this
    have heq : ∀ t ∈ G.vars, termValue ε ρ h t = termValue ε' ρ h t := fun t ht => by
      rw [termValue_now (hn t ht), termValue_now (hn t ht)]
    simp only [HoldsAt]
    rw [Linear.Fact.holds_congr (v' := termValuation ε' ρ h) (fun t ht => by simp only [termValuation, heq t ht])]
    exact ⟨fun ⟨a, b⟩ => ⟨fun t hm => heq t hm ▸ a t hm, b⟩, fun ⟨a, b⟩ => ⟨fun t hm => (heq t hm).symm ▸ a t hm, b⟩⟩
  | every s p stop body =>
    simp only [entrySlots, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at hF
    have hst : termValue ε ρ h stop = termValue ε' ρ h stop := by
      cases he : stop.atEntry
      · rw [termValue_now he, termValue_now he]
      · have := hF.1; simp [Term.entrySlots, he] at this
    have hb : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body,
        ∀ x ∈ F.vars, boundValue ε' ρ h ls i x = boundValue ε ρ h ls i x := by
      intro ls i F hF' x hx
      cases x with
      | free t =>
        simp only [boundValue]
        cases he : t.atEntry
        · rw [termValue_now he, termValue_now he]
        · have := hF.2 F hF' (.free t) hx; simp [Term.entrySlots, he] at this
      | _ => rfl
    simp only [HoldsAt, hst]
    constructor
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      exact ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F hF => LinearClause.holdsAt_congr (hb ls i F hF) (hall i hi F hF)⟩
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      exact ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F hF =>
        LinearClause.holdsAt_congr (fun x hx => (hb ls i F hF x hx).symm) (hall i hi F hF)⟩
  | _ => exact Iff.rfl

/-- A quantified fact's body with each variable translated by `m`, where it
translates every one. -/
def mapBodyWith (m : Bound → Option Bound) : List (LinearClause Bound) → Option (List (LinearClause Bound))
  | [] => some []
  | F :: t => do pure ((← F.mapVars m) :: (← mapBodyWith m t))

theorem mapBodyWith_pairs {m : Bound → Option Bound} :
    ∀ {body body' : List (LinearClause Bound)}, mapBodyWith m body = some body' →
      (∀ F' ∈ body', ∃ F ∈ body, F.mapVars m = some F') ∧
      (∀ F ∈ body, ∃ F' ∈ body', F.mapVars m = some F')
  | [], body', h => by simp only [mapBodyWith, Option.some.injEq] at h; subst h; simp
  | F :: t, body', h => by
    simp only [mapBodyWith, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨G, hG, t', ht, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mapBodyWith_pairs ht
    refine ⟨fun F' hF' => ?_, fun F0 hF0 => ?_⟩
    · rcases List.mem_cons.mp hF' with rfl | hF'
      · exact ⟨F, List.mem_cons_self .., hG⟩
      · obtain ⟨F1, hF1, hm⟩ := h1 F' hF'; exact ⟨F1, List.mem_cons_of_mem _ hF1, hm⟩
    · rcases List.mem_cons.mp hF0 with rfl | hF0
      · exact ⟨G, List.mem_cons_self .., hG⟩
      · obtain ⟨F1, hF1, hm⟩ := h2 F0 hF0; exact ⟨F1, List.mem_cons_of_mem _ hF1, hm⟩

/-- **The fact with each entry slot translated** to another entry frame,
where the map names every one (`Term.mapEntry`): its current slots are left
as they are. With `mapM` it makes a change of frame (`reframe`). -/
def mapEntry (g : Nat → Option Nat) : IndexFact → Option IndexFact
  | .linear F => (F.mapVars (Term.mapEntry g)).map .linear
  | .either A B => do pure (.either (← A.mapEntry g) (← B.mapEntry g))
  | .guarded s p t B => do pure (.guarded s p t (← B.mapEntry g))
  | .every s p stop body => do pure (.every s p (← stop.mapEntry g) (← mapBodyWith (Bound.mapEntry g) body))
  | F => some F

/-- **A fact with its entry slots translated holds at the translated entry
state where it held at the source one**: each translated entry slot holds
its source slot's value, and the entry heaps agree. -/
theorem holdsAt_mapEntry {F F' : IndexFact} {g : Nat → Option Nat} {ε' : EntryState} {ρ : Env} {h : Heap}
    (hm : F.mapEntry g = some F') (hh : ε'.heap = ε.heap)
    (hg : ∀ s ∈ F.entrySlots, ∀ j, g s = some j → ε'.env j = ε.env s) :
    F'.HoldsAt ε' ρ h ↔ F.HoldsAt ε ρ h := by
  induction F generalizing F' with
  | either A B ihA ihB =>
    simp only [mapEntry, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨A', hA, B', hB, rfl⟩ := hm
    exact or_congr (ihA hA fun s hs => hg s (List.mem_append_left _ hs))
      (ihB hB fun s hs => hg s (List.mem_append_right _ hs))
  | guarded s p t B ih =>
    simp only [mapEntry, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨B', hB, rfl⟩ := hm
    simp only [HoldsAt, ih hB hg]
  | linear G =>
    simp only [mapEntry, Option.map_eq_some_iff] at hm
    obtain ⟨G', hG, rfl⟩ := hm
    have hterm : ∀ x ∈ G.vars, ∀ y, x.mapEntry g = some y → termValue ε' ρ h y = termValue ε ρ h x :=
      fun x hx y hy => termValue_mapEntry hy hh fun he j hj =>
        hg x.slot (List.mem_flatMap.mpr ⟨x, hx, by simp [Term.entrySlots, he]⟩) j hj
    have hv : ∀ x ∈ G.vars, ∀ y, x.mapEntry g = some y → termValuation ε' ρ h y = termValuation ε ρ h x := by
      intro x hx y hy; simp only [termValuation, hterm x hx y hy]
    simp only [HoldsAt]
    rw [Linear.Fact.holds_mapVars hG hv]
    constructor
    · rintro ⟨hi, hh'⟩
      refine ⟨fun x hx => ?_, hh'⟩
      obtain ⟨y, hy, hfy⟩ := Linear.Fact.mapVars_vars_fwd hG x hx
      rw [← hterm x hx y hfy]; exact hi y hy
    · rintro ⟨hi, hh'⟩
      refine ⟨fun y hy => ?_, hh'⟩
      obtain ⟨x, hx, hfx⟩ := Linear.Fact.mapVars_vars hG y hy
      rw [hterm x hx y hfx]; exact hi x hx
  | every s p stop body =>
    simp only [mapEntry, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨stop', hstop, body', hbody, rfl⟩ := hm
    have hst : termValue ε' ρ h stop' = termValue ε ρ h stop :=
      termValue_mapEntry hstop hh fun he j hj => hg stop.slot (List.mem_append_left _ (by simp [Term.entrySlots, he])) j hj
    obtain ⟨hb1, hb2⟩ := mapBodyWith_pairs hbody
    have hval : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body, ∀ F', F.mapVars (Bound.mapEntry g) = some F' →
        (F'.HoldsAt (boundValue ε' ρ h ls i) ↔ F.HoldsAt (boundValue ε ρ h ls i)) := by
      intro ls i F hF F' hm
      refine LinearClause.holdsAt_mapVars hm fun x hx y hy => ?_
      cases x with
      | free t =>
        simp only [Bound.mapEntry, Option.map_eq_some_iff] at hy
        obtain ⟨t', ht', rfl⟩ := hy
        simp only [boundValue]
        refine termValue_mapEntry ht' hh fun he j hj => hg t.slot ?_ j hj
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨F, hF,
          List.mem_flatMap.mpr ⟨.free t, hx, by simp [Term.entrySlots, he]⟩⟩)
      | project k q =>
        cases hy; simp only [boundValue]
        split
        · rename_i l _
          cases h[l]? with
          | none => rfl
          | some v => simp only [Option.bind_some]; rw [termValue_now rfl, termValue_now rfl]
        · rfl
      | _ => cases hy; rfl
    simp only [HoldsAt, hst]
    constructor
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      refine ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F hF => ?_⟩
      obtain ⟨F', hF', hm⟩ := hb2 F hF
      exact (hval ls i F hF F' hm).mp (hall i hi F' hF')
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      refine ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F' hF' => ?_⟩
      obtain ⟨F, hF, hm⟩ := hb1 F' hF'
      exact (hval ls i F hF F' hm).mpr (hall i hi F hF)
  | index k => cases hm; exact Iff.rfl
  | length x n => cases hm; exact Iff.rfl
  | bound x k st => cases hm; exact Iff.rfl
  | int k => cases hm; exact Iff.rfl
  | pastSafe k => cases hm; exact Iff.rfl
  | element v x k => cases hm; exact Iff.rfl
  | apart a b => cases hm; exact Iff.rfl
  | storeApart a p b q => cases hm; exact Iff.rfl

/-- **A change of frame**: the fact with its current slots renamed by `f`
(`mapM`) and its entry slots translated by `g` (`mapEntry`), each by its own
map, where both name every slot. -/
def reframe (f g : Nat → Option Nat) (F : IndexFact) : Option IndexFact :=
  (F.mapM f).bind (·.mapEntry g)

/-- **A fact read in another frame** (proved): where `reframe f g` translates
`F` to `F'`, each current slot `s` renamed to `t` holds at `ρ'` what `s`
holds at `ρ`, each entry slot translated likewise holds at `ε'` what it holds
at `ε`, and the entry heaps agree, `F'` holds at `ε'`, `ρ'` exactly where `F`
holds at `ε`, `ρ`. -/
theorem holdsAt_reframe {F F' : IndexFact} {f g : Nat → Option Nat} {ε' : EntryState} {ρ ρ' : Env} {h : Heap}
    (hm : F.reframe f g = some F') (hf : ∀ s ∈ F.slots, ∀ t, f s = some t → ρ' t = ρ s)
    (hh : ε'.heap = ε.heap) (hg : ∀ s j, g s = some j → ε'.env j = ε.env s) :
    F'.HoldsAt ε' ρ' h ↔ F.HoldsAt ε ρ h := by
  obtain ⟨G, hG, hE⟩ := Option.bind_eq_some_iff.mp hm
  rw [holdsAt_mapEntry hE hh (fun s _ => hg s)]
  exact holdsAt_mapM hG hf

/-- **A fact reads the entry state through its entry terms only**: it holds
at one entry state where it holds at another at which each of its entry
terms denotes the same. -/
theorem holdsAt_congr_entryTerms {F : IndexFact} {ε' : EntryState} {ρ : Env} {h : Heap}
    (ht : ∀ t ∈ F.entryTerms, termAt ε.env ε.heap t = termAt ε'.env ε'.heap t) :
    F.HoldsAt ε ρ h ↔ F.HoldsAt ε' ρ h := by
  have hterm : ∀ t : Term, (t.atEntry = true → termAt ε.env ε.heap t = termAt ε'.env ε'.heap t) →
      termValue ε ρ h t = termValue ε' ρ h t := by
    intro t h1
    cases he : t.atEntry
    · rw [termValue_now he, termValue_now he]
    · rw [termValue_atEntry he, termValue_atEntry he]; exact h1 he
  induction F with
  | either A B ihA ihB =>
    exact or_congr (ihA fun t h => ht t (List.mem_append_left _ h)) (ihB fun t h => ht t (List.mem_append_right _ h))
  | guarded s p t B ih => simp only [HoldsAt, ih ht]
  | linear G =>
    have heq : ∀ t ∈ G.vars, termValue ε ρ h t = termValue ε' ρ h t := fun t htm =>
      hterm t fun he => ht t (List.mem_filter.mpr ⟨htm, he⟩)
    simp only [HoldsAt]
    rw [Linear.Fact.holds_congr (v' := termValuation ε' ρ h) (fun t htm => by simp only [termValuation, heq t htm])]
    exact ⟨fun ⟨a, b⟩ => ⟨fun t hm => heq t hm ▸ a t hm, b⟩, fun ⟨a, b⟩ => ⟨fun t hm => (heq t hm).symm ▸ a t hm, b⟩⟩
  | every s p stop body =>
    have hst : termValue ε ρ h stop = termValue ε' ρ h stop :=
      hterm stop fun he => ht stop (List.mem_append_left _ (by simp [he]))
    have hb : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body,
        ∀ x ∈ F.vars, boundValue ε' ρ h ls i x = boundValue ε ρ h ls i x := by
      intro ls i F hF x hx
      cases x with
      | free t =>
        simp only [boundValue]
        exact (hterm t fun he => ht t (List.mem_append_right _ (List.mem_flatMap.mpr ⟨F, hF,
          List.mem_filterMap.mpr ⟨.free t, hx, by simp [he]⟩⟩))).symm
      | project k q =>
        simp only [boundValue]
        split
        · rename_i l _
          cases h[l]? with
          | none => rfl
          | some v => simp only [Option.bind_some]; rw [termValue_now rfl, termValue_now rfl]
        · rfl
      | _ => rfl
    simp only [HoldsAt, hst]
    constructor
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      exact ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F hF => LinearClause.holdsAt_congr (hb ls i F hF) (hall i hi F hF)⟩
    · rintro ⟨w, st, ls, n, hw, hsto, hls, hn, hall⟩
      exact ⟨w, st, ls, n, hw, hsto, hls, hn, fun i hi F hF =>
        LinearClause.holdsAt_congr (fun x hx => (hb ls i F hF x hx).symm) (hall i hi F hF)⟩
  | _ => exact Iff.rfl

/-- A postcondition's current position read in a frame with no receiver:
the result `0` at `0`, the receiver `1` at none, each later position one
lower. -/
def postPastReceiver (i : Nat) : Option Nat := if i = 0 then some 0 else if i = 1 then none else some (i - 1)

/-- A call position of the entry frame read in a frame with no receiver:
the receiver `0` at none, each later position one lower. -/
def entryPastReceiver (p : Nat) : Option Nat := if p = 0 then none else some (p - 1)

/-- **A postcondition read past the receiver**: its current positions by
`postPastReceiver`, its entry positions by `entryPastReceiver`; none where
it names the receiver in either state. -/
def pastReceiver (F : IndexFact) : Option IndexFact := F.reframe postPastReceiver entryPastReceiver

/-- **A postcondition read past the receiver means what it meant** (proved):
at a return of a frame `L` whose code was entered at `recv :: L`, the
translated fact holds at the entry `⟨envOf L d, h⟩` and the return's
positions `push v (envOf L d)` exactly where the fact holds at
`⟨envOf (recv :: L) d, h⟩` and `push v (envOf (recv :: L) d)`. -/
theorem holdsAt_pastReceiver {F F' : IndexFact} (hm : F.pastReceiver = some F') (L : List Tm) (recv d v : Tm)
    (h h' : Heap) :
    F'.HoldsAt ⟨envOf L d, h⟩ (push v (envOf L d)) h' ↔
      F.HoldsAt ⟨envOf (recv :: L) d, h⟩ (push v (envOf (recv :: L) d)) h' := by
  refine holdsAt_reframe hm (fun s _ t hst => ?_) rfl (fun s t hst => ?_)
  · unfold postPastReceiver at hst
    split at hst
    · cases hst; subst s; rfl
    · split at hst
      · cases hst
      · cases hst
        obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
        simp [push, envOf]
  · unfold entryPastReceiver at hst
    split at hst
    · cases hst
    · cases hst
      obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      simp [envOf]

/-- A linear fact over slots' values holds where its slots hold safe integers
meeting it. -/
theorem holdsAt_valueFact {F : Linear.Fact Nat} {ρ : Env} {h : Heap} :
    (IndexFact.linear (valueFact F)).HoldsAt ε ρ h ↔ (∀ x ∈ F.vars, (intValue (ρ x)).isSome) ∧ F.Holds (valuation ρ) := by
  simp only [HoldsAt, vars_valueFact, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    termValue_value, holds_valueFact]

/-- A linear fact whose terms read the environment alone holds in every heap. -/
theorem holdsAt_linear_heap {F : Linear.Fact Term} {ρ : Env} {h h' : Heap} (hv : F.vars.all Term.envOnly = true)
    (hF : (IndexFact.linear F).HoldsAt ε ρ h) : (IndexFact.linear F).HoldsAt ε ρ h' := by
  have heq : ∀ t ∈ F.vars, termValue ε ρ h t = termValue ε ρ h' t :=
    fun t ht => termValue_envOnly (List.all_eq_true.mp hv t ht)
  refine ⟨fun t ht => heq t ht ▸ hF.1 t ht, ?_⟩
  exact (Linear.Fact.holds_congr (v' := termValuation ε ρ h') (fun t ht => by simp only [termValuation, heq t ht])).mp hF.2

/-- A linear fact holds in a heap where each of its terms denotes what it
denoted in the heap the fact held in. -/
theorem holdsAt_linear_terms {F : Linear.Fact Term} {ρ : Env} {h h' : Heap}
    (heq : ∀ t ∈ F.vars, termValue ε ρ h' t = termValue ε ρ h t)
    (hF : (IndexFact.linear F).HoldsAt ε ρ h) : (IndexFact.linear F).HoldsAt ε ρ h' := by
  refine ⟨fun t ht => by rw [heq t ht]; exact hF.1 t ht, ?_⟩
  exact (Linear.Fact.holds_congr (v' := termValuation ε ρ h')
    (fun t ht => by simp only [termValuation, heq t ht])).mp hF.2

end IndexFact

namespace LinearClause

def toIndexFact : LinearClause Term → IndexFact
  | .atom F => .linear F
  | .either A B => .either A.toIndexFact B.toIndexFact

theorem toIndexFact_holds {F : LinearClause Term} {ρ : Env} {h : Heap} :
    F.toIndexFact.HoldsAt ε ρ h ↔ F.HoldsAt (termValue ε ρ h) := by
  induction F with
  | atom F => rfl
  | either A B ihA ihB => exact or_congr ihA ihB

end LinearClause


/-! ## Facts a heap change keeps (ARITHMETIC.md, "Linear facts")

A change is described by what a location held before it: an object, a
number, an array store. A term reads locations of known contents, its path's
objects, then a store or a number; it denotes the same after a change that
alters no location holding what it reads. -/

/-- What a heap change does to a location holding an array store: keeps its
contents, keeps its length, grows it (a store at least as long, at most
`2^32 - 1` long where it was), or neither. -/
inductive StoreChange where
  | keep
  | length
  | grow
  | any
  deriving DecidableEq, Repr

/-- Which locations a heap change may alter, by what they held before it: an
object (`obj`), a number (`num`), an array store (`store`). A location
holding any other value may change. -/
structure Changes where
  obj : Bool
  num : Bool
  store : StoreChange
  deriving DecidableEq, Repr

namespace Changes

/-- Whether the change may alter a location holding `v`. -/
def alters (c : Changes) : Val → Bool
  | .objAt .. => c.obj
  | .num _ => c.num
  | .arr _ => c.store != .keep
  | _ => true

/-- `h'` meets the change from `h`: every location of `h` holding a value it
does not alter holds it in `h'`, and where it keeps stores' lengths every
store of `h` is a store of that length in `h'`. -/
def Holds (c : Changes) (h h' : Heap) : Prop :=
  (∀ (l : Nat) (v : Val), h[l]? = some v → c.alters v = false → h'[l]? = some v) ∧
  (c.store = .length → ∀ (l : Nat) (ls : List (Option Nat)), h[l]? = some (.arr ls) →
    ∃ ls' : List (Option Nat), h'[l]? = some (.arr ls') ∧ ls'.length = ls.length) ∧
  (c.store = .grow → ∀ (l : Nat) (ls : List (Option Nat)), h[l]? = some (.arr ls) →
    ∃ ls' : List (Option Nat), h'[l]? = some (.arr ls') ∧ ls.length ≤ ls'.length ∧
      (ls.length ≤ maxArrayLength → ls'.length ≤ maxArrayLength))

/-- A change from a heap extending `before` is one from `before`. -/
theorem Holds.prefix_left {c : Changes} {before middle after : Heap} (hc : c.Holds middle after)
    (hprefix : before.IsPrefix middle) : c.Holds before after := by
  obtain ⟨t, rfl⟩ := hprefix
  have hget : ∀ {l : Nat} {v : Val}, before[l]? = some v → (before ++ t)[l]? = some v := fun hv => by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1, hv]
  exact ⟨fun l v hv ha => hc.1 l v (hget hv) ha, fun hs l ls hl => hc.2.1 hs l ls (hget hl),
    fun hs l ls hl => hc.2.2 hs l ls (hget hl)⟩

/-- Every change: where nothing is known of a location's contents. -/
def top : Changes := ⟨true, true, .any⟩

theorem top_alters (v : Val) : Changes.top.alters v = true := by
  cases v <;> simp [Changes.top, Changes.alters]

/-- Two changes' union. -/
def join (a b : Changes) : Changes :=
  ⟨a.obj || b.obj, a.num || b.num, if a.store == .keep && b.store == .keep then .keep else .any⟩

theorem join_alters_left {a b : Changes} {v : Val} (h : a.alters v = true) : (a.join b).alters v = true := by
  cases v <;> simp_all [Changes.join, Changes.alters]

theorem join_alters_right {a b : Changes} {v : Val} (h : b.alters v = true) : (a.join b).alters v = true := by
  cases v <;> simp_all [Changes.join, Changes.alters]

theorem top_holds (h h' : Heap) : top.Holds h h' :=
  ⟨fun _ v _ ha => (by rw [top_alters] at ha; cases ha), fun hs => (by simp [top] at hs),
    fun hs => (by simp [top] at hs)⟩

/-- The change a closed footprint allows: below `any` no location holding an
object changes, at most `init` none holding a number, `init` or `scalar` on a
store is `keep`, and `grow` on a store leaves each store no shorter and within
`maxArrayLength` where it was. -/
def ofClosed (Φ : Footprints.Closed) : Changes :=
  ⟨Φ.value == .any, !(Φ.value.le .init),
    match Φ.store.onStore with
    | .keep => .keep
    | .grow => .grow
    | _ => .any⟩

theorem ofClosed_holds {Φ : Footprints.Closed} {h h' : Heap} (hp : Φ.Holds h h') : (ofClosed Φ).Holds h h' := by
  rw [Footprints.Closed.holds_iff] at hp
  refine ⟨fun l v hv ha => ?_, fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨v', hv', hc⟩ := hp.2 l v hv
    have hkeep : v' = v := by
      cases v
      case arr ls =>
        simp only [alters, ofClosed] at ha
        have hst : Φ.store = .keep ∨ Φ.store = .init ∨ Φ.store = .scalar := by
          cases hΦ : Φ.store <;> simp_all [Footprints.Change.onStore]
        simp only [Footprints.Closed.at, Footprints.isArr, ite_true] at hc
        rcases hst with hst | hst | hst
        · rw [hst] at hc; exact hc
        · rw [hst] at hc; exact hc.init_store
        · rw [hst] at hc; exact hc.scalar_store
      case objAt =>
        have hva : Φ.value ≠ .any := by
          intro he; simp [alters, ofClosed, he] at ha
        simp only [Footprints.Closed.at, Footprints.isArr] at hc
        exact hc.object_kept hva rfl
      case num =>
        have hva : Φ.value.le .init = true := by
          simpa [alters, ofClosed] using ha
        simp only [Footprints.Closed.at, Footprints.isArr] at hc
        exact hc.defined_kept hva rfl
      all_goals simp [alters] at ha
    exact hkeep ▸ hv'
  · revert hs; simp only [ofClosed]; split <;> simp
  · intro l ls hl
    have hg : Φ.store = .grow := by
      revert hs; simp only [ofClosed]
      cases hΦ : Φ.store <;> simp [Footprints.Change.onStore]
    obtain ⟨v', hv', hc⟩ := hp.2 l _ hl
    simp only [Footprints.Closed.at, Footprints.isArr, ite_true, hg] at hc
    rcases hc with rfl | ⟨ls₁, ls', h₁, rfl, -, -, hlen⟩ | hsc
    · exact ⟨ls, hv', Nat.le_refl _, id⟩
    · cases h₁; exact ⟨ls', hv', hlen.1, hlen.2⟩
    · exact absurd hsc.2.1 (by simp [Footprints.isArr])

end Changes

/-- The location of field `g` of slot `s`'s object keeps its contents from
`h` to `h'` wherever `first s g` says so. -/
def FirstKept (first : Nat → String → Bool) (ρ : Env) (h h' : Heap) : Prop :=
  ∀ s g fs cd o l v, first s g = true → ρ s = .objAt fs cd o → fs.lookup (.str g) = some l →
    h[l]? = some v → h'[l]? = some v

/-- Whether a term denotes the same after a change `c`: each location its
path reads holds an object, but the last, which holds a number for a value
term; a length term then reads a store, a view term a number. The first
location, field `g` of the root's object, may instead be one `first` keeps. -/
def Term.pathKeptBy (c : Changes) (first : Nat → String → Bool) (t : Term) : Bool :=
  let last := if t.kind == .value then c.num else c.obj
  match t.path with
    | [] => true
    | g :: q => (first t.slot g || !(if q.isEmpty then last else c.obj)) &&
        (q.isEmpty || (!last && (q.length == 1 || !c.obj)))

/-- Whether a change keeps a store's length: it keeps the store or its
length. -/
def Changes.keepsLength (c : Changes) : Bool := c.store == .keep || c.store == .length

def Term.keptBy (c : Changes) (first : Nat → String → Bool) (t : Term) : Bool :=
  t.atEntry || t.pathKeptBy c first &&
  (match t.kind with
    | .value => true
    | .length => c.keepsLength || (t.path.isEmpty && first t.slot "[]")
    | .view => !c.num
    | .strLength => t.path.isEmpty)

/-- A change keeps what a path reads: each location it reads holds an object
the change keeps, but the last, which holds the value read. -/
theorem readPath_kept {c : Changes} {h h' : Heap} (hc : c.Holds h h') :
    ∀ (p : List String) (v w : Val), readPath h v p = some w → (p = [] ∨ c.alters w = false) →
      (2 ≤ p.length → c.obj = false) → readPath h' v p = some w := by
  intro p
  induction p with
  | nil => intro v w hw _ _; exact hw
  | cons f q ih =>
    intro v w hw hlast hobj
    have hw' : c.alters w = false := hlast.resolve_left (by simp)
    cases v
    case objAt fs cd o =>
      simp only [readPath] at hw ⊢
      split at hw
      · rename_i l hl
        split at hw
        · rename_i u hu
          have hkeep : h'[l]? = some u := by
            apply hc.1 l u hu
            cases q with
            | nil => simp only [readPath, Option.some.injEq] at hw; subst hw; exact hw'
            | cons g q' =>
              cases u
              case objAt => exact hobj (by simp)
              all_goals simp [readPath] at hw
          simp only [hkeep]
          exact ih u w hw (Or.inr hw') (fun h2 => hobj (by simp; omega))
        · cases hw
      · cases hw
    all_goals simp [readPath] at hw

theorem viewLengthOf_inv {h : Heap} {v : Val} {n : Int} (hv : viewLengthOf h v = some n) :
    ∃ fs cd o l b, v = .objAt fs cd o ∧ (fs.lookup hostKey).isSome ∧ fs.lookup viewLengthKey = some l ∧
      h[l]? = some (.num b) ∧ SafeIntegers.safeIntOfBits b = some n ∧ 0 ≤ n := by
  unfold viewLengthOf at hv
  split at hv
  · rename_i fs cd o
    split at hv
    · rename_i hhost
      split at hv
      · rename_i l hl
        split at hv
        · rename_i b hb
          split at hv
          · rename_i m hm
            split at hv
            · cases hv; exact ⟨fs, cd, o, l, b, rfl, hhost, hl, hb, hm, by assumption⟩
            · cases hv
          · cases hv
        · cases hv
      · cases hv
    · cases hv
  · cases hv

/-- A change keeps what a kind of term reads of a value: a store it keeps or
keeps the length of, a number it keeps. -/
theorem kindValue_kept {c : Changes} {h h' : Heap} (hc : c.Holds h h') {k : Term.Kind} {w : Val} {n : Int}
    (hk : kindValue h k w = some n) (hlen : k = .length → c.keepsLength = true) (hview : k = .view → c.num = false) :
    kindValue h' k w = some n := by
  cases k with
  | value => exact hk
  | strLength => exact hk
  | length =>
    obtain ⟨s, ls, hs, hls, rfl, hm⟩ := lengthOf_store hk
    have hst := hlen rfl
    cases hcs : c.store with
    | keep => exact lengthOf_of_store hs (hc.1 s _ hls (by simp [Changes.alters, hcs])) hm
    | length =>
      obtain ⟨ls', hls', heq⟩ := hc.2.1 hcs s ls hls
      have := lengthOf_of_store hs hls' (by omega)
      simp only [kindValue, this, heq]
    | grow | any => simp [Changes.keepsLength, hcs] at hst
  | view =>
    obtain ⟨fs, cd, o, l, b, rfl, hhost, hl, hb, hm, h0⟩ := viewLengthOf_inv hk
    have hb' := hc.1 l _ hb (by simp [Changes.alters, hview rfl])
    simp only [kindValue, viewLengthOf, hhost, ite_true, hl, hb', hm, h0]

/-- A change keeps the value a term's path reads where it keeps the path
(`Term.pathKeptBy`) and that value is of the class the term's kind reads. -/
theorem pathRead_kept {c : Changes} {first : Nat → String → Bool} {ρ : Env} {h h' : Heap}
    {kind : Term.Kind} {s : Nat} {p : List String} {w : Val}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h')
    (hpath : Term.pathKeptBy c first ⟨kind, s, p, false⟩ = true)
    (hlast : c.alters w = (if kind == .value then c.num else c.obj))
    (hw : readPath h (ρ s) p = some w) : readPath h' (ρ s) p = some w := by
  simp only [Term.pathKeptBy] at hpath
  cases p with
  | nil => exact hw
  | cons g q =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hpath
    obtain ⟨hfirst, htail⟩ := hpath
    have hq : q ≠ [] → c.alters w = false ∧ (2 ≤ q.length → c.obj = false) := by
      intro hq
      have hne : q.isEmpty = false := by simpa using hq
      simp only [hne, Bool.false_eq_true, false_or, beq_iff_eq] at htail
      refine ⟨by rw [hlast]; simpa using htail.1, fun h2 => htail.2.resolve_left (by omega)⟩
    rcases hfirst with hfirst | hnot
    · -- The first location kept by `first`; the rest by the change.
      cases hv : ρ s
      case objAt fs cd o =>
        rw [hv] at hw
        simp only [readPath] at hw ⊢
        split at hw
        · rename_i l hl
          split at hw
          · rename_i u hu
            simp only [hf s g fs cd o l u hfirst hv hl hu]
            by_cases hqe : q = []
            · subst hqe; exact hw
            · exact readPath_kept hc q u w hw (Or.inr (hq hqe).1) (hq hqe).2
          · cases hw
        · cases hw
      all_goals rw [hv] at hw; simp [readPath] at hw
    · refine readPath_kept hc (g :: q) (ρ s) w hw (Or.inr ?_) (fun h2 => ?_)
      · by_cases hqe : q = []
        · subst hqe; simpa [hlast] using hnot
        · exact (hq hqe).1
      · have hqe : q ≠ [] := by intro he; subst he; simp at h2
        have hne : q.isEmpty = false := by simpa using hqe
        simpa [hne] using hnot

/-- **A change keeps a term it keeps** (`Term.keptBy`). -/
theorem termValue_kept {c : Changes} {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {t : Term} {n : Int}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hk : t.keptBy c first = true)
    (ht : termValue ε ρ h t = some n) : termValue ε ρ h' t = some n := by
  obtain ⟨kind, s, p, a⟩ := t
  cases a
  case true => exact termValue_entry_some rfl ht
  simp only [termValue, termAt, Bool.false_eq_true, if_false, Option.bind_eq_some_iff] at ht ⊢
  obtain ⟨w, hw, hkw⟩ := ht
  simp only [Term.keptBy, Term.pathKeptBy, Bool.false_or, Bool.and_eq_true] at hk
  obtain ⟨hpath, hkind⟩ := hk
  by_cases hstr : kind = .strLength
  · -- A string's length reads the slot's own value alone.
    subst hstr
    simp only [List.isEmpty_iff] at hkind
    subst hkind
    exact ⟨w, hw, hkw⟩
  have hlast : c.alters w = (if kind == .value then c.num else c.obj) := by
    cases kind with
    | value =>
      simp only [kindValue] at hkw
      obtain ⟨b, rfl, -⟩ := intValue_safe hkw
      rfl
    | length =>
      obtain ⟨st, ls, hs, -⟩ := lengthOf_store hkw
      cases w
      case objAt => rfl
      all_goals simp [Footprints.storeOf, Footprints.fieldsOf] at hs
    | view =>
      obtain ⟨fs, cd, o, l, b, rfl, -⟩ := viewLengthOf_inv hkw
      rfl
    | strLength => exact absurd rfl hstr
  by_cases hfs : kind = .length ∧ p = [] ∧ first s "[]" = true
  · -- The store at field `[]` of the root's object, kept by `first`.
    obtain ⟨rfl, rfl, hfs⟩ := hfs
    refine ⟨w, hw, ?_⟩
    simp only [readPath, Option.some.injEq] at hw
    subst hw
    simp only [kindValue] at hkw ⊢
    obtain ⟨st, ls, hst, hls, rfl, hm⟩ := lengthOf_store hkw
    cases hv : ρ s
    case objAt fs cd o =>
      rw [hv] at hst
      have hl : fs.lookup (.str "[]") = some st := by
        simpa [Footprints.storeOf, Footprints.fieldsOf, arrayStoreKey] using hst
      exact lengthOf_of_store hst (hf s "[]" fs cd o st _ hfs hv hl hls) hm
    all_goals rw [hv] at hst; simp [Footprints.storeOf, Footprints.fieldsOf] at hst
  have hkind' : (match kind with
      | .value => true
      | .length => c.keepsLength
      | .view => !c.num
      | .strLength => true) = true := by
    cases kind with
    | value => rfl
    | strLength => rfl
    | view => simpa using hkind
    | length =>
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at hkind
      rcases hkind with h1 | ⟨h2, h3⟩
      · simpa using h1
      · exact absurd ⟨rfl, h2, h3⟩ hfs
  refine ⟨w, ?_, kindValue_kept hc hkw (fun he => by subst he; simpa using hkind')
    (fun he => by subst he; simpa using hkind')⟩
  exact pathRead_kept hc hf (by simpa [Term.pathKeptBy] using hpath) hlast hw

/-- Whether a change grows what a length term denotes: it keeps the term's
path and grows every store (`StoreChange.grow`). -/
def Term.grownBy (c : Changes) (first : Nat → String → Bool) (t : Term) : Bool :=
  t.kind == .length && c.store == .grow && t.pathKeptBy c first

/-- **A growing change keeps a length term defined, at least as large**
(`Term.grownBy`). -/
theorem termValue_grown {c : Changes} {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {t : Term} {n : Int}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hg : t.grownBy c first = true)
    (ht : termValue ε ρ h t = some n) : ∃ n', termValue ε ρ h' t = some n' ∧ n ≤ n' := by
  obtain ⟨kind, s, p, a⟩ := t
  cases a
  case true => exact ⟨n, termValue_entry_some rfl ht, Int.le_refl n⟩
  simp only [Term.grownBy, Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨⟨rfl, hs⟩, hpath⟩ := hg
  simp only [termValue, termAt, Bool.false_eq_true, if_false, Option.bind_eq_some_iff] at ht ⊢
  obtain ⟨w, hw, hkw⟩ := ht
  simp only [kindValue] at hkw
  obtain ⟨st, ls, hst, hls, rfl, hm⟩ := lengthOf_store hkw
  have hlast : c.alters w = (if Term.Kind.length == .value then c.num else c.obj) := by
    cases w
    case objAt => rfl
    all_goals simp [Footprints.storeOf, Footprints.fieldsOf] at hst
  obtain ⟨ls', hls', hle, hmax⟩ := hc.2.2 hs st ls hls
  refine ⟨ls'.length, ⟨w, pathRead_kept hc hf hpath hlast hw, ?_⟩, by exact_mod_cast hle⟩
  simp only [kindValue]
  exact lengthOf_of_store hst hls' (hmax hm)

/-- Whether a change keeps `F ≤ d` by monotonicity: each term it keeps, or a
length it grows whose coefficient is at most `0`. -/
def Term.formKeptBy (c : Changes) (first : Nat → String → Bool) (F : Linear.Form Term) : Bool :=
  F.all fun (t, a) => t.keptBy c first || (decide (a ≤ 0) && t.grownBy c first)

theorem formKept_eval {c : Changes} {first : Nat → String → Bool} {ρ : Env} {h h' : Heap}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') :
    ∀ {F : Linear.Form Term}, Term.formKeptBy c first F = true →
      (∀ t ∈ F.map (·.1), (termValue ε ρ h t).isSome) →
      (∀ t ∈ F.map (·.1), (termValue ε ρ h' t).isSome) ∧
        Linear.Form.eval (termValuation ε ρ h') F ≤ Linear.Form.eval (termValuation ε ρ h) F
  | [], _, _ => ⟨by simp, Int.le_refl _⟩
  | (t, a) :: F, hk, hd => by
    simp only [Term.formKeptBy, List.all_cons, Bool.and_eq_true] at hk
    obtain ⟨hk1, hk2⟩ := hk
    obtain ⟨hdr, hev⟩ := formKept_eval hc hf (F := F) hk2 (fun u hu => hd u (by simp [hu]))
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hd t (by simp))
    have hv : termValuation ε ρ h t = n := by simp [termValuation, hn]
    rcases Bool.or_eq_true_iff.mp hk1 with hkt | hgt
    · have hn' := termValue_kept hc hf hkt hn
      have hv' : termValuation ε ρ h' t = n := by simp [termValuation, hn']
      refine ⟨fun u hu => ?_, ?_⟩
      · simp only [List.map_cons, List.mem_cons] at hu
        rcases hu with rfl | hu
        · simp [hn']
        · exact hdr u hu
      · simp only [Linear.Form.eval, hv, hv']; omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hgt
      obtain ⟨ha, hg⟩ := hgt
      obtain ⟨n', hn', hle⟩ := termValue_grown hc hf hg hn
      have hv' : termValuation ε ρ h' t = n' := by simp [termValuation, hn']
      refine ⟨fun u hu => ?_, ?_⟩
      · simp only [List.map_cons, List.mem_cons] at hu
        rcases hu with rfl | hu
        · simp [hn']
        · exact hdr u hu
      · simp only [Linear.Form.eval, hv, hv']
        have : a * n' ≤ a * n := Int.mul_le_mul_of_nonpos_left ha hle
        omega

/-- Whether a fact over variables `V` holds at a valuation `val'` where it
holds at `val`, every variable `kept` names keeping its value and every one
`grown` names denoting at least as much (`factAt_monotone`): each variable
kept, or, in a fact `F ≤ d`, grown at a coefficient at most `0`. -/
def factMonotone {V : Type} (kept grown : V → Bool) : Linear.Fact V → Bool
  | .le G _ => G.all fun p => kept p.1 || (decide (p.2 ≤ 0) && grown p.1)
  | .ne G _ => G.all fun p => kept p.1

theorem form_monotone {V : Type} {kept grown : V → Bool} {val val' : V → Option Int}
    (hk : ∀ x n, kept x = true → val x = some n → val' x = some n)
    (hg : ∀ x n, grown x = true → val x = some n → ∃ n', val' x = some n' ∧ n ≤ n') :
    ∀ {G : Linear.Form V}, (G.all fun p => kept p.1 || (decide (p.2 ≤ 0) && grown p.1)) = true →
      (∀ x ∈ G.map (·.1), (val x).isSome) →
      (∀ x ∈ G.map (·.1), (val' x).isSome) ∧
        Linear.Form.eval (fun x => (val' x).getD 0) G ≤ Linear.Form.eval (fun x => (val x).getD 0) G
  | [], _, _ => ⟨by simp, Int.le_refl _⟩
  | (x, a) :: G, hm, hd => by
    simp only [List.all_cons, Bool.and_eq_true] at hm
    obtain ⟨hm1, hm2⟩ := hm
    obtain ⟨hdr, hev⟩ := form_monotone hk hg (G := G) hm2 (fun u hu => hd u (by simp [hu]))
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hd x (by simp))
    rcases Bool.or_eq_true_iff.mp hm1 with hkx | hgx
    · have hn' := hk x n hkx hn
      refine ⟨fun u hu => ?_, ?_⟩
      · simp only [List.map_cons, List.mem_cons] at hu
        rcases hu with rfl | hu
        · simp [hn']
        · exact hdr u hu
      · simp only [Linear.Form.eval, hn, hn', Option.getD_some]; omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hgx
      obtain ⟨ha, hgx⟩ := hgx
      obtain ⟨n', hn', hle⟩ := hg x n hgx hn
      refine ⟨fun u hu => ?_, ?_⟩
      · simp only [List.map_cons, List.mem_cons] at hu
        rcases hu with rfl | hu
        · simp [hn']
        · exact hdr u hu
      · simp only [Linear.Form.eval, hn, hn', Option.getD_some]
        have : a * n' ≤ a * n := Int.mul_le_mul_of_nonpos_left ha hle
        omega

/-- **A fact holds where it held, each variable kept or grown as it allows**
(`factMonotone`). -/
theorem factAt_monotone {V : Type} {kept grown : V → Bool} {val val' : V → Option Int}
    (hk : ∀ x n, kept x = true → val x = some n → val' x = some n)
    (hg : ∀ x n, grown x = true → val x = some n → ∃ n', val' x = some n' ∧ n ≤ n')
    {F : Linear.Fact V} (hm : factMonotone kept grown F = true) (hF : FactAt val F) : FactAt val' F := by
  cases F with
  | le G d =>
    obtain ⟨hd, hev⟩ := form_monotone hk hg (G := G) (by simpa only [factMonotone] using hm)
      (by simpa only [Linear.Fact.vars] using hF.1)
    exact ⟨by simpa only [Linear.Fact.vars] using hd, Int.le_trans hev hF.2⟩
  | ne G d =>
    have he : ∀ x ∈ (Linear.Fact.ne G d).vars, val' x = val x := by
      intro x hx
      simp only [factMonotone, List.all_eq_true] at hm
      simp only [Linear.Fact.vars, List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hF.1 q.1 (List.mem_map_of_mem hq))
      rw [hn, hk q.1 n (hm q hq) hn]
    exact factAt_congr he hF

/-- Each alternative is preserved by a checked monotone change. -/
def LinearClause.monotone (kept grown : V → Bool) : LinearClause V → Bool
  | .atom F => factMonotone kept grown F
  | .either A B => A.monotone kept grown && B.monotone kept grown

theorem LinearClause.holdsAt_monotone {val val' : V → Option Int} {kept grown : V → Bool}
    (hk : ∀ x n, kept x = true → val x = some n → val' x = some n)
    (hg : ∀ x n, grown x = true → val x = some n → ∃ n', val' x = some n' ∧ n ≤ n')
    {F : LinearClause V} (hm : F.monotone kept grown = true) (hF : F.HoldsAt val) : F.HoldsAt val' := by
  induction F with
  | atom F => exact factAt_monotone hk hg hm hF
  | either A B ihA ihB =>
    obtain ⟨hA, hB⟩ := Bool.and_eq_true_iff.mp hm
    exact hF.imp (ihA hA) (ihB hB)

/-- Whether a change keeps what a body variable denotes (`Term.keptBy`): the
index and the element are read apart. -/
def Bound.keptBy (c : Changes) (first : Nat → String → Bool) : Bound → Bool
  | .project _ _ | .offset _ => false
  | .free t => t.keptBy c first
  | _ => true

/-- Whether a change grows what a body variable denotes (`Term.grownBy`). -/
def Bound.grownBy (c : Changes) (first : Nat → String → Bool) : Bound → Bool
  | .free t => t.grownBy c first
  | _ => false

/-- Whether a change keeps a body fact of a quantified fact at an index whose
element it keeps: each term kept, or grown at a coefficient at most `0`. -/
def bodyKeptBy (c : Changes) (first : Nat → String → Bool) : LinearClause Bound → Bool :=
  LinearClause.monotone (Bound.keptBy c first) (Bound.grownBy c first)

namespace IndexFact

/-- A footprint frames a quantified clause when it keeps the store and
numeric element cells, its array path, bound and every free body term. -/
def everyKept (c : Changes) (first : Nat → String → Bool) : IndexFact → Bool
  | .every s p stop body => c.store == .keep && !c.num &&
      (Term.mk .length s p false).pathKeptBy c first && stop.keptBy c first &&
      body.all (fun F => F.vars.all fun b => match b with
        | .free t => t.keptBy c first
        | .project _ _ => false
        | _ => true)
  | _ => false

theorem everyKept_sound {c : Changes} {first : Nat → String → Bool} {F : IndexFact} {ρ h h'}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h')
    (hk : F.everyKept c first = true) (hF : F.HoldsAt ε ρ h) : F.HoldsAt ε ρ h' := by
  cases F <;> simp only [everyKept] at hk
  all_goals try contradiction
  rename_i s p stop body
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.all_eq_true] at hk
  obtain ⟨⟨⟨⟨hstore, hnum⟩, hpath⟩, hstop⟩, hbody⟩ := hk
  obtain ⟨w, st, ls, z, hw, hst, hls, hz, hall⟩ := hF
  have hobj : c.alters w = c.obj := by
    cases w <;> simp_all [elementsOf, Footprints.storeOf, Footprints.fieldsOf, Changes.alters]
  have hpath' := pathRead_kept (kind := .length) hc hf hpath hobj hw
  refine ⟨w, st, ls, z, hpath', hst, hc.1 st _ hls (by simp [Changes.alters, hstore]),
    termValue_kept hc hf hstop hz, fun i hi F hm => ?_⟩
  have hA := hall i hi F hm
  apply LinearClause.holdsAt_extend (fun x hx a ha => ?_) hA
  have elem : ∀ j, elementInt h ls j = some a → elementInt h' ls j = some a := by
    intro j hj
    apply elementInt_frame hj
    intro l v hl hv
    have hz' : intValue v = some a := by
      simpa only [elementInt, hl, hv, Option.bind_some] using hj
    obtain ⟨b, rfl, _⟩ := intValue_safe hz'
    exact hc.1 l _ hv (by simp [Changes.alters, hnum])
  cases x with
  | index => exact ha
  | free t => exact termValue_kept (ε := ε) hc hf (hbody F hm (.free t) hx) ha
  | elem => exact elem i ha
  | offset d => exact elem (i + d) ha
  | project k p => have := hbody F hm (.project k p) hx; contradiction

/-- A change keeping every store keeps every region: its store cell holds
the same store, and a raw store reads no heap. -/
theorem regionOf_kept {c : Changes} {h h' : Heap} {v : Val} {s xs}
    (hc : c.Holds h h') (hk : c.store = .keep) (hr : RegionOf h v s xs) : RegionOf h' v s xs := by
  rcases hr with hr | ⟨st, hs, hst, hx⟩
  · exact .inl hr
  · exact .inr ⟨st, hs, hst, hc.1 st _ hx (by simp [Changes.alters, hk])⟩

theorem regionsApart_kept {c : Changes} {h h' : Heap} {u v : Val}
    (hc : c.Holds h h') (hk : c.store = .keep) (ha : RegionsApart h u v) : RegionsApart h' u v := by
  obtain ⟨sa, xs, sb, ys, hx, hy, hab⟩ := ha
  exact ⟨sa, xs, sb, ys, regionOf_kept hc hk hx, regionOf_kept hc hk hy, hab⟩

/-- Whether a change preserves a fact (`Term.keptBy`): `index` and `int` read
no heap, `length` and `bound` a store's length. -/
def keptBy (c : Changes) (first : Nat → String → Bool) : IndexFact → Bool
  | .index _ | .int _ | .pastSafe _ => true
  | .length x _ => c.keepsLength || first x "[]"
  | .bound x _ _ => c.store != .any || first x "[]"
  | .linear F => F.vars.all (Term.keptBy c first) || match F with
    | .le G _ => Term.formKeptBy c first G
    | .ne _ _ => false
  | .either A B => A.keptBy c first && B.keptBy c first
  | .guarded s p _ B => guardKept first s p && B.keptBy c first
  | .element .. | .every .. => false
  | .apart .. => c.store == .keep
  | .storeApart a p b q => guardKept first a p && guardKept first b q

theorem holdsAt_kept {c : Changes} {first : Nat → String → Bool} {F : IndexFact} {ρ : Env} {h h' : Heap}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hk : F.keptBy c first = true) (hF : F.HoldsAt ε ρ h) :
    F.HoldsAt ε ρ h' := by
  have store : ∀ {x s : Nat} {ls : List (Option Nat)}, (c.store != .any || first x "[]") = true →
      Footprints.storeOf (ρ x) = some s → h[s]? = some (.arr ls) →
      ∃ ls' : List (Option Nat), h'[s]? = some (.arr ls') ∧ ls.length ≤ ls'.length ∧
        ((c.keepsLength || first x "[]") = true → ls'.length = ls.length) := by
    intro x s ls hk hs hls
    by_cases hfs : first x "[]" = true
    · cases hv : ρ x
      case objAt fs cd o =>
        rw [hv] at hs
        have hl : fs.lookup (.str "[]") = some s := by
          simpa [Footprints.storeOf, Footprints.fieldsOf, arrayStoreKey] using hs
        exact ⟨ls, hf x "[]" fs cd o s _ hfs hv hl hls, Nat.le_refl _, fun _ => rfl⟩
      all_goals rw [hv] at hs; simp [Footprints.storeOf, Footprints.fieldsOf] at hs
    · simp only [hfs, Bool.or_false] at hk ⊢
      cases hcs : c.store with
      | keep => exact ⟨ls, hc.1 s _ hls (by simp [Changes.alters, hcs]), Nat.le_refl _, fun _ => rfl⟩
      | length =>
        obtain ⟨ls', hls', heq⟩ := hc.2.1 hcs s ls hls
        exact ⟨ls', hls', by omega, fun _ => heq⟩
      | grow =>
        obtain ⟨ls', hls', hle, -⟩ := hc.2.2 hcs s ls hls
        exact ⟨ls', hls', hle, fun h => by simp [Changes.keepsLength, hcs] at h⟩
      | any => simp [hcs] at hk
  induction F with
  | either A B ihA ihB =>
    simp only [keptBy, Bool.and_eq_true] at hk
    exact hF.imp (ihA hk.1) (ihB hk.2)
  | apart a b =>
    simp only [keptBy, beq_iff_eq] at hk
    exact regionsApart_kept hc hk hF
  | storeApart a p b q =>
    simp only [keptBy, Bool.and_eq_true] at hk
    obtain ⟨u, w, hu, hw, hne⟩ := hF
    exact ⟨u, w, readPath_guardKept hf hk.1 hu, readPath_guardKept hf hk.2 hw, hne⟩
  | guarded s p t B ih =>
    simp only [keptBy, Bool.and_eq_true] at hk
    obtain ⟨v, hv, hor⟩ := hF
    exact ⟨v, readGuard_kept hf hk.1 hv, hor.imp id (ih hk.2)⟩
  | element _ _ _ => simp [keptBy] at hk
  | every _ _ _ _ => simp [keptBy] at hk
  | index k => exact hF
  | int k => exact hF
  | pastSafe k => exact hF
  | length x m =>
    simp only [keptBy] at hk
    obtain ⟨s, ls, hs, hls, hm, hmax⟩ := hF
    have hk' : (c.store != .any || first x "[]") = true := by
      rcases Bool.or_eq_true_iff.mp hk with h1 | h1
      · cases hcs : c.store <;> simp_all [Changes.keepsLength]
      · simp [h1]
    obtain ⟨ls', hls', -, heq⟩ := store hk' hs hls
    have heq := heq hk
    exact ⟨s, ls', hs, hls', heq ▸ hm, heq ▸ hmax⟩
  | bound x k st =>
    simp only [keptBy] at hk
    obtain ⟨s, ls, b, i, hs, hls, hb, hi, hle⟩ := hF
    obtain ⟨ls', hls', hgrow, -⟩ := store hk hs hls
    exact ⟨s, ls', b, i, hs, hls', hb, hi, by omega⟩
  | linear G =>
    simp only [keptBy, Bool.or_eq_true, List.all_eq_true] at hk
    rcases hk with hk | hk
    · obtain ⟨hi, hh⟩ := hF
      have heq : ∀ t ∈ G.vars, termValue ε ρ h' t = termValue ε ρ h t := by
        intro t ht
        obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hi t ht)
        rw [hn, termValue_kept hc hf (hk t ht) hn]
      refine ⟨fun t ht => by rw [heq t ht]; exact hi t ht, ?_⟩
      rw [Linear.Fact.holds_congr (v' := termValuation ε ρ h) (fun t ht => by simp only [termValuation, heq t ht])]
      exact hh
    · cases G with
      | ne _ _ => simp at hk
      | le G d =>
        simp only at hk
        obtain ⟨hd, hev⟩ := formKept_eval hc hf hk hF.1
        exact ⟨hd, Int.le_trans hev hF.2⟩

end IndexFact


/-- Where `views s g` holds, the view the field `g` of slot `s`'s object held
preserves its length from `h` to `h'`. -/
def ViewsKept (views : Nat → String → Bool) (ρ : Env) (h h' : Heap) : Prop :=
  ∀ s g fs cd o l w, views s g = true → ρ s = .objAt fs cd o → fs.lookup (.str g) = some l →
    h[l]? = some w → viewLengthOf h' w = viewLengthOf h w

/-- Whether a change keeps the length of a view read through one
field (`view-path-stable`): the field's location is one `first` keeps or holds
an object the change keeps, and `views` frames the view's length. -/
def Term.viewFramed (c : Changes) (first views : Nat → String → Bool) (t : Term) : Bool :=
  t.kind == .view && match t.path with
    | [g] => (first t.slot g || !c.obj) && views t.slot g
    | _ => false

theorem termValue_viewFramed {c : Changes} {first views : Nat → String → Bool} {ρ : Env} {h h' : Heap}
    {t : Term} {n : Int} (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hv : ViewsKept views ρ h h')
    (hk : t.viewFramed c first views = true) (ht : termValue ε ρ h t = some n) : termValue ε ρ h' t = some n := by
  obtain ⟨kind, s, p, a⟩ := t
  cases a
  case true => exact termValue_entry_some rfl ht
  simp only [Term.viewFramed, Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨rfl, hp⟩ := hk
  match p, hp with
  | [g], hp =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp
    obtain ⟨hfirst, hvs⟩ := hp
    simp only [termValue, termAt, Bool.false_eq_true, if_false, Option.bind_eq_some_iff] at ht ⊢
    obtain ⟨w, hw, hkw⟩ := ht
    cases hs : ρ s
    case objAt fs0 cd0 o0 =>
      rw [hs] at hw
      simp only [readPath] at hw ⊢
      split at hw
      · rename_i l hl
        split at hw
        · rename_i u hu
          simp only [Option.some.injEq] at hw
          subst hw
          have hu' : h'[l]? = some u := by
            rcases hfirst with hfirst | hobj
            · exact hf s g fs0 cd0 o0 l u hfirst hs hl hu
            · obtain ⟨fs, cd, o, -, -, rfl, -⟩ := viewLengthOf_inv hkw
              exact hc.1 l _ hu (by simp [Changes.alters, hobj])
          refine ⟨u, by simp [hu'], ?_⟩
          simp only [kindValue] at hkw ⊢
          rw [hv s g fs0 cd0 o0 l u hvs hs hl hu]; exact hkw
        · cases hw
      · cases hw
    all_goals rw [hs] at hw; simp [readPath] at hw

namespace IndexFact

/-- Whether a change preserves a fact, each of its terms kept by `Term.keptBy` or
framed by `Term.viewFramed`, or the fact kept by `keptBy`. -/
def keptWith (c : Changes) (first views : Nat → String → Bool) : IndexFact → Bool
  | .linear F => (F.vars.all fun t => t.keptBy c first || t.viewFramed c first views) ||
      (IndexFact.linear F).keptBy c first
  | F => F.keptBy c first

theorem holdsAt_keptWith {c : Changes} {first views : Nat → String → Bool} {F : IndexFact} {ρ : Env} {h h' : Heap}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hv : ViewsKept views ρ h h')
    (hk : F.keptWith c first views = true) (hF : F.HoldsAt ε ρ h) : F.HoldsAt ε ρ h' := by
  cases F with
  | linear G =>
    simp only [keptWith, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    rotate_left
    · exact holdsAt_kept hc hf hk hF
    simp only [List.all_eq_true, Bool.or_eq_true] at hk
    refine holdsAt_linear_terms (fun t ht => ?_) hF
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (hF.1 t ht)
    rw [hm]
    rcases hk t ht with hk | hk
    · exact termValue_kept hc hf hk hm
    · exact termValue_viewFramed hc hf hv hk hm
  | index _ => exact holdsAt_kept hc hf (by simp [keptWith] at hk ⊢; exact hk) hF
  | int _ => exact holdsAt_kept hc hf (by simp [keptWith] at hk ⊢; exact hk) hF
  | pastSafe _ => exact holdsAt_kept hc hf (by simp [keptWith] at hk ⊢; exact hk) hF
  | length _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | bound _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | either _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | guarded _ _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | element _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | every _ _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | apart _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | storeApart _ _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF

end IndexFact

/-- Where `grown s` holds, the store of slot `s`'s value is no shorter in
`h'`, and within `maxArrayLength` where it was. -/
def StoresGrown (grown : Nat → Bool) (ρ : Env) (h h' : Heap) : Prop :=
  ∀ s l ls, grown s = true → Footprints.storeOf (ρ s) = some l → h[l]? = some (.arr ls) →
    ∃ ls', h'[l]? = some (.arr ls') ∧ Footprints.LengthGrows ls ls'

/-- Whether a term is the length of the store of a slot's own value that
`grown` names. -/
def Term.storeGrown (grown : Nat → Bool) (t : Term) : Bool :=
  t.kind == .length && t.path.isEmpty && grown t.slot

/-- **A grown store's length is defined and at least as large**
(`Term.storeGrown`). -/
theorem termValue_storeGrown {grown : Nat → Bool} {ρ : Env} {h h' : Heap} {t : Term} {n : Int}
    (hg : StoresGrown grown ρ h h') (ht : t.storeGrown grown = true) (hn : termValue ε ρ h t = some n) :
    ∃ n', termValue ε ρ h' t = some n' ∧ n ≤ n' := by
  obtain ⟨kind, s, p, a⟩ := t
  cases a
  case true => exact ⟨n, termValue_entry_some rfl hn, Int.le_refl n⟩
  simp only [Term.storeGrown, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at ht
  obtain ⟨⟨rfl, rfl⟩, hs⟩ := ht
  rw [termValue_nil] at hn ⊢
  simp only [kindValue] at hn ⊢
  obtain ⟨l, ls, hl, hls, rfl, hm⟩ := lengthOf_store hn
  obtain ⟨ls', hls', hle, hmax⟩ := hg s l ls hs hl hls
  exact ⟨ls'.length, lengthOf_of_store hl hls' (hmax hm), by exact_mod_cast hle⟩

namespace IndexFact

/-- Whether a fact holds after a change `c` that also grows the stores
`grown` names (`StoresGrown`): a linear fact each of whose terms is kept or
framed as `keptWith` keeps it, or, in `F ≤ d`, a length of such a store at a
coefficient at most `0` (`factMonotone`); a bound below the length of such a
store; or a fact `keptWith` keeps. -/
def grownWith (c : Changes) (first views : Nat → String → Bool) (grown : Nat → Bool) : IndexFact → Bool
  | .linear F => factMonotone (fun t => t.keptBy c first || t.viewFramed c first views)
      (Term.storeGrown grown) F || (IndexFact.linear F).keptWith c first views
  | .bound x k st => grown x || (IndexFact.bound x k st).keptWith c first views
  | F => F.keptWith c first views

theorem holdsAt_grownWith {c : Changes} {first views : Nat → String → Bool} {grown : Nat → Bool}
    {F : IndexFact} {ρ : Env} {h h' : Heap}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hv : ViewsKept views ρ h h')
    (hg : StoresGrown grown ρ h h') (hk : F.grownWith c first views grown = true) (hF : F.HoldsAt ε ρ h) :
    F.HoldsAt ε ρ h' := by
  cases F with
  | linear G =>
    simp only [grownWith, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · refine factAt_monotone (val := termValue ε ρ h) (val' := termValue ε ρ h') (fun t n ht hn => ?_)
        (fun t n ht hn => termValue_storeGrown hg ht hn) hk hF
      rcases Bool.or_eq_true_iff.mp ht with ht | ht
      · exact termValue_kept hc hf ht hn
      · exact termValue_viewFramed hc hf hv ht hn
    · exact holdsAt_keptWith hc hf hv hk hF
  | bound x k st =>
    simp only [grownWith, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · obtain ⟨s, ls, b, i, hs, hls, hb, hi, hle⟩ := hF
      obtain ⟨ls', hls', hgr, -⟩ := hg x s ls hk hs hls
      exact ⟨s, ls', b, i, hs, hls', hb, hi, by omega⟩
    · exact holdsAt_keptWith hc hf hv hk hF
  | index _ => exact holdsAt_keptWith hc hf hv (by simpa [grownWith] using hk) hF
  | int _ => exact holdsAt_keptWith hc hf hv (by simpa [grownWith] using hk) hF
  | pastSafe _ => exact holdsAt_keptWith hc hf hv (by simpa [grownWith] using hk) hF
  | length _ _ => exact holdsAt_keptWith hc hf hv (by simpa [grownWith] using hk) hF
  | either _ _ => exact holdsAt_keptWith hc hf hv (by simpa [grownWith] using hk) hF
  | guarded _ _ _ _ => exact holdsAt_keptWith hc hf hv (by simpa [grownWith] using hk) hF
  | element _ _ _ => exact holdsAt_keptWith hc hf hv (by simpa [grownWith] using hk) hF
  | every _ _ _ _ => exact holdsAt_keptWith hc hf hv (by simpa [grownWith] using hk) hF
  | apart _ _ => exact holdsAt_keptWith hc hf hv (by simpa [grownWith] using hk) hF
  | storeApart _ _ _ _ => exact holdsAt_keptWith hc hf hv (by simpa [grownWith] using hk) hF

end IndexFact

end Verification.HeapKnowledge
