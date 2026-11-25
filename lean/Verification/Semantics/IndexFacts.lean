import Verification.Semantics.ClosedFootprints
import Verification.Semantics.SafeIntegers
import Verification.Semantics.Linear

/-! Index facts: what a slot holds as an array index, a length, a bound by a
spine's length, a safe integer or a linear fact (PROGRAM-TYPING.md, "Writes at
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
(`value`), the length of its array spine (`length`), the length of
the typed array it is (`view`), the count of UTF-16 code units of the
string it is (`strLength`), or its 32-bit integer masked by `mask` (`bitMask`,
for `0 ≤ mask < 2^31`). -/
inductive Term.Kind where
  | value
  | length
  | view
  | strLength
  | bitMask (mask : Nat)
  deriving DecidableEq, Repr, Hashable

/-- A term of a linear fact (ARITHMETIC.md, "Linear facts"): a root slot,
a path of named data fields read in turn from the value it holds, and what
the term reads of the value the path ends at (`Term.Kind`): the safe integer
it is; the length of its array spine, as the calculus's `lenOf` gives it
(`Step.lenV`), at most `maxArrayLength`; or the length of the typed
array it is, the safe integer at least `0` its descriptor states
(`viewLengthOf`); or the count of UTF-16 code units of
the string it is, at most `maxStringLength` (`strLengthOf`). The empty path
reads the slot's value itself.

A term's slot is a slot of one of two environments, the current one or, for
an entry term, the entry state's: two namespaces. The constructor is private:
a term is built by `Term.now` or `Term.old`, which name its namespace, and its
slot renamed only by maps that take the namespace (`Term.mapM` for current
slots, `Term.mapEntry` for entry slots, `Term.reroot` for both), so a map of
one namespace is never applied to a slot of the other. -/
structure Term where
  private mk ::
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

/-- The term of kind `k` reading path `p` from slot `s` of the current
environment. -/
abbrev now (k : Kind) (s : Nat) (p : List String) : Term := ⟨k, s, p, false⟩

/-- The term of kind `k` reading path `p` from slot `s` of the entry
environment: `old(t)`. -/
abbrev old (k : Kind) (s : Nat) (p : List String) : Term := ⟨k, s, p, true⟩

@[simp] theorem now_kind (k : Kind) (s : Nat) (p : List String) : (now k s p).kind = k := rfl
@[simp] theorem now_slot (k : Kind) (s : Nat) (p : List String) : (now k s p).slot = s := rfl
@[simp] theorem now_path (k : Kind) (s : Nat) (p : List String) : (now k s p).path = p := rfl
@[simp] theorem now_atEntry (k : Kind) (s : Nat) (p : List String) : (now k s p).atEntry = false := rfl
@[simp] theorem old_kind (k : Kind) (s : Nat) (p : List String) : (old k s p).kind = k := rfl
@[simp] theorem old_slot (k : Kind) (s : Nat) (p : List String) : (old k s p).slot = s := rfl
@[simp] theorem old_path (k : Kind) (s : Nat) (p : List String) : (old k s p).path = p := rfl
@[simp] theorem old_atEntry (k : Kind) (s : Nat) (p : List String) : (old k s p).atEntry = true := rfl

/-- A current term is `now` of its fields, an entry term `old` of them. -/
theorem eta (t : Term) : t = if t.atEntry then old t.kind t.slot t.path else now t.kind t.slot t.path := by
  obtain ⟨k, s, p, a⟩ := t; cases a <;> rfl

theorem eq_now {t : Term} (h : t.atEntry = false) : t = now t.kind t.slot t.path := by
  obtain ⟨k, s, p, a⟩ := t; cases h; rfl

/-- The safe integer a slot holds. -/
def value (s : Nat) : Term := ⟨.value, s, [], false⟩
/-- The length of the array spine a slot holds. -/
def length (s : Nat) : Term := ⟨.length, s, [], false⟩
/-- The length of the string a slot holds. -/
def strLength (s : Nat) : Term := ⟨.strLength, s, [], false⟩

/-- Whether a kind reads a number directly (`.value` or `.bitMask`). -/
def Kind.isNum : Kind → Bool
  | .value | .bitMask _ => true
  | _ => false

/-- Whether a term reads no current heap: an entry term, which reads the
entry state, or a slot's own value, masked value, or string length. -/
def envOnly (t : Term) : Bool :=
  t.atEntry || ((t.kind.isNum || t.kind == .strLength) && t.path.isEmpty)

def Kind.code : Kind → Nat
  | .value => 0
  | .length => 1
  | .view => 2
  | .strLength => 3
  | .bitMask _ => 4

def Kind.before : Kind → Kind → Bool
  | .bitMask m1, .bitMask m2 => decide (m1 < m2)
  | k1, k2 => decide (k1.code < k2.code)

/-- Paths in lexicographic order, the empty path first. -/
def pathBefore : List String → List String → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: p, b :: q => decide (a < b) || (a == b && pathBefore p q)

/-- An order on terms: by slot, kind, entry flag, then path. -/
def before (a b : Term) : Bool :=
  a.slot < b.slot || (a.slot == b.slot && (a.kind.before b.kind ||
    (a.kind == b.kind && ((!a.atEntry && b.atEntry) || (a.atEntry == b.atEntry && pathBefore a.path b.path)))))

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
  · simp only [he, Bool.false_eq_true, ite_false, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact .inr ⟨rfl, hs, rfl⟩
  · simp only [he, ite_true, Option.some.injEq] at h
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
    simp only [slots, he, Bool.false_eq_true, ite_false, List.mem_singleton] at hy
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
  · simp only [he, Bool.false_eq_true, ite_false, Option.some.injEq] at h
    exact .inl ⟨rfl, h.symm⟩
  · simp only [he, ite_true, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact .inr ⟨rfl, hs, rfl⟩

/-- **A term re-rooted, each state by its own map.** A root is a slot and a
path read from it before the term's own. A current term at slot `s` is read
from the root `now s` names in the current environment; an entry term at
slot `s` from the root `entry s` names in the entry environment. The two
environments are two namespaces: a slot of one is no slot of the other. -/
def reroot (now entry : Nat → Option (Nat × List String)) (t : Term) : Option Term :=
  ((if t.atEntry then entry else now) t.slot).map fun (s, p) => { t with slot := s, path := p ++ t.path }

/-- A term read at the current state: `old(t)` as `t`. -/
def toNow (t : Term) : Term := { t with atEntry := false }

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
"Guarded clauses"): equality or inequality against `null`, `undefined`,
`true`, or `false`. -/
inductive GuardTag where
  | null
  | undef
  | tru
  | fls
  | notNull
  | notUndef
  | notTru
  | notFls
  deriving DecidableEq, Repr, Hashable

/-- The value a positive guard tag names, where it is positive. -/
def GuardTag.val? : GuardTag → Option Val
  | .null => some .nul
  | .undef => some .undef
  | .tru => some .tru
  | .fls => some .fls
  | .notNull | .notUndef | .notTru | .notFls => none

/-- Whether a guard tag tests equality against one primitive tag (`===`). -/
def GuardTag.isPositive : GuardTag → Bool
  | .null | .undef | .tru | .fls => true
  | .notNull | .notUndef | .notTru | .notFls => false

/-- The complementary guard tag (`===` ↔ `!==`). -/
def GuardTag.complement : GuardTag → GuardTag
  | .null => .notNull
  | .notNull => .null
  | .undef => .notUndef
  | .notUndef => .undef
  | .tru => .notTru
  | .notTru => .tru
  | .fls => .notFls
  | .notFls => .fls

/-- Whether a value satisfies a guard tag. -/
def GuardTag.holds : GuardTag → Val → Prop
  | .null, v => v = .nul
  | .undef, v => v = .undef
  | .tru, v => v = .tru
  | .fls, v => v = .fls
  | .notNull, v => v ≠ .nul
  | .notUndef, v => v ≠ .undef
  | .notTru, v => v ≠ .tru
  | .notFls, v => v ≠ .fls

theorem GuardTag.complement_not_holds {t : GuardTag} {v : Val}
    (hc : t.complement.holds v) : ¬ t.holds v := by
  cases t <;> simp_all [GuardTag.complement, GuardTag.holds]

/-- Whether `undefined` satisfies a guard tag. -/
def GuardTag.holdsUndef : GuardTag → Bool
  | .undef | .notNull | .notTru | .notFls => true
  | .null | .tru | .fls | .notUndef => false

theorem GuardTag.not_holds_undef {t : GuardTag} (h : t.holdsUndef = false) : ¬ t.holds .undef := by
  cases t <;> simp_all [GuardTag.holdsUndef, GuardTag.holds]

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

/-- The length of the array spine a value holds, read in the heap, where it
is at most `maxArrayLength`. -/
def lengthOf (h : Heap) (v : Val) : Option Int :=
  match Footprints.spineOf v with
  | some s => match h[s]? with
    | some (.arr ls) => if ls.length ≤ maxArrayLength then some (ls.length : Int) else none
    | _ => none
  | none => none

theorem lengthOf_spine {h : Heap} {v : Val} {n : Int} (hl : lengthOf h v = some n) :
    ∃ s ls, Footprints.spineOf v = some s ∧ h[s]? = some (.arr ls) ∧ n = (ls.length : Int) ∧
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

/-- **A well-formed typed array owns no array-spine slot** (the note
*Tolerant frames*, (W3): a typed array's one spine is the view spine its
descriptor names). -/
theorem RefsOk.view_noArraySpine {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {i s n : Nat}
    {f : ViewFormat} (hr : RefsOk W (.viewAt fs i s f n)) : fs.lookup arraySpineKey = none := by
  have := (hr (.view s f n (fs.lookup arraySpineKey).isNone) (by simp [refs])).1
  simpa using this

/-- **The descriptor selects a well-formed typed array's spine**, whatever
its other fields: it is the spine of elements its element facts read, it
has no array spine, and so no array length; its length is its
descriptor's (`viewLengthOf`). -/
theorem RefsOk.view_selects {k : Nat} {W : WorldT k} {fs : List (PropKey × Nat)} {i s n : Nat}
    {f : ViewFormat} (hr : RefsOk W (.viewAt fs i s f n)) (h : Heap) :
    elementsOf (.viewAt fs i s f n) = some s ∧ Footprints.spineOf (.viewAt fs i s f n) = none ∧
      lengthOf h (.viewAt fs i s f n) = none := by
  have hno := RefsOk.view_noArraySpine hr
  refine ⟨elementsOf_view hno i s f n, by simpa [Footprints.spineOf, Footprints.fieldsOf] using hno, ?_⟩
  simp [lengthOf, Footprints.spineOf, Footprints.fieldsOf, hno]

theorem lengthOf_of_spine {h : Heap} {v : Val} {s : Nat} {ls : List (Option Nat)} (hs : Footprints.spineOf v = some s)
    (hl : h[s]? = some (.arr ls)) (hm : ls.length ≤ maxArrayLength) : lengthOf h v = some (ls.length : Int) := by
  simp only [lengthOf, hs, hl, hm, ite_true]

/-- The length of the typed array a value is (the note *Tolerant frames*,
`view(b)`): its descriptor's fixed length, a safe integer. It reads no
heap: the length is part of the value. -/
def viewLengthOf : Val → Option Int
  | .viewAt _ _ _ _ N => if N < 2 ^ 53 then some N else none
  | _ => none

theorem viewLengthOf_range {v : Val} {n : Int} (hv : viewLengthOf v = some n) :
    0 ≤ n ∧ n ≤ 2 ^ 53 - 1 := by
  unfold viewLengthOf at hv
  split at hv
  · split at hv
    · cases hv; omega
    · cases hv
  · cases hv

/-- A typed array's length is its descriptor's. -/
theorem viewLengthOf_inv {v : Val} {n : Int} (hv : viewLengthOf v = some n) :
    ∃ fs o s f N, v = .viewAt fs o s f N ∧ n = N ∧ N < 2 ^ 53 := by
  unfold viewLengthOf at hv
  split at hv
  · split at hv
    · cases hv; exact ⟨_, _, _, _, _, rfl, rfl, by assumption⟩
    · cases hv
  · cases hv

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

/-- The 32-bit masked integer `ToInt32(v) & m` of a numeric value, for a
non-negative 32-bit mask `m < 2^31`. -/
def bitMaskOf (m : Nat) : Val → Option Int
  | .num b => if m < 2 ^ 31 then some (intAnd (toInt32 b) (m : Int)) else none
  | _ => none

theorem bitMaskOf_range {m : Nat} {v : Val} {n : Int} (hv : bitMaskOf m v = some n) :
    0 ≤ n ∧ n ≤ (m : Int) ∧ m < 2 ^ 31 := by
  cases v with
  | num b =>
    simp only [bitMaskOf] at hv
    split at hv
    · rename_i hm
      cases hv
      have hr := IndexNumbers.intAnd_mask_range (toInt32 b) m
      exact ⟨hr.1, hr.2, hm⟩
    · cases hv
  | _ => cases hv

/-- What a kind of term reads of a value. -/
def kindValue (h : Heap) : Term.Kind → Val → Option Int
  | .value, v => intValue v
  | .length, v => lengthOf h v
  | .view, v => viewLengthOf v
  | .strLength, v => strLengthOf v
  | .bitMask m, v => bitMaskOf m v

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
  simp only [termValue, he, Bool.false_eq_true, ite_false]

theorem termValue_atEntry {ρ : Env} {h : Heap} {t : Term} (he : t.atEntry = true) :
    termValue ε ρ h t = termAt ε.env ε.heap t := by
  simp only [termValue, he, ite_true]

/-- At the entry state, `old(t)` denotes what `t` does. -/
theorem termValue_toNow {ρ : Env} {h : Heap} (hρ : ε.env = ρ) (hh : ε.heap = h) (t : Term) :
    termValue ε ρ h t.toNow = termValue ε ρ h t := by
  cases he : t.atEntry
  · obtain ⟨k, s, p, a⟩ := t; simp only at he; subst he; rfl
  · rw [termValue_now rfl, termValue_atEntry he]
    simp only [Term.toNow, termAt, hρ, hh]

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
  simp only [termValue, he, Bool.false_eq_true, ite_false, termAt, hs]

/-- **A term renamed by a total map of current slots denotes what it did**
where each current slot's image holds its value. -/
theorem termValue_mapM' {f : Nat → Nat} {ρ ρ' : Env} {h : Heap} {t : Term}
    (hf : t.atEntry = false → ρ' (f t.slot) = ρ t.slot) :
    termValue ε ρ' h (t.mapM' f) = termValue ε ρ h t := by
  obtain ⟨k, s, p, a⟩ := t
  cases a
  · exact termValue_slot (t := ⟨k, s, p, false⟩) (hf rfl) rfl
  · exact termValue_entry_invariant rfl

/-- A current term re-rooted at a slot holding its slot's value denotes what
it did. -/
theorem termValue_now_slot {ρ ρ' : Env} {h : Heap} {t : Term} {s : Nat} (hs : ρ' s = ρ t.slot)
    (he : t.atEntry = false) : termValue ε ρ' h (.now t.kind s t.path) = termValue ε ρ h t := by
  obtain ⟨k, s', p, a⟩ := t
  cases he
  exact termValue_slot (t := ⟨k, s', p, false⟩) hs rfl

/-- A term reads the current environment at its current slot only. -/
theorem termValue_congr {ρ ρ' : Env} {h : Heap} {t : Term} (hs : t.atEntry = false → ρ t.slot = ρ' t.slot) :
    termValue ε ρ h t = termValue ε ρ' h t := by
  cases he : t.atEntry
  · simp only [termValue, he, Bool.false_eq_true, ite_false, termAt, hs he]
  · exact termValue_entry_invariant he

/-- A term reads the entry environment at its entry slot only, and the
entry heap. -/
theorem termValue_congr_entry {ε' : EntryState} {ρ : Env} {h : Heap} {t : Term} (hh : ε.heap = ε'.heap)
    (hs : t.atEntry = true → ε.env t.slot = ε'.env t.slot) : termValue ε ρ h t = termValue ε' ρ h t := by
  cases he : t.atEntry
  · rw [termValue_now he, termValue_now he]
  · simp only [termValue, he, ite_true, termAt, hh, hs he]

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
    simp only [termValue, he, ite_true, termAt, hh, hg he _ hs]

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

/-- A heap extension keeps the length of what a value is: a spine lies in the
old heap. -/
theorem lengthOf_extend {h : Heap} (vs : List Val) {v : Val} {n : Int} (hl : lengthOf h v = some n) :
    lengthOf (h ++ vs) v = some n := by
  obtain ⟨s, ls, hs, hls, rfl, hm⟩ := lengthOf_spine hl
  exact lengthOf_of_spine hs (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hls).1, hls]) hm

/-- A term reading the environment alone denotes the same in every heap. -/
theorem termValue_envOnly {ρ : Env} {h h' : Heap} {t : Term} (ht : t.envOnly = true) :
    termValue ε ρ h t = termValue ε ρ h' t := by
  cases he : t.atEntry
  · obtain ⟨k, s, p, a⟩ := t
    simp only at he; subst he
    simp only [Term.envOnly, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      List.isEmpty_iff] at ht
    obtain ⟨hk, rfl⟩ := ht
    cases k <;> simp [Term.Kind.isNum] at hk <;> rfl
  · exact termValue_entry_invariant he

theorem kindValue_extend {h : Heap} (vs : List Val) {k : Term.Kind} {v : Val} {n : Int} (hk : kindValue h k v = some n) :
    kindValue (h ++ vs) k v = some n := by
  cases k with
  | value => exact hk
  | length => exact lengthOf_extend vs hk
  | view => exact hk
  | strLength => exact hk
  | bitMask _ => exact hk

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

/-- Map each variable in a linear form to either a target variable or an integer
constant, folding constants into the accumulated offset `k`. -/
def formMapVarsOrConst (f : V → Option (W ⊕ Int)) : Linear.Form V → Option (Linear.Form W × Int)
  | [] => some ([], 0)
  | (x, c) :: rest => do
    let (F', k) ← formMapVarsOrConst f rest
    match ← f x with
    | .inl y => pure ((y, c) :: F', k)
    | .inr v => pure (F', k + c * v)

/-- Map each variable in a linear fact to either a target variable or an integer
constant. -/
def factMapVarsOrConst (f : V → Option (W ⊕ Int)) : Linear.Fact V → Option (Linear.Fact W)
  | .le F d => (formMapVarsOrConst f F).map fun (F', k) => .le F' (d - k)
  | .ne F d => (formMapVarsOrConst f F).map fun (F', k) => .ne F' (d - k)

/-- Map each variable in a `LinearClause` to either a target variable or an
integer constant. -/
def mapVarsOrConst (f : V → Option (W ⊕ Int)) : LinearClause V → Option (LinearClause W)
  | .atom F => (factMapVarsOrConst f F).map .atom
  | .either A B => do pure (.either (← A.mapVarsOrConst f) (← B.mapVarsOrConst f))

private theorem formMapVarsOrConst_eval {f : V → Option (W ⊕ Int)}
    {val : V → Option Int} {val' : W → Option Int} :
    ∀ {F : Linear.Form V} {F' : Linear.Form W} {k : Int},
      formMapVarsOrConst f F = some (F', k) →
      (∀ x ∈ F.map (·.1),
        (∀ y, f x = some (.inl y) → val' y = val x) ∧
        (∀ v, f x = some (.inr v) → val x = some v)) →
      (Linear.Form.eval (fun w => (val' w).getD 0) F' + k = Linear.Form.eval (fun v => (val v).getD 0) F) ∧
      ((∀ y ∈ F'.map (·.1), (val' y).isSome) ↔ (∀ x ∈ F.map (·.1), (val x).isSome))
  | [], F', k, hm, _ => by
    simp only [formMapVarsOrConst, Option.some.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    simp [Linear.Form.eval]
  | (x, c) :: rest, F', k, hm, hf => by
    simp only [formMapVarsOrConst, Option.bind_eq_bind, Option.bind_eq_some_iff] at hm
    obtain ⟨⟨R', kr⟩, hR, o, ho, hres⟩ := hm
    have hrest := formMapVarsOrConst_eval hR fun z hz => hf z (List.mem_cons_of_mem _ hz)
    have hfx := hf x (List.mem_cons_self ..)
    cases o with
    | inl y =>
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hres
      obtain ⟨rfl, rfl⟩ := hres
      have hxy := hfx.1 y ho
      refine ⟨?_, ?_⟩
      · simp only [Linear.Form.eval, hxy]; omega
      · constructor
        · intro hall z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · rw [← hxy]; exact hall y (List.mem_cons_self ..)
          · exact hrest.2.mp (fun w hw => hall w (List.mem_cons_of_mem _ hw)) z hz
        · intro hall w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · rw [hxy]; exact hall x (List.mem_cons_self ..)
          · exact hrest.2.mpr (fun z hz => hall z (List.mem_cons_of_mem _ hz)) w hw
    | inr v =>
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hres
      obtain ⟨rfl, rfl⟩ := hres
      have hxv := hfx.2 v ho
      refine ⟨?_, ?_⟩
      · simp only [Linear.Form.eval, hxv, Option.getD_some]; omega
      · constructor
        · intro hall z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · simp [hxv]
          · exact hrest.2.mp hall z hz
        · intro hall w hw
          exact hrest.2.mpr (fun z hz => hall z (List.mem_cons_of_mem _ hz)) w hw

theorem factAt_mapVarsOrConst {f : V → Option (W ⊕ Int)} {val : V → Option Int} {val' : W → Option Int}
    {F : Linear.Fact V} {G : Linear.Fact W} (hm : factMapVarsOrConst f F = some G)
    (hf : ∀ x ∈ F.vars,
      (∀ y, f x = some (.inl y) → val' y = val x) ∧
      (∀ v, f x = some (.inr v) → val x = some v)) : FactAt val' G ↔ FactAt val F := by
  cases F with
  | le F d =>
    simp only [factMapVarsOrConst, Option.map_eq_some_iff] at hm
    obtain ⟨⟨F', k⟩, hF, rfl⟩ := hm
    obtain ⟨heval, hdef⟩ := formMapVarsOrConst_eval hF hf
    simp only [FactAt, Linear.Fact.vars, Linear.Fact.Holds]
    exact and_congr hdef (by omega)
  | ne F d =>
    simp only [factMapVarsOrConst, Option.map_eq_some_iff] at hm
    obtain ⟨⟨F', k⟩, hF, rfl⟩ := hm
    obtain ⟨heval, hdef⟩ := formMapVarsOrConst_eval hF hf
    simp only [FactAt, Linear.Fact.vars, Linear.Fact.Holds]
    exact and_congr hdef (by omega)

theorem holdsAt_mapVarsOrConst {f : V → Option (W ⊕ Int)} {val : V → Option Int} {val' : W → Option Int}
    {F : LinearClause V} {G : LinearClause W} (hm : F.mapVarsOrConst f = some G)
    (hf : ∀ x ∈ F.vars,
      (∀ y, f x = some (.inl y) → val' y = val x) ∧
      (∀ v, f x = some (.inr v) → val x = some v)) : G.HoldsAt val' ↔ F.HoldsAt val := by
  induction F generalizing G with
  | atom F =>
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.mp hm
    exact factAt_mapVarsOrConst hG hf
  | either A B ihA ihB =>
    simp only [mapVarsOrConst, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
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

/-- An affine index shift `Σ c·t + offset` added to a quantified index `i` (or
evaluated at `i = 0` as an affine element index). `⟨[], 0⟩` is unshifted `i`;
`⟨[(.value base, 1)], 0⟩` is `i + base`; `⟨[(.length a, 1)], -1⟩` is `|a| - 1`. -/
structure IndexShift where
  terms : Linear.Form Term := []
  offset : Int := 0
  deriving DecidableEq, Repr, Hashable

namespace IndexShift

def zero : IndexShift := ⟨[], 0⟩

def ofSlot (k : Nat) : IndexShift := ⟨[(.value k, 1)], 0⟩

def isZero (sh : IndexShift) : Bool := sh.terms.isEmpty && sh.offset == 0

def asSlot? (sh : IndexShift) : Option Nat :=
  if sh.offset == 0 then
    match sh.terms with
    | [(t, 1)] => if !t.atEntry && t.kind == .value && t.path.isEmpty then some t.slot else none
    | _ => none
  else none

def slots (sh : IndexShift) : List Nat := sh.terms.flatMap fun p => p.1.slots

def entrySlots (sh : IndexShift) : List Nat := sh.terms.flatMap fun p => p.1.entrySlots

def entryTerms (sh : IndexShift) : List Term :=
  sh.terms.filterMap fun p => if p.1.atEntry then some p.1 else none

def mapM (f : Nat → Option Nat) (sh : IndexShift) : Option IndexShift :=
  (sh.terms.mapM fun (p : Term × Int) => (p.1.mapM f).map (·, p.2)).map fun ts => ⟨ts, sh.offset⟩

def mapTotal (f : Nat → Nat) (sh : IndexShift) : IndexShift :=
  ⟨sh.terms.map fun p => (p.1.mapM' f, p.2), sh.offset⟩

def mapEntry (g : Nat → Option Nat) (sh : IndexShift) : Option IndexShift :=
  (sh.terms.mapM fun (p : Term × Int) => (p.1.mapEntry g).map (·, p.2)).map fun ts => ⟨ts, sh.offset⟩

def toNow (sh : IndexShift) : IndexShift :=
  ⟨sh.terms.map fun p => (p.1.toNow, p.2), sh.offset⟩

def reroot (now entry : Nat → Option (Nat × List String)) (sh : IndexShift) : Option IndexShift :=
  (sh.terms.mapM fun (p : Term × Int) => (p.1.reroot now entry).map (·, p.2)).map fun ts => ⟨ts, sh.offset⟩

def eval (ε : EntryState) (ρ : Env) (h : Heap) (i : Nat) (sh : IndexShift) : Option Nat :=
  if sh.terms.all fun p => (termValue ε ρ h p.1).isSome then
    let idx := (i : Int) + Linear.Form.eval (termValuation ε ρ h) sh.terms + sh.offset
    if 0 ≤ idx then some idx.toNat else none
  else none

@[simp] theorem eval_zero (ε : EntryState) (ρ : Env) (h : Heap) (i : Nat) :
    zero.eval ε ρ h i = some i := by
  simp [eval, zero, Linear.Form.eval]

@[simp] theorem isZero_zero : zero.isZero = true := rfl

theorem eq_zero_of_isZero {sh : IndexShift} (h : sh.isZero = true) : sh = zero := by
  obtain ⟨ts, off⟩ := sh
  simp only [isZero, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem eval_ofSlot {ε : EntryState} {ρ : Env} {h : Heap} {k i : Nat} :
    (ofSlot k).eval ε ρ h 0 = some i ↔ intValue (ρ k) = some (i : Int) := by
  simp only [eval, ofSlot, List.all_cons, List.all_nil, Bool.and_true, termValue_value,
    Linear.Form.eval, termValuation, Int.natCast_zero, Int.zero_add, Int.add_zero]
  cases hv : intValue (ρ k) with
  | none => simp
  | some z =>
    simp only [Option.isSome_some, ite_true, Option.getD_some, Option.some.injEq]
    constructor
    · intro h'
      split at h'
      · cases h'; omega
      · cases h'
    · intro h'; subst h'; simp

theorem eval_asSlot? {ε : EntryState} {ρ : Env} {h : Heap} {sh : IndexShift} {k i : Nat}
    (hs : sh.asSlot? = some k) :
    sh.eval ε ρ h 0 = some i ↔ intValue (ρ k) = some (i : Int) := by
  obtain ⟨ts, off⟩ := sh
  simp only [asSlot?] at hs
  split at hs
  · rename_i hoff
    have hoff' : off = 0 := beq_iff_eq.mp hoff
    subst hoff'
    cases ts with
    | nil => cases hs
    | cons p rest =>
      cases rest with
      | cons _ _ => simp at hs
      | nil =>
        obtain ⟨⟨kd, s, path, ae⟩, c⟩ := p
        by_cases hc : c = 1
        · subst hc
          simp only at hs
          split at hs
          · rename_i hcond
            simp only [Option.some.injEq] at hs; subst hs
            simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.isEmpty_iff] at hcond
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hcond
            exact eval_ofSlot
          · cases hs
        · simp [hc] at hs
  · cases hs

theorem eval_defines {ε : EntryState} {ρ : Env} {h : Heap} {i j : Nat} {sh : IndexShift}
    (he : sh.eval ε ρ h i = some j) : ∀ p ∈ sh.terms, (termValue ε ρ h p.1).isSome := by
  unfold eval at he
  split at he
  · rename_i hall
    exact fun p hp => List.all_eq_true.mp hall p hp
  · cases he

theorem eval_eq {ε : EntryState} {ρ : Env} {h : Heap} {i j : Nat} {sh : IndexShift}
    (he : sh.eval ε ρ h i = some j) :
    (j : Int) = (i : Int) + Linear.Form.eval (termValuation ε ρ h) sh.terms + sh.offset := by
  unfold eval at he
  split at he
  · dsimp only at he
    split at he
    · cases he; omega
    · cases he
  · cases he

theorem eval_of_eq {ε : EntryState} {ρ : Env} {h : Heap} {i j : Nat} {sh : IndexShift}
    (hdef : ∀ p ∈ sh.terms, (termValue ε ρ h p.1).isSome)
    (heq : (j : Int) = (i : Int) + Linear.Form.eval (termValuation ε ρ h) sh.terms + sh.offset) :
    sh.eval ε ρ h i = some j := by
  unfold eval
  have hall : (sh.terms.all fun p => (termValue ε ρ h p.1).isSome) = true := List.all_eq_true.mpr hdef
  simp only [hall, ite_true, ← heq, Int.natCast_nonneg, Int.toNat_natCast]

theorem eval_congr_term {ε ε' : EntryState} {ρ ρ' : Env} {h h' : Heap} {i : Nat} {sh : IndexShift}
    (ht : ∀ p ∈ sh.terms, termValue ε' ρ' h' p.1 = termValue ε ρ h p.1) :
    sh.eval ε' ρ' h' i = sh.eval ε ρ h i := by
  have hform : ∀ (ts : Linear.Form Term),
      (∀ p ∈ ts, termValue ε' ρ' h' p.1 = termValue ε ρ h p.1) →
      (ts.all fun p => (termValue ε' ρ' h' p.1).isSome) = (ts.all fun p => (termValue ε ρ h p.1).isSome) ∧
      Linear.Form.eval (termValuation ε' ρ' h') ts = Linear.Form.eval (termValuation ε ρ h) ts := by
    intro ts hts
    induction ts with
    | nil => simp [Linear.Form.eval]
    | cons p rest ih =>
      have hp := hts p (List.mem_cons_self ..)
      have ⟨ha, he⟩ := ih fun q hq => hts q (List.mem_cons_of_mem _ hq)
      simp only [List.all_cons, Linear.Form.eval, termValuation, hp, ha, he, and_self]
  obtain ⟨ha, he⟩ := hform sh.terms ht
  simp only [eval, ha, he]

theorem eval_frame {ε : EntryState} {ρ : Env} {h h' : Heap} {i j : Nat} {sh : IndexShift}
    (ht : ∀ p ∈ sh.terms, ∀ z, termValue ε ρ h p.1 = some z → termValue ε ρ h' p.1 = some z)
    (he : sh.eval ε ρ h i = some j) : sh.eval ε ρ h' i = some j := by
  have hdef := eval_defines he
  have hcongr : ∀ p ∈ sh.terms, termValue ε ρ h' p.1 = termValue ε ρ h p.1 := fun p hp => by
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp (hdef p hp)
    rw [hz, ht p hp z hz]
  rw [eval_congr_term hcongr]; exact he

theorem eval_extend {ε : EntryState} {ρ : Env} {h : Heap} (vs : List Val) {i j : Nat} {sh : IndexShift}
    (he : sh.eval ε ρ h i = some j) : sh.eval ε ρ (h ++ vs) i = some j :=
  eval_frame (fun _ _ _ hz => termValue_extend vs hz) he

private theorem mapM_list_total (f : Nat → Nat) :
    ∀ ts : Linear.Form Term,
      (ts.mapM fun (p : Term × Int) => (p.1.mapM (some ∘ f)).map (·, p.2)) = some (ts.map fun p => (p.1.mapM' f, p.2))
  | [] => rfl
  | p :: ts => by
    have h1 : p.1.mapM (some ∘ f) = some (p.1.mapM' f) := congrFun (Term.mapM_eq f) p.1
    simp only [List.mapM_cons, h1, Option.map_some, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      mapM_list_total f ts, List.map_cons]

theorem mapM_total (f : Nat → Nat) : IndexShift.mapM (some ∘ f) = some ∘ mapTotal f := by
  funext ⟨ts, off⟩
  simp [mapM, mapTotal, mapM_list_total]

private theorem eval_mapM_list {ε ε' : EntryState} {ρ ρ' : Env} {h : Heap}
    {m : Term → Option Term} :
    ∀ {ts ts' : Linear.Form Term},
      (ts.mapM fun p => (m p.1).map (·, p.2)) = some ts' →
      (∀ p ∈ ts, ∀ t', m p.1 = some t' → termValue ε' ρ' h t' = termValue ε ρ h p.1) →
      (ts'.all fun p => (termValue ε' ρ' h p.1).isSome) = (ts.all fun p => (termValue ε ρ h p.1).isSome) ∧
      Linear.Form.eval (termValuation ε' ρ' h) ts' = Linear.Form.eval (termValuation ε ρ h) ts
  | [], ts', hm, _ => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm
    subst hm; simp [Linear.Form.eval]
  | p :: ts, ts', hm, hf => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hm
    obtain ⟨q, ⟨t', ht', rfl⟩, rest', hrest, rfl⟩ := hm
    have h1 := hf p (List.mem_cons_self ..) t' ht'
    obtain ⟨ha, he⟩ := eval_mapM_list hrest fun r hr => hf r (List.mem_cons_of_mem _ hr)
    simp only [List.all_cons, Linear.Form.eval, termValuation, h1, ha, he, and_self]

theorem eval_mapM {ε : EntryState} {f : Nat → Option Nat} {ρ ρ' : Env} {h : Heap} {i : Nat}
    {sh sh' : IndexShift} (hm : sh.mapM f = some sh')
    (hf : ∀ s ∈ sh.slots, ∀ t, f s = some t → ρ' t = ρ s) :
    sh'.eval ε ρ' h i = sh.eval ε ρ h i := by
  obtain ⟨ts, off⟩ := sh
  simp only [mapM, Option.map_eq_some_iff] at hm
  obtain ⟨ts', hts, rfl⟩ := hm
  obtain ⟨ha, he⟩ := eval_mapM_list (ε := ε) (ε' := ε) (h := h) hts fun p hp t' ht' =>
    termValue_mapM ht' fun he' j hj =>
      hf p.1.slot (List.mem_flatMap.mpr ⟨p, hp, by simp [Term.slots, he']⟩) j hj
  simp only [eval, ha, he]

theorem eval_congr {ε : EntryState} {ρ ρ' : Env} {h : Heap} {i : Nat} {sh : IndexShift}
    (hs : ∀ s ∈ sh.slots, ρ s = ρ' s) : sh.eval ε ρ h i = sh.eval ε ρ' h i :=
  (eval_congr_term fun p hp =>
    (termValue_congr fun he => hs p.1.slot (List.mem_flatMap.mpr ⟨p, hp, by simp [Term.slots, he]⟩)).symm).symm

theorem eval_congr_entry {ε ε' : EntryState} {ρ : Env} {h : Heap} {i : Nat} {sh : IndexShift}
    (hh : ε.heap = ε'.heap) (hs : ∀ s ∈ sh.entrySlots, ε.env s = ε'.env s) :
    sh.eval ε ρ h i = sh.eval ε' ρ h i :=
  (eval_congr_term fun p hp =>
    (termValue_congr_entry hh fun he => hs p.1.slot (List.mem_flatMap.mpr ⟨p, hp, by simp [Term.entrySlots, he]⟩)).symm).symm

theorem eval_entry {ε ε' : EntryState} {ρ : Env} {h : Heap} {i : Nat} {sh : IndexShift}
    (hs : sh.entrySlots = []) : sh.eval ε ρ h i = sh.eval ε' ρ h i :=
  (eval_congr_term fun p hp => by
    cases he : p.1.atEntry
    · rw [termValue_now he, termValue_now he]
    · have := List.flatMap_eq_nil_iff.mp hs p hp
      simp [Term.entrySlots, he] at this).symm

theorem eval_mapEntry {ε ε' : EntryState} {g : Nat → Option Nat} {ρ : Env} {h : Heap} {i : Nat}
    {sh sh' : IndexShift} (hh : ε'.heap = ε.heap) (hm : sh.mapEntry g = some sh')
    (hg : ∀ s ∈ sh.entrySlots, ∀ j, g s = some j → ε'.env j = ε.env s) :
    sh'.eval ε' ρ h i = sh.eval ε ρ h i := by
  obtain ⟨ts, off⟩ := sh
  simp only [mapEntry, Option.map_eq_some_iff] at hm
  obtain ⟨ts', hts, rfl⟩ := hm
  obtain ⟨ha, he⟩ := eval_mapM_list (ε := ε) (ε' := ε') (ρ := ρ) (ρ' := ρ) (h := h) hts fun p hp t' ht' =>
    termValue_mapEntry ht' hh fun he' j hj =>
      hg p.1.slot (List.mem_flatMap.mpr ⟨p, hp, by simp [Term.entrySlots, he']⟩) j hj
  simp only [eval, ha, he]

theorem eval_congr_entryTerms {ε ε' : EntryState} {ρ : Env} {h : Heap} {i : Nat} {sh : IndexShift}
    (ht : ∀ t ∈ sh.entryTerms, termAt ε.env ε.heap t = termAt ε'.env ε'.heap t) :
    sh.eval ε ρ h i = sh.eval ε' ρ h i :=
  (eval_congr_term fun p hp => by
    cases he : p.1.atEntry
    · rw [termValue_now he, termValue_now he]
    · rw [termValue_atEntry he, termValue_atEntry he]
      exact (ht p.1 (List.mem_filterMap.mpr ⟨p, hp, by simp [he]⟩)).symm).symm

theorem eval_toNow {ε : EntryState} {ρ : Env} {h : Heap} (hρ : ε.env = ρ) (hh : ε.heap = h)
    {i : Nat} (sh : IndexShift) : sh.toNow.eval ε ρ h i = sh.eval ε ρ h i := by
  obtain ⟨ts, off⟩ := sh
  have haux : ∀ l : Linear.Form Term,
      ((l.map fun p => (p.1.toNow, p.2)).all fun p => (termValue ε ρ h p.1).isSome) =
        (l.all fun p => (termValue ε ρ h p.1).isSome) ∧
      Linear.Form.eval (termValuation ε ρ h) (l.map fun p => (p.1.toNow, p.2)) =
        Linear.Form.eval (termValuation ε ρ h) l := by
    intro l
    induction l with
    | nil => simp [Linear.Form.eval]
    | cons p rest ih =>
      simp only [List.map_cons, List.all_cons, Linear.Form.eval, termValuation,
        termValue_toNow hρ hh p.1, ih.1, ih.2, and_self]
  obtain ⟨ha, he⟩ := haux ts
  simp only [toNow, eval, ha, he]

theorem entrySlots_toNow (sh : IndexShift) : sh.toNow.entrySlots = [] := by
  simp only [toNow, entrySlots, List.flatMap_eq_nil_iff, List.mem_map]
  rintro _ ⟨p, -, rfl⟩
  simp [Term.entrySlots, Term.toNow]

end IndexShift

/-- A variable of the body of a quantified clause (ARITHMETIC.md,
"Quantified clauses"): the bound index, the element at it, an offset element,
a projection of the element, a projection of the element at a shifted index in
a parallel array, or a term. -/
inductive Bound where
  | index
  | elem
  | offset (delta : Nat)
  | project (kind : Term.Kind) (path : List String)
  | parallel (slot : Nat) (path : List String) (shift : IndexShift) (kind : Term.Kind) (elemPath : List String)
  | free (t : Term)
  deriving DecidableEq, Repr, Hashable

namespace Bound

/-- The variable with a term's slot renamed, where the map names one. -/
def mapM (f : Nat → Option Nat) : Bound → Option Bound
  | .index => some .index
  | .elem => some .elem
  | .offset d => some (.offset d)
  | .project k p => some (.project k p)
  | .parallel s p sh k ep => do pure (.parallel (← f s) p (← sh.mapM f) k ep)
  | .free t => (t.mapM f).map .free

/-- The variable with a term's slot renamed by a total map. -/
def mapTotal (f : Nat → Nat) : Bound → Bound
  | .index => .index
  | .elem => .elem
  | .offset d => .offset d
  | .project k p => .project k p
  | .parallel s p sh k ep => .parallel (f s) p (sh.mapTotal f) k ep
  | .free t => .free (t.mapM' f)

theorem mapM_total (f : Nat → Nat) : Bound.mapM (some ∘ f) = some ∘ mapTotal f := by
  funext b; cases b with
  | free t => simp only [Function.comp_apply, mapM, mapTotal, Term.mapM_eq]; rfl
  | parallel s p sh k ep =>
    have hsh : sh.mapM (some ∘ f) = some (sh.mapTotal f) := congrFun (IndexShift.mapM_total f) sh
    simp only [Function.comp_apply, mapM, mapTotal, hsh]; rfl
  | _ => rfl

/-- The term a variable denotes at an index `i` read of the slot `k` whose
element is the slot `r`'s value. -/
def inst (k r : Nat) : Bound → Term
  | .index => .value k
  | .elem => .value r
  | .offset _ => .value r
  | .project k p => ⟨k, r, p, false⟩
  | .parallel _ _ _ k ep => ⟨k, r, ep, false⟩
  | .free t => t

/-- The slots of the terms a variable names. -/
def slots : Bound → List Nat
  | .parallel s _ sh _ _ => s :: sh.slots
  | .free t => t.slots
  | _ => []

/-- The entry slots a variable names. -/
def entrySlots : Bound → List Nat
  | .parallel _ _ sh _ _ => sh.entrySlots
  | .free t => t.entrySlots
  | _ => []

/-- The entry terms a variable names. -/
def entryTerms : Bound → List Term
  | .parallel _ _ sh _ _ => sh.entryTerms
  | .free t => if t.atEntry then [t] else []
  | _ => []

/-- The variable with a term's entry slot translated, where the map names
one (`Term.mapEntry`). -/
def mapEntry (g : Nat → Option Nat) : Bound → Option Bound
  | .parallel s p sh k ep => (sh.mapEntry g).map fun sh' => .parallel s p sh' k ep
  | .free t => (t.mapEntry g).map .free
  | b => some b

end Bound

/-- The element value tested by an element guard inside a quantified clause:
the quantified array's own element at `i` (with optional field path `elemPath`),
or the element at a shifted index `i + shift` of a parallel array read at `(slot, path)`. -/
inductive ElemTarget where
  | self (elemPath : List String)
  | parallel (slot : Nat) (path : List String) (shift : IndexShift) (elemPath : List String)
  deriving DecidableEq, Repr, Hashable

namespace ElemTarget

/-- Whether the target is the quantified array's own element read with no
field path, `xs[i]`. JavaScript evaluates that read at every index of an
array (a hole and an index past the end read `undefined`), so it cannot
fail; a field step (`xs[i].f`) fails on a nullish element and a parallel
array's read (`ys[i]`) fails on a nullish base. -/
def ownElement : ElemTarget → Bool
  | .self [] => true
  | _ => false

def slots : ElemTarget → List Nat
  | .self _ => []
  | .parallel s _ sh _ => s :: sh.slots

def entrySlots : ElemTarget → List Nat
  | .self _ => []
  | .parallel _ _ sh _ => sh.entrySlots

def entryTerms : ElemTarget → List Term
  | .self _ => []
  | .parallel _ _ sh _ => sh.entryTerms

def mapM (f : Nat → Option Nat) : ElemTarget → Option ElemTarget
  | .self ep => some (.self ep)
  | .parallel s p sh ep => do pure (.parallel (← f s) p (← sh.mapM f) ep)

theorem mapM_ownElement {f : Nat → Option Nat} {t t' : ElemTarget} (h : t.mapM f = some t') :
    t'.ownElement = t.ownElement := by
  cases t with
  | self ep => cases h; rfl
  | parallel s p sh ep =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; rfl

def mapTotal (f : Nat → Nat) : ElemTarget → ElemTarget
  | .self ep => .self ep
  | .parallel s p sh ep => .parallel (f s) p (sh.mapTotal f) ep

theorem mapM_total (f : Nat → Nat) : ElemTarget.mapM (some ∘ f) = some ∘ mapTotal f := by
  funext t; cases t with
  | self _ => rfl
  | parallel s p sh ep =>
    have hsh : sh.mapM (some ∘ f) = some (sh.mapTotal f) := congrFun (IndexShift.mapM_total f) sh
    simp only [Function.comp_apply, mapM, mapTotal, hsh]; rfl

def mapEntry (g : Nat → Option Nat) : ElemTarget → Option ElemTarget
  | .self ep => some (.self ep)
  | .parallel s p sh ep => (sh.mapEntry g).map fun sh' => .parallel s p sh' ep

def toNow : ElemTarget → ElemTarget
  | .self ep => .self ep
  | .parallel s p sh ep => .parallel s p sh.toNow ep

/-- The value an element guard reads at index `i` of spine elements `ls`. -/
def read (ε : EntryState) (ρ : Env) (h : Heap) (ls : List (Option Nat)) (i : Nat) : ElemTarget → Option Val
  | .self ep => match ls[i]? with
    | some (some l) => h[l]?.bind fun v => readGuard h v ep
    | _ => none
  | .parallel s p sh ep => match sh.eval ε ρ h i with
    | some j => match readPath h (ρ s) p with
      | some a => match elementsOf a with
        | some st => match h[st]?.bind spineEntries with
          | some ls' => match ls'[j]? with
            | some (some l) => h[l]?.bind fun v => readGuard h v ep
            | _ => none
          | none => none
        | none => none
      | none => none
    | none => none

end ElemTarget

/-- A body clause of a quantified fact (`IndexFact.every`): a linear clause over
bound variables, one guarded by a tag test on an element (`xs[i] === null || …`,
`ys[i + shift] === null || …`), or a disjunction of two body clauses. -/
inductive BodyClause where
  | clause (c : LinearClause Bound)
  | guarded (target : ElemTarget) (tag : GuardTag) (body : BodyClause)
  | either (left right : BodyClause)
  deriving DecidableEq, Repr, Hashable

namespace BodyClause

def slots : BodyClause → List Nat
  | .clause c => c.vars.flatMap Bound.slots
  | .guarded t _ b => t.slots ++ b.slots
  | .either a b => a.slots ++ b.slots

def entrySlots : BodyClause → List Nat
  | .clause c => c.vars.flatMap Bound.entrySlots
  | .guarded t _ b => t.entrySlots ++ b.entrySlots
  | .either a b => a.entrySlots ++ b.entrySlots

def entryTerms : BodyClause → List Term
  | .clause c => c.vars.flatMap Bound.entryTerms
  | .guarded t _ b => t.entryTerms ++ b.entryTerms
  | .either a b => a.entryTerms ++ b.entryTerms

def mapM (f : Nat → Option Nat) : BodyClause → Option BodyClause
  | .clause c => (c.mapVars (Bound.mapM f)).map .clause
  | .guarded t g b => do pure (.guarded (← t.mapM f) g (← b.mapM f))
  | .either a b => do pure (.either (← a.mapM f) (← b.mapM f))

theorem mapM_some (f : Nat → Nat) : ∀ b : BodyClause, ∃ b', b.mapM (some ∘ f) = some b'
  | .clause c => by
    obtain ⟨c', hc⟩ := LinearClause.mapVars_some (Bound.mapTotal f) c
    exact ⟨.clause c', by simp only [mapM, Bound.mapM_total, hc, Option.map_some]⟩
  | .guarded t g b => by
    obtain ⟨b', hb⟩ := mapM_some f b
    exact ⟨.guarded (t.mapTotal f) g b', by simp only [mapM, ElemTarget.mapM_total, hb]; rfl⟩
  | .either a b => by
    obtain ⟨a', ha⟩ := mapM_some f a
    obtain ⟨b', hb⟩ := mapM_some f b
    exact ⟨.either a' b', by simp only [mapM, ha, hb]; rfl⟩

def mapEntry (g : Nat → Option Nat) : BodyClause → Option BodyClause
  | .clause c => (c.mapVars (Bound.mapEntry g)).map .clause
  | .guarded t tg b => do pure (.guarded (← t.mapEntry g) tg (← b.mapEntry g))
  | .either a b => do pure (.either (← a.mapEntry g) (← b.mapEntry g))

def toNow (bt : Bound → Bound) : BodyClause → BodyClause
  | .clause c => .clause ((c.mapVars (some ∘ bt)).getD c)
  | .guarded t g b => .guarded t.toNow g (b.toNow bt)
  | .either a b => .either (a.toNow bt) (b.toNow bt)

end BodyClause


/-- A heap extension keeps what a spine location lists. -/
theorem spineEntries_extend {h : Heap} (vs : List Val) {s : Nat} {ls : List (Option Nat)}
    (hs : h[s]?.bind spineEntries = some ls) : (h ++ vs)[s]?.bind spineEntries = some ls := by
  obtain ⟨u, hu, he⟩ := Option.bind_eq_some_iff.mp hs
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hu).1, hu]; exact he

/-- An array's spine is the spine of elements it holds. -/
theorem elementsOf_spine {v : Val} {s : Nat} (h : Footprints.spineOf v = some s) : elementsOf v = some s := by
  simp only [Footprints.spineOf] at h
  cases v <;> simp_all [elementsOf, Footprints.fieldsOf]

/-- The safe integer the element at index `i` of the spine elements `ls` is,
where it is present and one. -/
def elementInt (h : Heap) (ls : List (Option Nat)) (i : Nat) : Option Int :=
  match ls[i]? with
  | some (some l) => h[l]?.bind intValue
  | _ => none

/-- Every listed element cell is allocated below `b`. This describes a
particular spine view; a later spine replacement needs a new proof. -/
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

/-- What a body variable denotes at the index `i` of the spine elements `ls`. -/
def boundValue (ε : EntryState) (ρ : Env) (h : Heap) (ls : List (Option Nat)) (i : Nat) : Bound → Option Int
  | .index => some (i : Int)
  | .elem => elementInt h ls i
  | .offset d => elementInt h ls (i + d)
  | .project k p => match ls[i]? with
    | some (some l) => h[l]?.bind fun v => termValue ε (fun _ => v) h ⟨k, 0, p, false⟩
    | _ => none
  | .parallel s p sh k ep => match sh.eval ε ρ h i with
    | some j => match readPath h (ρ s) p with
      | some a => match elementsOf a with
        | some st => match h[st]?.bind spineEntries with
          | some ls' => match ls'[j]? with
            | some (some l) => h[l]?.bind fun v => termValue ε (fun _ => v) h ⟨k, 0, ep, false⟩
            | _ => none
          | none => none
        | none => none
      | none => none
    | none => none
  | .free t => termValue ε ρ h t

/-- Whether a body clause holds at index `i` of spine elements `ls`. A guarded
clause `t === g || b` holds as JavaScript evaluates it: the guard's read
yields a value satisfying `g`, or the read evaluates and `b` holds. The read
evaluates where it yields a value; the quantified array's own element `xs[i]`
evaluates at every index (`ElemTarget.ownElement`). -/
def BodyClause.HoldsAt (ε : EntryState) (ρ : Env) (h : Heap) (ls : List (Option Nat)) (i : Nat) : BodyClause → Prop
  | .clause c => c.HoldsAt (boundValue ε ρ h ls i)
  | .guarded t g b =>
    (∃ w, t.read ε ρ h ls i = some w ∧ g.holds w) ∨
    ((t.ownElement = false → ∃ w, t.read ε ρ h ls i = some w) ∧ b.HoldsAt ε ρ h ls i)
  | .either a b => a.HoldsAt ε ρ h ls i ∨ b.HoldsAt ε ρ h ls i

theorem ElemTarget.read_extend {h : Heap} (vs : List Val) {ρ : Env} {ls : List (Option Nat)} {i : Nat}
    {t : ElemTarget} {w : Val} (hr : t.read ε ρ h ls i = some w) : t.read ε ρ (h ++ vs) ls i = some w := by
  cases t with
  | self ep =>
    simp only [ElemTarget.read] at hr ⊢
    split at hr
    · rename_i l _
      obtain ⟨v, hv, hg⟩ := Option.bind_eq_some_iff.mp hr
      exact Option.bind_eq_some_iff.mpr ⟨v, by
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv,
        readGuard_extend vs hg⟩
    · cases hr
  | parallel s p sh ep =>
    simp only [ElemTarget.read] at hr ⊢
    cases hsh : sh.eval ε ρ h i with
    | none => simp [hsh] at hr
    | some j =>
      simp only [hsh, IndexShift.eval_extend vs hsh] at hr ⊢
      cases hp : readPath h (ρ s) p with
      | none => simp [hp] at hr
      | some a =>
        simp only [hp, readPath_extend vs hp] at hr ⊢
        cases he : elementsOf a with
        | none => simp [he] at hr
        | some st =>
          simp only [he] at hr ⊢
          cases hs : h[st]?.bind spineEntries with
          | none => simp [hs] at hr
          | some ls' =>
            simp only [hs, spineEntries_extend vs hs] at hr ⊢
            split at hr
            · rename_i l _
              obtain ⟨v, hv, hg⟩ := Option.bind_eq_some_iff.mp hr
              exact Option.bind_eq_some_iff.mpr ⟨v, by
                rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv,
                readGuard_extend vs hg⟩
            · cases hr

theorem boundValue_extend {h : Heap} (vs : List Val) {ρ : Env} {ls : List (Option Nat)} {i : Nat}
    {x : Bound} {m : Int} (hm : boundValue ε ρ h ls i x = some m) :
    boundValue ε ρ (h ++ vs) ls i x = some m := by
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
  | parallel s p sh k ep =>
    simp only [boundValue] at hm ⊢
    cases hsh : sh.eval ε ρ h i with
    | none => simp [hsh] at hm
    | some j =>
      simp only [hsh, IndexShift.eval_extend vs hsh] at hm ⊢
      cases hp : readPath h (ρ s) p with
      | none => simp [hp] at hm
      | some a =>
        simp only [hp, readPath_extend vs hp] at hm ⊢
        cases he : elementsOf a with
        | none => simp [he] at hm
        | some st =>
          simp only [he] at hm ⊢
          cases hs : h[st]?.bind spineEntries with
          | none => simp [hs] at hm
          | some ls' =>
            simp only [hs, spineEntries_extend vs hs] at hm ⊢
            split at hm
            · rename_i l _
              obtain ⟨v, hv, ht⟩ := Option.bind_eq_some_iff.mp hm
              exact Option.bind_eq_some_iff.mpr ⟨v, by
                rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv,
                termValue_extend vs ht⟩
            · cases hm
  | free t => exact termValue_extend (ε := ε) vs hm

theorem BodyClause.holdsAt_extend {h : Heap} (vs : List Val) {ρ : Env} {ls : List (Option Nat)} {i : Nat} :
    ∀ {B : BodyClause}, B.HoldsAt ε ρ h ls i → B.HoldsAt ε ρ (h ++ vs) ls i
  | .clause _, hB => LinearClause.holdsAt_extend (fun _ _ _ hm => boundValue_extend vs hm) hB
  | .guarded t _ _, .inl ⟨w, hw, hg⟩ => .inl ⟨w, t.read_extend vs hw, hg⟩
  | .guarded t _ _, .inr ⟨hp, hb⟩ => .inr ⟨fun hne => let ⟨w, hw⟩ := hp hne; ⟨w, t.read_extend vs hw⟩, holdsAt_extend vs hb⟩
  | .either _ _, hB => hB.imp (holdsAt_extend vs) (holdsAt_extend vs)

theorem BodyClause.holdsAt_mapM {f : Nat → Option Nat} {ρ ρ' : Env} {h : Heap} {ls : List (Option Nat)} {i : Nat} :
    ∀ {B B' : BodyClause}, B.mapM f = some B' →
      (∀ s ∈ B.slots, ∀ t, f s = some t → ρ' t = ρ s) →
      (B'.HoldsAt ε ρ' h ls i ↔ B.HoldsAt ε ρ h ls i)
  | .clause c, B', hm, hf => by
    obtain ⟨c', hc, rfl⟩ := Option.map_eq_some_iff.mp hm
    refine LinearClause.holdsAt_mapVars hc fun x hx y hy => ?_
    cases x with
    | index => cases hy; rfl
    | elem => cases hy; rfl
    | offset _ => cases hy; rfl
    | project _ _ => cases hy; rfl
    | parallel s p sh k ep =>
      simp only [Bound.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hy
      obtain ⟨s', hs', sh', hsh', rfl⟩ := hy
      have hρ := hf s (List.mem_flatMap.mpr ⟨.parallel s p sh k ep, hx, by simp [Bound.slots]⟩) s' hs'
      have hsh := IndexShift.eval_mapM (ε := ε) (h := h) (i := i) hsh' fun z hz =>
        hf z (List.mem_flatMap.mpr ⟨.parallel s p sh k ep, hx, by simp [Bound.slots, hz]⟩)
      simp only [boundValue, hρ, hsh]
    | free t =>
      obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp hy
      simp only [boundValue]
      refine termValue_mapM ht' fun he j hj => hf t.slot
        (List.mem_flatMap.mpr ⟨.free t, hx, by simp [Bound.slots, Term.slots, he]⟩) j hj
  | .guarded t g b, B', hm, hf => by
    simp only [BodyClause.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨t', ht, b', hb, rfl⟩ := hm
    have htr : t'.read ε ρ' h ls i = t.read ε ρ h ls i := by
      cases t with
      | self ep => cases ht; rfl
      | parallel s p sh ep =>
        simp only [ElemTarget.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at ht
        obtain ⟨s', hs', sh', hsh', rfl⟩ := ht
        have hρ := hf s (List.mem_append_left _ (by simp [ElemTarget.slots])) s' hs'
        have hsh := IndexShift.eval_mapM (ε := ε) (h := h) (i := i) hsh' fun z hz =>
          hf z (List.mem_append_left _ (by simp [ElemTarget.slots, hz]))
        simp only [ElemTarget.read, hρ, hsh]
    have hep := ElemTarget.mapM_ownElement ht
    have ih := holdsAt_mapM (h := h) (ls := ls) (i := i) hb (fun s hs => hf s (List.mem_append_right _ hs))
    simp only [BodyClause.HoldsAt, htr, hep, ih]
  | .either a b, B', hm, hf => by
    simp only [BodyClause.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨a', ha, b', hb, rfl⟩ := hm
    have iha := holdsAt_mapM (h := h) (ls := ls) (i := i) ha (fun s hs => hf s (List.mem_append_left _ hs))
    have ihb := holdsAt_mapM (h := h) (ls := ls) (i := i) hb (fun s hs => hf s (List.mem_append_right _ hs))
    exact or_congr iha ihb

theorem BodyClause.holdsAt_congr {ρ ρ' : Env} {h : Heap} {ls : List (Option Nat)} {i : Nat} :
    ∀ {B : BodyClause}, (∀ s ∈ B.slots, ρ s = ρ' s) →
      (B.HoldsAt ε ρ h ls i ↔ B.HoldsAt ε ρ' h ls i)
  | .clause c, hs => by
    have hb : ∀ x ∈ c.vars, boundValue ε ρ' h ls i x = boundValue ε ρ h ls i x := by
      intro x hx
      cases x with
      | index | elem | offset _ | project _ _ => rfl
      | parallel s p sh k ep =>
        have hρ := hs s (List.mem_flatMap.mpr ⟨.parallel s p sh k ep, hx, by simp [Bound.slots]⟩)
        have hsh := IndexShift.eval_congr (ε := ε) (h := h) (i := i) (sh := sh) fun z hz =>
          hs z (List.mem_flatMap.mpr ⟨.parallel s p sh k ep, hx, by simp [Bound.slots, hz]⟩)
        simp only [boundValue, hρ, hsh]
      | free t =>
        simp only [boundValue]
        exact (termValue_congr fun he => hs t.slot
          (List.mem_flatMap.mpr ⟨.free t, hx, by simp [Bound.slots, Term.slots, he]⟩)).symm
    exact ⟨LinearClause.holdsAt_congr hb, LinearClause.holdsAt_congr fun x hx => (hb x hx).symm⟩
  | .guarded t g b, hs => by
    have htr : t.read ε ρ h ls i = t.read ε ρ' h ls i := by
      cases t with
      | self ep => rfl
      | parallel s p sh ep =>
        have hρ := hs s (List.mem_append_left _ (by simp [ElemTarget.slots]))
        have hsh := IndexShift.eval_congr (ε := ε) (h := h) (i := i) (sh := sh) fun z hz =>
          hs z (List.mem_append_left _ (by simp [ElemTarget.slots, hz]))
        simp only [ElemTarget.read, hρ, hsh]
    have ih := holdsAt_congr (h := h) (ls := ls) (i := i) (B := b)
      (fun s hsb => hs s (List.mem_append_right _ hsb))
    simp only [BodyClause.HoldsAt, htr, ih]
  | .either a b, hs =>
    or_congr (holdsAt_congr (B := a) fun s h => hs s (List.mem_append_left _ h))
      (holdsAt_congr (B := b) fun s h => hs s (List.mem_append_right _ h))

private theorem boundValue_parallel_entry {ε' : EntryState} {ρ : Env} {h : Heap} {ls : List (Option Nat)}
    {i s : Nat} {p ep : List String} {sh sh' : IndexShift} {k : Term.Kind}
    (hsh : sh'.eval ε' ρ h i = sh.eval ε ρ h i) :
    boundValue ε' ρ h ls i (.parallel s p sh' k ep) = boundValue ε ρ h ls i (.parallel s p sh k ep) := by
  simp only [boundValue, hsh, termValue, termAt, Bool.false_eq_true, ite_false]

private theorem elemTarget_parallel_entry {ε' : EntryState} {ρ : Env} {h : Heap} {ls : List (Option Nat)}
    {i s : Nat} {p ep : List String} {sh sh' : IndexShift}
    (hsh : sh'.eval ε' ρ h i = sh.eval ε ρ h i) :
    (ElemTarget.parallel s p sh' ep).read ε' ρ h ls i = (ElemTarget.parallel s p sh ep).read ε ρ h ls i := by
  simp only [ElemTarget.read, hsh]

private theorem boundValue_project_entry {ε' : EntryState} {ρ : Env} {h : Heap} {ls : List (Option Nat)}
    {i : Nat} {k : Term.Kind} {p : List String} :
    boundValue ε' ρ h ls i (.project k p) = boundValue ε ρ h ls i (.project k p) := by
  simp only [boundValue]
  split
  · rename_i l _
    cases h[l]? with
    | none => rfl
    | some v => simp only [Option.bind_some]; rw [termValue_now rfl, termValue_now rfl]
  · rfl

theorem BodyClause.holdsAt_congr_entry {ε' : EntryState} {ρ : Env} {h : Heap} {ls : List (Option Nat)} {i : Nat}
    (hh : ε.heap = ε'.heap) :
    ∀ {B : BodyClause}, (∀ s ∈ B.entrySlots, ε.env s = ε'.env s) →
      (B.HoldsAt ε ρ h ls i ↔ B.HoldsAt ε' ρ h ls i)
  | .clause c, hs => by
    have hb : ∀ x ∈ c.vars, boundValue ε' ρ h ls i x = boundValue ε ρ h ls i x := by
      intro x hx
      cases x with
      | free t =>
        simp only [boundValue]
        exact (termValue_congr_entry hh fun he => hs t.slot
          (List.mem_flatMap.mpr ⟨.free t, hx, by simp [Bound.entrySlots, Term.entrySlots, he]⟩)).symm
      | project k p => exact boundValue_project_entry
      | parallel s p sh k ep =>
        refine boundValue_parallel_entry (IndexShift.eval_congr_entry hh fun z hz =>
          hs z (List.mem_flatMap.mpr ⟨.parallel s p sh k ep, hx, by simp [Bound.entrySlots, hz]⟩)).symm
      | _ => rfl
    exact ⟨LinearClause.holdsAt_congr hb, LinearClause.holdsAt_congr fun x hx => (hb x hx).symm⟩
  | .guarded t g b, hs => by
    have htr : t.read ε ρ h ls i = t.read ε' ρ h ls i := by
      cases t with
      | self _ => rfl
      | parallel s p sh ep =>
        exact (elemTarget_parallel_entry (IndexShift.eval_congr_entry hh fun z hz =>
          hs z (List.mem_append_left _ hz)).symm).symm
    have ih := holdsAt_congr_entry (ε' := ε') (ρ := ρ) (h := h) (ls := ls) (i := i) (B := b) hh
      (fun s hsb => hs s (List.mem_append_right _ hsb))
    simp only [BodyClause.HoldsAt, htr, ih]
  | .either a b, hs =>
    or_congr (holdsAt_congr_entry (ε' := ε') (B := a) hh fun s h => hs s (List.mem_append_left _ h))
      (holdsAt_congr_entry (ε' := ε') (B := b) hh fun s h => hs s (List.mem_append_right _ h))

theorem BodyClause.holdsAt_entry {ε' : EntryState} {ρ : Env} {h : Heap} {ls : List (Option Nat)} {i : Nat} :
    ∀ {B : BodyClause}, B.entrySlots = [] → (B.HoldsAt ε ρ h ls i ↔ B.HoldsAt ε' ρ h ls i)
  | .clause c, hB => by
    have hb : ∀ x ∈ c.vars, boundValue ε' ρ h ls i x = boundValue ε ρ h ls i x := by
      intro x hx
      cases x with
      | free t =>
        simp only [boundValue]
        cases he : t.atEntry
        · rw [termValue_now he, termValue_now he]
        · have := List.flatMap_eq_nil_iff.mp hB (.free t) hx; simp [Bound.entrySlots, Term.entrySlots, he] at this
      | project k p => exact boundValue_project_entry
      | parallel s p sh k ep =>
        have hnil : sh.entrySlots = [] := List.flatMap_eq_nil_iff.mp hB (.parallel s p sh k ep) hx
        exact boundValue_parallel_entry (IndexShift.eval_entry hnil).symm
      | _ => rfl
    exact ⟨LinearClause.holdsAt_congr hb, LinearClause.holdsAt_congr fun x hx => (hb x hx).symm⟩
  | .guarded t g b, hB => by
    simp only [entrySlots, List.append_eq_nil_iff] at hB
    have htr : t.read ε ρ h ls i = t.read ε' ρ h ls i := by
      cases t with
      | self _ => rfl
      | parallel s p sh ep =>
        exact (elemTarget_parallel_entry (IndexShift.eval_entry hB.1).symm).symm
    have ih := holdsAt_entry (ε' := ε') (ρ := ρ) (h := h) (ls := ls) (i := i) (B := b) hB.2
    simp only [BodyClause.HoldsAt, htr, ih]
  | .either a b, hB => by
    obtain ⟨ha, hb⟩ := List.append_eq_nil_iff.mp hB
    exact or_congr (holdsAt_entry (ε' := ε') (B := a) ha) (holdsAt_entry (ε' := ε') (B := b) hb)

theorem BodyClause.holdsAt_mapEntry {g : Nat → Option Nat} {ε' : EntryState} {ρ : Env} {h : Heap}
    {ls : List (Option Nat)} {i : Nat} (hh : ε'.heap = ε.heap) :
    ∀ {B B' : BodyClause}, B.mapEntry g = some B' →
      (∀ s ∈ B.entrySlots, ∀ j, g s = some j → ε'.env j = ε.env s) →
      (B'.HoldsAt ε' ρ h ls i ↔ B.HoldsAt ε ρ h ls i)
  | .clause c, B', hm, hg => by
    obtain ⟨c', hc, rfl⟩ := Option.map_eq_some_iff.mp hm
    refine LinearClause.holdsAt_mapVars hc fun x hx y hy => ?_
    cases x with
    | free t =>
      obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp hy
      simp only [boundValue]
      exact termValue_mapEntry ht' hh fun he j hj => hg t.slot
        (List.mem_flatMap.mpr ⟨.free t, hx, by simp [Bound.entrySlots, Term.entrySlots, he]⟩) j hj
    | project k p => cases hy; exact boundValue_project_entry
    | parallel s p sh k ep =>
      obtain ⟨sh', hsh', rfl⟩ := Option.map_eq_some_iff.mp hy
      exact boundValue_parallel_entry (IndexShift.eval_mapEntry hh hsh' fun z hz =>
        hg z (List.mem_flatMap.mpr ⟨.parallel s p sh k ep, hx, by simp [Bound.entrySlots, hz]⟩))
    | _ => cases hy; rfl
  | .guarded t tg b, B', hm, hg => by
    simp only [BodyClause.mapEntry, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨t', ht', b', hb, rfl⟩ := hm
    have hown : t'.ownElement = t.ownElement := by
      cases t with
      | self _ => cases ht'; rfl
      | parallel s p sh ep =>
        obtain ⟨sh', _, rfl⟩ := Option.map_eq_some_iff.mp ht'; rfl
    have htr : t'.read ε' ρ h ls i = t.read ε ρ h ls i := by
      cases t with
      | self _ => cases ht'; rfl
      | parallel s p sh ep =>
        obtain ⟨sh', hsh', rfl⟩ := Option.map_eq_some_iff.mp ht'
        exact elemTarget_parallel_entry (IndexShift.eval_mapEntry hh hsh' fun z hz =>
          hg z (List.mem_append_left _ hz))
    have ih := holdsAt_mapEntry (ε' := ε') (ρ := ρ) (h := h) (ls := ls) (i := i) hh hb
      (fun s hs => hg s (List.mem_append_right _ hs))
    simp only [BodyClause.HoldsAt, htr, hown, ih]
  | .either a b, B', hm, hg => by
    simp only [BodyClause.mapEntry, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨a', ha, b', hb, rfl⟩ := hm
    exact or_congr (holdsAt_mapEntry (ε' := ε') hh ha fun s h => hg s (List.mem_append_left _ h))
      (holdsAt_mapEntry (ε' := ε') hh hb fun s h => hg s (List.mem_append_right _ h))

theorem BodyClause.holdsAt_congr_entryTerms {ε' : EntryState} {ρ : Env} {h : Heap} {ls : List (Option Nat)} {i : Nat} :
    ∀ {B : BodyClause}, (∀ t ∈ B.entryTerms, termAt ε.env ε.heap t = termAt ε'.env ε'.heap t) →
      (B.HoldsAt ε ρ h ls i ↔ B.HoldsAt ε' ρ h ls i)
  | .clause c, ht => by
    have hb : ∀ x ∈ c.vars, boundValue ε' ρ h ls i x = boundValue ε ρ h ls i x := by
      intro x hx
      cases x with
      | free t =>
        simp only [boundValue]
        cases he : t.atEntry
        · rw [termValue_now he, termValue_now he]
        · rw [termValue_atEntry he, termValue_atEntry he]
          exact (ht t (List.mem_flatMap.mpr ⟨.free t, hx, by simp [Bound.entryTerms, he]⟩)).symm
      | project k p => exact boundValue_project_entry
      | parallel s p sh k ep =>
        exact boundValue_parallel_entry (IndexShift.eval_congr_entryTerms fun t htm =>
          ht t (List.mem_flatMap.mpr ⟨.parallel s p sh k ep, hx, by simp [Bound.entryTerms, htm]⟩)).symm
      | _ => rfl
    exact ⟨LinearClause.holdsAt_congr hb, LinearClause.holdsAt_congr fun x hx => (hb x hx).symm⟩
  | .guarded t g b, ht => by
    have htr : t.read ε ρ h ls i = t.read ε' ρ h ls i := by
      cases t with
      | self _ => rfl
      | parallel s p sh ep =>
        exact (elemTarget_parallel_entry (IndexShift.eval_congr_entryTerms fun tm htm =>
          ht tm (List.mem_append_left _ htm)).symm).symm
    have ih := holdsAt_congr_entryTerms (ε' := ε') (ρ := ρ) (h := h) (ls := ls) (i := i) (B := b)
      (fun tm htm => ht tm (List.mem_append_right _ htm))
    simp only [BodyClause.HoldsAt, htr, ih]
  | .either a b, ht =>
    or_congr (holdsAt_congr_entryTerms (ε' := ε') (B := a) fun t h => ht t (List.mem_append_left _ h))
      (holdsAt_congr_entryTerms (ε' := ε') (B := b) fun t h => ht t (List.mem_append_right _ h))

/-- All guard targets named in a body clause. -/
def BodyClause.targets : BodyClause → List ElemTarget
  | .clause _ => []
  | .guarded t _ b => t :: b.targets
  | .either a b => a.targets ++ b.targets

/-- All bound variables named in a body clause's linear clause. -/
def BodyClause.vars : BodyClause → List Bound
  | .clause c => c.vars
  | .guarded _ _ b => b.vars
  | .either a b => a.vars ++ b.vars

theorem BodyClause.holdsAt_frame {ρ : Env} {h h' : Heap} {ls ls' : List (Option Nat)} {i : Nat} :
    ∀ {B : BodyClause},
      (∀ t ∈ B.targets, ∀ w, t.read ε ρ h ls i = some w → t.read ε ρ h' ls' i = some w) →
      (∀ b ∈ B.vars, ∀ z, boundValue ε ρ h ls i b = some z → boundValue ε ρ h' ls' i b = some z) →
      B.HoldsAt ε ρ h ls i → B.HoldsAt ε ρ h' ls' i
  | .clause _, _, hb, hB => LinearClause.holdsAt_extend hb hB
  | .guarded t _ _, ht, _, .inl ⟨w, hw, hg⟩ =>
    .inl ⟨w, ht t (List.mem_cons_self ..) w hw, hg⟩
  | .guarded t _ _, ht, hb, .inr ⟨hp, hB⟩ =>
    .inr ⟨fun hne => let ⟨w, hw⟩ := hp hne; ⟨w, ht t (List.mem_cons_self ..) w hw⟩,
      holdsAt_frame (fun t' ht' => ht t' (List.mem_cons_of_mem _ ht')) hb hB⟩
  | .either _ _, ht, hb, hB =>
    hB.imp
      (holdsAt_frame (fun t h => ht t (List.mem_append_left _ h)) (fun b h => hb b (List.mem_append_left _ h)))
      (holdsAt_frame (fun t h => ht t (List.mem_append_right _ h)) (fun b h => hb b (List.mem_append_right _ h)))

/-- The region of a value (FOOTPRINTS.md, "Element regions"): a raw spine
lists its element cells and has no spine cell; an array object has its spine
field's location and the cells the spine there lists. -/
def RegionOf (h : Heap) (v : Val) (spine : Option Nat) (cells : List (Option Nat)) : Prop :=
  (spine = none ∧ v = .arr cells) ∨
    ∃ st, spine = some st ∧ Footprints.spineOf v = some st ∧ h[st]? = some (.arr cells)

/-- A location of a region: its spine cell or a listed element cell. -/
def InRegion (spine : Option Nat) (cells : List (Option Nat)) (l : Nat) : Prop :=
  spine = some l ∨ some l ∈ cells

/-- The values two paths read hold different array spines, where both hold
one (`!==` of two arrays, ARITHMETIC.md, "Spine separation"): for two
arrays, `Footprints.SpineApart` (`PathSpinesApart.spineApart`). -/
def PathSpinesApart (h : Heap) (x : Val) (p : List String) (y : Val) (q : List String) : Prop :=
  ∃ u w, readPath h x p = some u ∧ readPath h y q = some w ∧
    ∀ s t, Footprints.spineOf u = some s → Footprints.spineOf w = some t → s ≠ t

theorem PathSpinesApart.symm {h : Heap} {x y : Val} {p q : List String}
    (ha : PathSpinesApart h x p y q) : PathSpinesApart h y q x p := by
  obtain ⟨u, w, hu, hw, hne⟩ := ha
  exact ⟨w, u, hw, hu, fun s t hs ht he => hne t s ht hs he.symm⟩

theorem PathSpinesApart.extend {h : Heap} {x y : Val} {p q : List String} (vs : List Val)
    (ha : PathSpinesApart h x p y q) : PathSpinesApart (h ++ vs) x p y q := by
  obtain ⟨u, w, hu, hw, hne⟩ := ha
  exact ⟨u, w, readPath_extend vs hu, readPath_extend vs hw, hne⟩

/-- The array spine of path `(x, p)` is distinct from the array spine of every
element currently stored in path `(y, q)`. -/
def PathElemSpinesApart (h : Heap) (x : Val) (p : List String) (y : Val) (q : List String) : Prop :=
  ∃ u w, readPath h x p = some u ∧ readPath h y q = some w ∧
    ∀ st, elementsOf w = some st → ∃ ls, h[st]?.bind spineEntries = some ls ∧
      ∀ l, some l ∈ ls → ∃ e, h[l]? = some e ∧
        ∀ s se, Footprints.spineOf u = some s → Footprints.spineOf e = some se → s ≠ se

theorem PathElemSpinesApart.extend {h : Heap} {x y : Val} {p q : List String} (vs : List Val)
    (ha : PathElemSpinesApart h x p y q) : PathElemSpinesApart (h ++ vs) x p y q := by
  obtain ⟨u, w, hu, hw, hall⟩ := ha
  refine ⟨u, w, readPath_extend vs hu, readPath_extend vs hw, fun st hst => ?_⟩
  obtain ⟨ls, hls, hel⟩ := hall st hst
  refine ⟨ls, spineEntries_extend vs hls, fun l hl => ?_⟩
  obtain ⟨e, he, hne⟩ := hel l hl
  exact ⟨e, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp he).1]; exact he, hne⟩

/-- Two values' regions share no location. -/
def RegionsApart (h : Heap) (u v : Val) : Prop :=
  ∃ sa xs sb ys, RegionOf h u sa xs ∧ RegionOf h v sb ys ∧
    ∀ l, InRegion sa xs l → ∀ m, InRegion sb ys m → l ≠ m

/-- Two paths read values whose regions share no location. -/
def PathRegionsApart (h : Heap) (x : Val) (p : List String) (y : Val) (q : List String) : Prop :=
  ∃ u w, readPath h x p = some u ∧ readPath h y q = some w ∧ RegionsApart h u w

theorem PathRegionsApart.symm {h : Heap} {x y : Val} {p q : List String}
    (ha : PathRegionsApart h x p y q) : PathRegionsApart h y q x p := by
  obtain ⟨u, w, hu, hw, hr⟩ := ha
  obtain ⟨sa, xs, sb, ys, h1, h2, hsep⟩ := hr
  exact ⟨w, u, hw, hu, sb, ys, sa, xs, h2, h1, fun l hl m hm he => hsep m hm l hl he.symm⟩

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

/-- An array object's region has its spine cell. -/
theorem regionOf_spine {h : Heap} {v : Val} {s xs l} (hr : RegionOf h v s xs)
    (hs : Footprints.spineOf v = some l) : s = some l := by
  rcases hr with ⟨-, rfl⟩ | ⟨st, rfl, hst, -⟩
  · simp [Footprints.spineOf, Footprints.fieldsOf] at hs
  · rw [hst] at hs; exact hs

/-- A region's value determines it, in a given heap. -/
theorem regionOf_unique {h : Heap} {v : Val} {s s' xs xs'} (hr : RegionOf h v s xs) (hr' : RegionOf h v s' xs') :
    s = s' ∧ xs = xs' := by
  rcases hr with ⟨rfl, rfl⟩ | ⟨st, rfl, hst, hx⟩ <;> rcases hr' with ⟨rfl, he⟩ | ⟨st', rfl, hst', hx'⟩
  · cases he; exact ⟨rfl, rfl⟩
  · simp [Footprints.spineOf, Footprints.fieldsOf] at hst'
  · subst he; simp [Footprints.spineOf, Footprints.fieldsOf] at hst
  · rw [hst] at hst'; cases hst'; rw [hx] at hx'; cases hx'; exact ⟨rfl, rfl⟩

/-- An affine index bound `t + offset` (or the constant `offset` when `base = none`),
used as the lower (`start`) and upper (`stop`) bounds of `IndexFact.every`. -/
structure IndexBound where
  base : Option Term := none
  offset : Int := 0
  deriving DecidableEq, Repr, Hashable

namespace IndexBound

def zero : IndexBound := ⟨none, 0⟩
def const (n : Int) : IndexBound := ⟨none, n⟩
def ofTerm (t : Term) (offset : Int := 0) : IndexBound := ⟨some t, offset⟩

def eval (ε : EntryState) (ρ : Env) (h : Heap) (b : IndexBound) : Option Int :=
  match b.base with
  | none => some b.offset
  | some t => (termValue ε ρ h t).map (· + b.offset)

def slots (b : IndexBound) : List Nat :=
  match b.base with
  | none => []
  | some t => t.slots

def entrySlots (b : IndexBound) : List Nat :=
  match b.base with
  | none => []
  | some t => t.entrySlots

def entryTerms (b : IndexBound) : List Term :=
  match b.base with
  | none => []
  | some t => if t.atEntry then [t] else []

def terms (b : IndexBound) : List Term :=
  match b.base with
  | none => []
  | some t => [t]

def mapM (f : Nat → Option Nat) (b : IndexBound) : Option IndexBound :=
  match b.base with
  | none => some b
  | some t => (t.mapM f).map fun t' => { b with base := some t' }

def mapM' (f : Nat → Nat) (b : IndexBound) : IndexBound :=
  { b with base := b.base.map (Term.mapM' f) }

def mapEntry (g : Nat → Option Nat) (b : IndexBound) : Option IndexBound :=
  match b.base with
  | none => some b
  | some t => (t.mapEntry g).map fun t' => { b with base := some t' }

def toNow (b : IndexBound) : IndexBound :=
  { b with base := b.base.map fun t => { t with atEntry := false } }

def reroot (now entry : Nat → Option (Nat × List String)) (b : IndexBound) : Option IndexBound :=
  match b.base with
  | none => some b
  | some t => (t.reroot now entry).map fun t' => { b with base := some t' }

/-- The linear form representing `a.base - b.base` (cancelling identical base terms). -/
def subTerms (a b : IndexBound) : Linear.Form Term :=
  match a.base, b.base with
  | none, none => []
  | some ta, none => [(ta, 1)]
  | none, some tb => [(tb, -1)]
  | some ta, some tb => if ta == tb then [] else [(ta, 1), (tb, -1)]

/-- The linear fact encoding `a + extra ≤ b`. -/
def leFact (a b : IndexBound) (extra : Int := 0) : Linear.Fact Term :=
  .le (subTerms a b) (b.offset - a.offset - extra)

theorem leFact_sound {a b : IndexBound} {extra ma mb : Int} {ρ : Env} {h : Heap}
    (ha : a.eval ε ρ h = some ma) (hb : b.eval ε ρ h = some mb)
    (hle : (a.leFact b extra).Holds (termValuation ε ρ h)) : ma + extra ≤ mb := by
  simp only [leFact, subTerms, Linear.Fact.Holds] at hle
  cases hba : a.base <;> cases hbb : b.base <;>
    simp only [eval, hba, hbb, Option.map_eq_some_iff, Option.some.injEq] at ha hb hle
  · subst ha; subst hb; simp only [Linear.Form.eval] at hle; omega
  · obtain ⟨vb, hvb, rfl⟩ := hb; subst ha
    simp only [Linear.Form.eval, termValuation, hvb, Option.getD_some] at hle; omega
  · obtain ⟨va, hva, rfl⟩ := ha; subst hb
    simp only [Linear.Form.eval, termValuation, hva, Option.getD_some] at hle; omega
  · obtain ⟨va, hva, rfl⟩ := ha; obtain ⟨vb, hvb, rfl⟩ := hb
    rename_i ta tb
    by_cases heq : ta = tb
    · subst heq; rw [hva] at hvb; cases hvb
      simp only [beq_self_eq_true, ite_true, Linear.Form.eval] at hle; omega
    · have hne : (ta == tb) = false := beq_false_of_ne heq
      simp only [hne, Bool.false_eq_true, ite_false, Linear.Form.eval, termValuation, hva, hvb, Option.getD_some] at hle
      omega

/-- The term part of a bound as a linear form: `b = form + offset`. -/
def form (b : IndexBound) : Linear.Form Term :=
  match b.base with
  | none => []
  | some t => [(t, 1)]

theorem eval_form {b : IndexBound} {z : Int} {ρ : Env} {h : Heap} (hb : b.eval ε ρ h = some z) :
    Linear.Form.eval (termValuation ε ρ h) b.form + b.offset = z := by
  cases hbb : b.base with
  | none =>
    simp only [eval, hbb, Option.some.injEq] at hb
    simp [form, hbb, Linear.Form.eval, hb]
  | some t =>
    simp only [eval, hbb, Option.map_eq_some_iff] at hb
    obtain ⟨v, hv, rfl⟩ := hb
    simp only [form, hbb, Linear.Form.eval, termValuation, hv, Option.getD_some]
    omega

theorem mapM_eq (f : Nat → Nat) (b : IndexBound) : b.mapM (some ∘ f) = some (b.mapM' f) := by
  cases b with
  | mk base offset =>
    cases base with
    | none => rfl
    | some t =>
      simp only [mapM, mapM', congrFun (Term.mapM_eq f) t, Function.comp_apply, Option.map_some]

theorem eval_mapM {b b' : IndexBound} {f : Nat → Option Nat} {ρ ρ' : Env} {h : Heap}
    (hm : b.mapM f = some b') (hf : ∀ s ∈ b.slots, ∀ t, f s = some t → ρ' t = ρ s) :
    b'.eval ε ρ' h = b.eval ε ρ h := by
  cases b with
  | mk base offset =>
    cases base with
    | none => cases hm; rfl
    | some t =>
      simp only [mapM, Option.map_eq_some_iff] at hm
      obtain ⟨t', ht', rfl⟩ := hm
      simp only [eval]
      have htv : termValue ε ρ' h t' = termValue ε ρ h t :=
        termValue_mapM ht' fun he j hj => hf t.slot (by simp [slots, Term.slots, he]) j hj
      rw [htv]

theorem eval_extend {b : IndexBound} {ρ : Env} {h : Heap} {z : Int} (vs : List Val)
    (hb : b.eval ε ρ h = some z) : b.eval ε ρ (h ++ vs) = some z := by
  cases b with
  | mk base offset =>
    cases base with
    | none => exact hb
    | some t =>
      simp only [eval, Option.map_eq_some_iff] at hb ⊢
      obtain ⟨v, hv, rfl⟩ := hb
      exact ⟨v, termValue_extend vs hv, rfl⟩

theorem eval_congr {b : IndexBound} {ρ ρ' : Env} {h : Heap}
    (hs : ∀ s ∈ b.slots, ρ s = ρ' s) : b.eval ε ρ h = b.eval ε ρ' h := by
  cases b with
  | mk base offset =>
    cases base with
    | none => rfl
    | some t =>
      simp only [eval]
      rw [termValue_congr fun he => hs t.slot (by simp [slots, Term.slots, he])]

theorem eval_congr_entry {b : IndexBound} {ε' : EntryState} {ρ : Env} {h : Heap} (hh : ε.heap = ε'.heap)
    (hs : ∀ s ∈ b.entrySlots, ε.env s = ε'.env s) : b.eval ε ρ h = b.eval ε' ρ h := by
  cases b with
  | mk base offset =>
    cases base with
    | none => rfl
    | some t =>
      simp only [eval]
      rw [termValue_congr_entry hh fun he => hs t.slot (by simp [entrySlots, Term.entrySlots, he])]

theorem eval_entry {b : IndexBound} (hb : b.entrySlots = []) (ε' : EntryState) {ρ : Env} {h : Heap} :
    b.eval ε ρ h = b.eval ε' ρ h := by
  cases b with
  | mk base offset =>
    cases base with
    | none => rfl
    | some t =>
      simp only [eval]
      cases he : t.atEntry
      · rw [termValue_now he, termValue_now he]
      · simp [entrySlots, Term.entrySlots, he] at hb

theorem eval_mapEntry {b b' : IndexBound} {g : Nat → Option Nat} {ε' : EntryState} {ρ : Env} {h : Heap}
    (hm : b.mapEntry g = some b') (hh : ε'.heap = ε.heap)
    (hg : ∀ s ∈ b.entrySlots, ∀ j, g s = some j → ε'.env j = ε.env s) :
    b'.eval ε' ρ h = b.eval ε ρ h := by
  cases b with
  | mk base offset =>
    cases base with
    | none => cases hm; rfl
    | some t =>
      simp only [mapEntry, Option.map_eq_some_iff] at hm
      obtain ⟨t', ht', rfl⟩ := hm
      simp only [eval]
      rw [termValue_mapEntry ht' hh fun he j hj => hg t.slot (by simp [entrySlots, Term.entrySlots, he]) j hj]

theorem eval_congr_entryTerms {b : IndexBound} {ε' : EntryState} {ρ : Env} {h : Heap}
    (ht : ∀ t ∈ b.entryTerms, termAt ε.env ε.heap t = termAt ε'.env ε'.heap t) :
    b.eval ε ρ h = b.eval ε' ρ h := by
  cases b with
  | mk base offset =>
    cases base with
    | none => rfl
    | some t =>
      simp only [eval]
      cases he : t.atEntry
      · rw [termValue_now he, termValue_now he]
      · rw [termValue_atEntry he, termValue_atEntry he, ht t (by simp [entryTerms, he])]

theorem eval_toNow {ρ : Env} {h : Heap} (hρ : ε.env = ρ) (hh : ε.heap = h) (b : IndexBound) :
    b.toNow.eval ε ρ h = b.eval ε ρ h := by
  cases b with
  | mk base offset =>
    cases base with
    | none => rfl
    | some t =>
      simp only [toNow, eval, Option.map_some]
      cases he : t.atEntry
      · obtain ⟨k, s, p, a⟩ := t; simp only at he; subst he; rfl
      · rw [termValue_now rfl, termValue_atEntry he]
        simp only [termAt, hρ, hh]

theorem entrySlots_toNow (b : IndexBound) : b.toNow.entrySlots = [] := by
  cases b with
  | mk base offset =>
    cases base with
    | none => rfl
    | some t => simp [toNow, entrySlots, Term.entrySlots]

end IndexBound

/-- An index fact (DESIGN of the guarded write, PROGRAM-TYPING.md, "Writes at
a checked index"): the slot `k` holds a number that is an array index
(`index`); the slot `n` holds the length of the spine the array in slot `x`
holds (`length`); the slot `k` holds an array index at most that length
(`bound`), below it where `strict`; the slot `k` holds a safe integer (`int`);
the slot `k` holds the double `2^53`, past the safe integers (`pastSafe`);
the slots of a linear
fact denote integers meeting it (`linear`, ARITHMETIC.md, "Linear
facts"), its terms (`Term`) rooted at slots. `index`, `int` and a linear fact
of slots' values read no heap; the others read the locations their terms or
the array's spine field read. A guarded fact (`guarded`, ARITHMETIC.md,
"Guarded clauses") holds where the path `path` from the slot `slot` reads a
value (`readGuard`) that is the tag's, or its body holds. An element fact
(`element`, ARITHMETIC.md, "Quantified clauses") states that the slot
`value` holds what the spine of the array in slot `array` holds at the index
the slot `index` holds, below its length: the present element's value, or
`undefined` at a hole. A quantified fact (`every`) states, of the array the
path `path` reads from the slot `slot`, that for every index `i` with
`start ≤ i < stop` each fact of its body holds, its variables the index, the
element at it (a present safe integer) and terms, each denoting an integer.
A region fact (`apart`, FOOTPRINTS.md, "Element regions") states that the
regions of the values in slots `slot` and `other` share no location
(`RegionsApart`). A spine separation (`spineApart`, ARITHMETIC.md, "Spine
separation") states that the values the paths `path` and `otherPath` read
from the slots `slot` and `other` hold different array spines
(`PathSpinesApart`). -/
inductive IndexFact where
  | index (slot : Nat)
  | length (array length : Nat)
  | bound (array index : Nat) (strict : Bool)
  | int (slot : Nat)
  | pastSafe (slot : Nat)
  | linear (fact : Linear.Fact Term)
  | either (left right : IndexFact)
  | guarded (slot : Nat) (path : List String) (tag : GuardTag) (body : IndexFact)
  | element (value array : Nat) (index : IndexShift)
  | fieldRead (value obj : Nat) (field : String)
  | every (slot : Nat) (path : List String) (start stop : IndexBound) (body : List BodyClause)
  | atIndex (slot : Nat) (path : List String) (index : IndexShift) (guard : Option GuardTag) (body : LinearClause Bound)
  | apart (slot : Nat) (path : List String) (other : Nat) (otherPath : List String)
  | spineApart (slot : Nat) (path : List String) (other : Nat) (otherPath : List String)
  | elemSpineApart (slot : Nat) (path : List String) (other : Nat) (otherPath : List String)
  | same (slot other : Nat)
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
  | .element v x k => v :: x :: k.slots
  | .fieldRead v o _ => [v, o]
  | .every s _ start stop body => s :: start.slots ++ stop.slots ++ body.flatMap BodyClause.slots
  | .atIndex s _ idx _ body => s :: idx.slots ++ body.vars.flatMap Bound.slots
  | .apart a _ b _ => [a, b]
  | .spineApart a _ b _ => [a, b]
  | .elemSpineApart a _ b _ => [a, b]
  | .same a b => [a, b]

/-- The slots of the entry environment a fact reads, by its entry terms. -/
def entrySlots : IndexFact → List Nat
  | .linear F => F.vars.flatMap Term.entrySlots
  | .either A B => A.entrySlots ++ B.entrySlots
  | .guarded _ _ _ B => B.entrySlots
  | .element _ _ k => k.entrySlots
  | .every _ _ start stop body => start.entrySlots ++ stop.entrySlots ++ body.flatMap BodyClause.entrySlots
  | .atIndex _ _ idx _ body => idx.entrySlots ++ body.vars.flatMap Bound.entrySlots
  | _ => []

/-- A quantified fact's body with each slot renamed, where the map names every one. -/
def mapBody (f : Nat → Option Nat) : List BodyClause → Option (List BodyClause)
  | [] => some []
  | F :: t => do pure ((← F.mapM f) :: (← mapBody f t))

theorem mapBody_pairs {f : Nat → Option Nat} :
    ∀ {body body' : List BodyClause}, mapBody f body = some body' →
      (∀ F' ∈ body', ∃ F ∈ body, F.mapM f = some F') ∧
      (∀ F ∈ body, ∃ F' ∈ body', F.mapM f = some F')
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

theorem mapBody_some (f : Nat → Nat) : ∀ body : List BodyClause, ∃ body', mapBody (some ∘ f) body = some body'
  | [] => ⟨[], rfl⟩
  | F :: t => by
    obtain ⟨G, hG⟩ := F.mapM_some f
    obtain ⟨t', ht⟩ := mapBody_some f t
    refine ⟨G :: t', ?_⟩
    simp only [mapBody, hG, ht]
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
  | .element v x k => do pure (.element (← f v) (← f x) (← k.mapM f))
  | .fieldRead v o fld => do pure (.fieldRead (← f v) (← f o) fld)
  | .every s p start stop body => do
    pure (.every (← f s) p (← start.mapM f) (← stop.mapM f) (← mapBody f body))
  | .atIndex s p idx guard body => do
    pure (.atIndex (← f s) p (← idx.mapM f) guard (← body.mapVars (Bound.mapM f)))
  | .apart a p b q => do pure (.apart (← f a) p (← f b) q)
  | .spineApart a p b q => do pure (.spineApart (← f a) p (← f b) q)
  | .elemSpineApart a p b q => do pure (.elemSpineApart (← f a) p (← f b) q)
  | .same a b => do pure (.same (← f a) (← f b))

/-- The fact with each slot renamed. -/
def map (f : Nat → Nat) (F : IndexFact) : IndexFact := (F.mapM (some ∘ f)).getD F

def HoldsAt (ε : EntryState) : IndexFact → Env → Heap → Prop
  | .index k, ρ, _ => ∃ b i, ρ k = .num b ∧ indexOfBits b = some i
  | .length x n, ρ, h => ∃ s ls, Footprints.spineOf (ρ x) = some s ∧ h[s]? = some (.arr ls) ∧
      ρ n = .num (bitsOfNat ls.length) ∧ ls.length ≤ maxArrayLength
  | .bound x k st, ρ, h => ∃ s ls b i, Footprints.spineOf (ρ x) = some s ∧ h[s]? = some (.arr ls) ∧
      ρ k = .num b ∧ indexOfBits b = some i ∧ i + (if st then 1 else 0) ≤ ls.length
  | .int k, ρ, _ => (intValue (ρ k)).isSome
  | .pastSafe k, ρ, _ => ρ k = .num SafeIntegers.pastSafeBits
  | .linear F, ρ, h => (∀ t ∈ F.vars, (termValue ε ρ h t).isSome) ∧ F.Holds (termValuation ε ρ h)
  | .either A B, ρ, h => A.HoldsAt ε ρ h ∨ B.HoldsAt ε ρ h
  | .guarded s p t B, ρ, h => ∃ v, readGuard h (ρ s) p = some v ∧ (t.holds v ∨ B.HoldsAt ε ρ h)
  | .element v x k, ρ, h => ∃ s ls, ∃ i : Nat, elementsOf (ρ x) = some s ∧ h[s]?.bind spineEntries = some ls ∧
      k.eval ε ρ h 0 = some i ∧ i < ls.length ∧
      (∀ l, ls[i]? = some (some l) → h[l]? = some (ρ v)) ∧ (ls[i]? = some none → ρ v = .undef)
  | .fieldRead v o fld, ρ, h => readPath h (ρ o) [fld] = some (ρ v)
  | .every s p start stop body, ρ, h => ∃ w st ls m n, readPath h (ρ s) p = some w ∧ elementsOf w = some st ∧
      h[st]?.bind spineEntries = some ls ∧ start.eval ε ρ h = some m ∧ stop.eval ε ρ h = some n ∧
      ∀ i : Nat, m ≤ (i : Int) → (i : Int) < n → ∀ F ∈ body, F.HoldsAt ε ρ h ls i
  | .atIndex s p idx guard body, ρ, h => ∃ w st ls, ∃ i : Nat, readPath h (ρ s) p = some w ∧ elementsOf w = some st ∧
      h[st]?.bind spineEntries = some ls ∧ idx.eval ε ρ h 0 = some i ∧ i < ls.length ∧
      match guard with
      | some g => (∃ l v, ls[i]? = some (some l) ∧ h[l]? = some v ∧ g.holds v) ∨
          (ls[i]? = some none ∧ g.holds .undef) ∨ body.HoldsAt (boundValue ε ρ h ls i)
      | none => body.HoldsAt (boundValue ε ρ h ls i)
  | .apart a p b q, ρ, h => PathRegionsApart h (ρ a) p (ρ b) q
  | .spineApart a p b q, ρ, h => PathSpinesApart h (ρ a) p (ρ b) q
  | .elemSpineApart a p b q, ρ, h => PathElemSpinesApart h (ρ a) p (ρ b) q
  | .same a b, ρ, _ => ρ a = ρ b



/-- A quantified clause is framed by its array path, spine (kept or extended),
bounds, guard targets, and body values. -/
theorem every_frame {s p start stop body ρ h h'}
    (he : (IndexFact.every s p start stop body).HoldsAt ε ρ h)
    (hp : ∀ w, readPath h (ρ s) p = some w → readPath h' (ρ s) p = some w)
    (hs : ∀ w st ls, readPath h (ρ s) p = some w → elementsOf w = some st →
      h[st]?.bind spineEntries = some ls → ∃ ls', h'[st]?.bind spineEntries = some ls' ∧ ls <+: ls')
    (hm : ∀ m, start.eval ε ρ h = some m → start.eval ε ρ h' = some m)
    (hn : ∀ z, stop.eval ε ρ h = some z → stop.eval ε ρ h' = some z)
    (ht : ∀ w st ls ls', readPath h (ρ s) p = some w → elementsOf w = some st →
      h[st]?.bind spineEntries = some ls → ls <+: ls' → ∀ F ∈ body, ∀ i t, t ∈ F.targets → ∀ v,
      t.read ε ρ h ls i = some v → t.read ε ρ h' ls' i = some v)
    (hb : ∀ w st ls ls', readPath h (ρ s) p = some w → elementsOf w = some st →
      h[st]?.bind spineEntries = some ls → ls <+: ls' → ∀ F ∈ body, ∀ i b, b ∈ F.vars → ∀ z,
      boundValue ε ρ h ls i b = some z → boundValue ε ρ h' ls' i b = some z) :
    (IndexFact.every s p start stop body).HoldsAt ε ρ h' := by
  obtain ⟨w, st, ls, m, z, hw, hst, hls, hmv, hz, hall⟩ := he
  obtain ⟨ls', hls', hpre⟩ := hs w st ls hw hst hls
  exact ⟨w, st, ls', m, z, hp w hw, hst, hls', hm m hmv, hn z hz,
    fun i hlo hi F hF => BodyClause.holdsAt_frame (ht w st ls ls' hw hst hls hpre F hF i)
      (hb w st ls ls' hw hst hls hpre F hF i) (hall i hlo hi F hF)⟩

/-- An indexed-element clause is framed by its array path, spine, index, element
cell (when guarded) and body values. -/
theorem atIndex_frame {s p idx guard body ρ h h'}
    (he : (IndexFact.atIndex s p idx guard body).HoldsAt ε ρ h)
    (hp : ∀ w, readPath h (ρ s) p = some w → readPath h' (ρ s) p = some w)
    (hs : ∀ w st ls, readPath h (ρ s) p = some w → elementsOf w = some st →
      h[st]?.bind spineEntries = some ls → h'[st]?.bind spineEntries = some ls)
    (hn : ∀ i : Nat, idx.eval ε ρ h 0 = some i → idx.eval ε ρ h' 0 = some i)
    (hguard : ∀ g, guard = some g → ∀ w st ls (i l : Nat) v, readPath h (ρ s) p = some w → elementsOf w = some st →
      h[st]?.bind spineEntries = some ls → ls[i]? = some (some l) → h[l]? = some v → g.holds v → h'[l]? = some v)
    (hb : ∀ w st ls, readPath h (ρ s) p = some w → elementsOf w = some st →
      h[st]?.bind spineEntries = some ls → ∀ i b, b ∈ body.vars → ∀ z,
      boundValue ε ρ h ls i b = some z → boundValue ε ρ h' ls i b = some z) :
    (IndexFact.atIndex s p idx guard body).HoldsAt ε ρ h' := by
  obtain ⟨w, st, ls, i, hw, hst, hls, hi, hlt, hrest⟩ := he
  refine ⟨w, st, ls, i, hp w hw, hst, hs w st ls hw hst hls, hn i hi, hlt, ?_⟩
  cases guard with
  | none => exact LinearClause.holdsAt_extend (hb w st ls hw hst hls i) hrest
  | some g =>
    rcases hrest with ⟨l, v, hli, hlv, hgv⟩ | ⟨hli, hgu⟩ | hbody
    · exact .inl ⟨l, v, hli, hguard g rfl w st ls i l v hw hst hls hli hlv hgv, hgv⟩
    · exact .inr (.inl ⟨hli, hgu⟩)
    · exact .inr (.inr (LinearClause.holdsAt_extend (hb w st ls hw hst hls i) hbody))


theorem holdsAt_mapM {F F' : IndexFact} {f : Nat → Option Nat} {ρ ρ' : Env} {h : Heap}
    (hm : F.mapM f = some F') (hf : ∀ s ∈ F.slots, ∀ t, f s = some t → ρ' t = ρ s) :
    F'.HoldsAt ε ρ' h ↔ F.HoldsAt ε ρ h := by
  induction F generalizing F' with
  | either A B ihA ihB =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨A', hA, B', hB, rfl⟩ := hm
    exact or_congr (ihA hA (fun x hx y hy => hf x (by simp [slots, hx]) y hy))
      (ihB hB (fun x hx y hy => hf x (by simp [slots, hx]) y hy))
  | apart a p b q =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨a', ha, b', hb, rfl⟩ := hm
    simp only [HoldsAt, hf a (by simp [slots]) a' ha, hf b (by simp [slots]) b' hb]
  | spineApart a p b q =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨a', ha, b', hb, rfl⟩ := hm
    simp only [HoldsAt, hf a (by simp [slots]) a' ha, hf b (by simp [slots]) b' hb]
  | elemSpineApart a p b q =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨a', ha, b', hb, rfl⟩ := hm
    simp only [HoldsAt, hf a (by simp [slots]) a' ha, hf b (by simp [slots]) b' hb]
  | same a b =>
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
    have hk' : k'.eval ε ρ' h 0 = k.eval ε ρ h 0 :=
      IndexShift.eval_mapM hk fun z hz => hf z (by simp [slots, hz])
    simp only [HoldsAt, hf v (by simp [slots]) v' hv, hf x (by simp [slots]) x' hx, hk']
  | fieldRead v o fld =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨v', hv, o', ho, rfl⟩ := hm
    simp only [HoldsAt, hf v (by simp [slots]) v' hv, hf o (by simp [slots]) o' ho]
  | every s p start stop body =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨s', hs, start', hstart, stop', hstop, body', hbody, rfl⟩ := hm
    have hs' := hf s (by simp [slots]) s' hs
    have hlo : start'.eval ε ρ' h = start.eval ε ρ h :=
      IndexBound.eval_mapM hstart fun x hx j hj => hf x (by simp [slots, hx]) j hj
    have hst : stop'.eval ε ρ' h = stop.eval ε ρ h :=
      IndexBound.eval_mapM hstop fun x hx j hj => hf x (by simp [slots, hx]) j hj
    obtain ⟨hb1, hb2⟩ := mapBody_pairs hbody
    have hval : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body, ∀ F', F.mapM f = some F' →
        (F'.HoldsAt ε ρ' h ls i ↔ F.HoldsAt ε ρ h ls i) := fun ls i F hF F' hm =>
      BodyClause.holdsAt_mapM hm fun x hx y hy =>
        hf x (by simp only [slots, List.mem_cons, List.mem_append, List.mem_flatMap]; exact .inr ⟨F, hF, hx⟩) y hy
    simp only [HoldsAt, hs', hlo, hst]
    constructor
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      refine ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo hi F hF => ?_⟩
      obtain ⟨F', hF', hm⟩ := hb2 F hF
      exact (hval ls i F hF F' hm).mp (hall i hlo hi F' hF')
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      refine ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo hi F' hF' => ?_⟩
      obtain ⟨F, hF, hm⟩ := hb1 F' hF'
      exact (hval ls i F hF F' hm).mpr (hall i hlo hi F hF)
  | atIndex s p idx guard body =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨s', hs, idx', hidx, body', hbody, rfl⟩ := hm
    have hs' := hf s (by simp [slots]) s' hs
    have hst : idx'.eval ε ρ' h 0 = idx.eval ε ρ h 0 :=
      IndexShift.eval_mapM hidx fun z hz j hj => hf z (List.mem_cons_of_mem _ (List.mem_append_left _ hz)) j hj
    have hval : ∀ (ls : List (Option Nat)) (i : Nat),
        body'.HoldsAt (boundValue ε ρ' h ls i) ↔ body.HoldsAt (boundValue ε ρ h ls i) := by
      intro ls i
      refine LinearClause.holdsAt_mapVars hbody fun x hx y hy => ?_
      cases x with
      | index => cases hy; rfl
      | elem => cases hy; rfl
      | offset _ => cases hy; rfl
      | project _ _ => cases hy; rfl
      | parallel s' p' sh k ep =>
        simp only [Bound.mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hy
        obtain ⟨t', ht', sh', hsh', rfl⟩ := hy
        have hsp := hf s' (List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨.parallel s' p' sh k ep, hx, by simp [Bound.slots]⟩))) t' ht'
        have hsh := IndexShift.eval_mapM (ε := ε) (h := h) (i := i) hsh' fun z hz =>
          hf z (List.mem_cons_of_mem _ (List.mem_append_right _
            (List.mem_flatMap.mpr ⟨.parallel s' p' sh k ep, hx, by simp [Bound.slots, hz]⟩)))
        simp only [boundValue, hsp, hsh]
      | free t =>
        simp only [Bound.mapM, Option.map_eq_some_iff] at hy
        obtain ⟨t', ht', rfl⟩ := hy
        simp only [boundValue]
        refine termValue_mapM ht' fun he j hj => hf t.slot ?_ j hj
        exact List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨.free t, hx, by simp [Bound.slots, Term.slots, he]⟩))
    simp only [HoldsAt, hs', hst]
    cases guard with
    | none => simp only [hval]
    | some g => simp only [hval]
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

/-- A body variable read at the current state. -/
def _root_.Verification.HeapKnowledge.Bound.toNow : Bound → Bound
  | .parallel s p sh k ep => .parallel s p sh.toNow k ep
  | .free t => .free t.toNow
  | b => b

/-- The fact read at the entry state itself: each entry term `old(t)`
restated as `t` (the current term at the same slot), in every fact form
whose terms are terms, a quantified fact's bound and body included. -/
def toNow : IndexFact → IndexFact
  | .linear F => .linear ((F.mapVars fun t => some t.toNow).getD F)
  | .either A B => .either A.toNow B.toNow
  | .guarded s p t B => .guarded s p t B.toNow
  | .element v x k => .element v x k.toNow
  | .every s p start stop body => .every s p start.toNow stop.toNow (body.map (BodyClause.toNow Bound.toNow))
  | .atIndex s p idx guard body => .atIndex s p idx.toNow guard ((body.mapVars (some ∘ Bound.toNow)).getD body)
  | F => F

theorem _root_.Verification.HeapKnowledge.BodyClause.holdsAt_toNow {ρ : Env} {h : Heap}
    (hρ : ε.env = ρ) (hh : ε.heap = h) {ls : List (Option Nat)} {i : Nat} :
    ∀ C : BodyClause, (C.toNow Bound.toNow).HoldsAt ε ρ h ls i ↔ C.HoldsAt ε ρ h ls i
  | .clause c => by
    obtain ⟨c', hc⟩ := LinearClause.mapVars_some Bound.toNow c
    simp only [BodyClause.toNow, BodyClause.HoldsAt, hc, Option.getD_some]
    refine LinearClause.holdsAt_mapVars hc fun x _ y hy => ?_
    cases hy
    cases x with
    | parallel s p sh k ep =>
      simp only [Bound.toNow, boundValue, IndexShift.eval_toNow hρ hh sh]
    | free t => exact termValue_toNow hρ hh t
    | _ => rfl
  | .guarded t g b => by
    have hown : t.toNow.ownElement = t.ownElement := by cases t <;> rfl
    have htr : t.toNow.read ε ρ h ls i = t.read ε ρ h ls i := by
      cases t with
      | self _ => rfl
      | parallel s p sh ep => simp only [ElemTarget.toNow, ElemTarget.read, IndexShift.eval_toNow hρ hh sh]
    simp only [BodyClause.toNow, BodyClause.HoldsAt, htr, hown, BodyClause.holdsAt_toNow hρ hh b]
  | .either a b =>
    or_congr (BodyClause.holdsAt_toNow hρ hh a) (BodyClause.holdsAt_toNow hρ hh b)

theorem _root_.Verification.HeapKnowledge.BodyClause.entrySlots_toNow :
    ∀ C : BodyClause, (C.toNow Bound.toNow).entrySlots = []
  | .clause c => by
    obtain ⟨d, hd⟩ := LinearClause.mapVars_some Bound.toNow c
    simp only [BodyClause.toNow, BodyClause.entrySlots, hd, Option.getD_some, List.flatMap_eq_nil_iff]
    intro b hb
    obtain ⟨x, -, hx⟩ := LinearClause.mapVars_vars hd b hb
    cases hx
    cases x with
    | parallel s p sh k ep => simp [Bound.toNow, Bound.entrySlots, IndexShift.entrySlots_toNow]
    | free t => simp [Bound.toNow, Bound.entrySlots, Term.entrySlots, Term.toNow]
    | _ => simp [Bound.toNow, Bound.entrySlots]
  | .guarded t _ b => by
    have ht : t.toNow.entrySlots = [] := by
      cases t with
      | self _ => rfl
      | parallel _ _ sh _ => exact IndexShift.entrySlots_toNow sh
    simp only [BodyClause.toNow, BodyClause.entrySlots, ht, BodyClause.entrySlots_toNow b, List.nil_append]
  | .either a b => by
    simp only [BodyClause.toNow, BodyClause.entrySlots, BodyClause.entrySlots_toNow a, BodyClause.entrySlots_toNow b, List.append_nil]

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
  | element v x k =>
    simp only [toNow, HoldsAt, IndexShift.eval_toNow hρ hh k]
  | every s p start stop body =>
    simp only [toNow, HoldsAt, IndexBound.eval_toNow hρ hh start, IndexBound.eval_toNow hρ hh stop]
    constructor
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      exact ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo hi C hC =>
        (BodyClause.holdsAt_toNow hρ hh C).mp (hall i hlo hi _ (List.mem_map_of_mem hC))⟩
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      refine ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo hi C' hC' => ?_⟩
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
      exact (BodyClause.holdsAt_toNow hρ hh C).mpr (hall i hlo hi C hC)
  | atIndex s p idx guard body =>
    have hb : ∀ (ls : List (Option Nat)) (i : Nat),
        ((body.mapVars (some ∘ Bound.toNow)).getD body).HoldsAt (boundValue ε ρ h ls i) ↔
          body.HoldsAt (boundValue ε ρ h ls i) := by
      intro ls i
      obtain ⟨C', hC⟩ := LinearClause.mapVars_some Bound.toNow body
      rw [hC, Option.getD_some]
      refine LinearClause.holdsAt_mapVars hC fun x _ y hy => ?_
      cases hy
      cases x with
      | parallel s p sh k ep => simp only [Bound.toNow, boundValue, IndexShift.eval_toNow hρ hh sh]
      | free t => exact termValue_toNow hρ hh t
      | _ => rfl
    simp only [toNow, HoldsAt, IndexShift.eval_toNow hρ hh idx]
    cases guard with
    | none => simp only [hb]
    | some g => simp only [hb]
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
  | element v x k => exact IndexShift.entrySlots_toNow k
  | every s p start stop body =>
    simp only [toNow, entrySlots, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
    refine ⟨⟨IndexBound.entrySlots_toNow start, IndexBound.entrySlots_toNow stop⟩, fun C' hC' => ?_⟩
    obtain ⟨C, -, rfl⟩ := List.mem_map.mp hC'
    exact BodyClause.entrySlots_toNow C
  | atIndex s p idx guard body =>
    simp only [toNow, entrySlots, List.append_eq_nil_iff, List.flatMap_eq_nil_iff]
    refine ⟨IndexShift.entrySlots_toNow idx, fun b hb => ?_⟩
    obtain ⟨D, hD⟩ := LinearClause.mapVars_some Bound.toNow body
    rw [hD, Option.getD_some] at hb
    obtain ⟨x, -, hx⟩ := LinearClause.mapVars_vars hD b hb
    cases hx
    cases x with
    | parallel _ _ sh _ _ => exact IndexShift.entrySlots_toNow sh
    | free t => simp [Bound.toNow, Bound.entrySlots, Term.entrySlots, Term.toNow]
    | _ => simp [Bound.toNow, Bound.entrySlots]
  | _ => rfl

/-- The entry terms a fact names. -/
def entryTerms : IndexFact → List Term
  | .linear F => F.vars.filter (·.atEntry)
  | .either A B => A.entryTerms ++ B.entryTerms
  | .guarded _ _ _ B => B.entryTerms
  | .element _ _ k => k.entryTerms
  | .every _ _ start stop body => start.entryTerms ++ stop.entryTerms ++ body.flatMap BodyClause.entryTerms
  | .atIndex _ _ idx _ body => idx.entryTerms ++ body.vars.flatMap Bound.entryTerms
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

/-- **The terms a fact states defined** (the note "Tolerant frames",
section 6: an atom's paths are defined), by every form: a linear fact's
terms; an `int` atom's slot's value; a `length` atom's array's length and
its slot's value; an element atom's index; a quantified fact's bound. -/
def defines : IndexFact → List Term
  | .linear F => F.vars
  | .int k => [.value k]
  | .length x n => [.length x, .value n]
  | .element _ _ k => k.terms.map (·.1)
  | .every _ _ start stop _ => start.terms ++ stop.terms
  | .atIndex _ _ idx _ _ => idx.terms.map (·.1)
  | .index _ | .bound _ _ _ | .pastSafe _ | .either _ _ | .guarded _ _ _ _ | .fieldRead _ _ _ | .apart _ _ _ _
  | .spineApart _ _ _ _ | .elemSpineApart _ _ _ _ | .same _ _ => []

/-- **A fact that holds defines its terms** (proved, by every form): each
term `defines` names denotes an integer wherever the fact holds. -/
theorem defines_holds {F : IndexFact} {ρ : Env} {h : Heap} (hF : F.HoldsAt ε ρ h) :
    ∀ t ∈ F.defines, (termValue ε ρ h t).isSome := by
  intro t ht
  cases F with
  | linear G => exact hF.1 t ht
  | int k =>
    simp only [defines, List.mem_singleton] at ht; subst ht
    simp only [termValue_value]; exact hF
  | length x n =>
    obtain ⟨s, ls, hs, hl, hn, hm⟩ := hF
    simp only [defines, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · simp only [termValue_length, lengthOf_of_spine hs hl hm, Option.isSome_some]
    · simp only [termValue_value, hn]
      rw [intValue_num (i := (ls.length : Int)) ⟨by simp [maxArrayLength] at hm ⊢; omega, .inl ⟨by omega, by simp⟩⟩]; rfl
  | element v x k =>
    obtain ⟨s, ls, i, -, -, hk, -⟩ := hF
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact IndexShift.eval_defines hk p hp
  | every s p start stop body =>
    obtain ⟨w, sto, ls, m, n, -, -, -, hm, hn, -⟩ := hF
    simp only [defines, List.mem_append] at ht
    rcases ht with ht | ht
    · cases hsb : start.base with
      | none => simp [IndexBound.terms, hsb] at ht
      | some ts =>
        simp only [IndexBound.terms, hsb, List.mem_singleton] at ht; subst ht
        simp only [IndexBound.eval, hsb, Option.map_eq_some_iff] at hm
        obtain ⟨v, hv, -⟩ := hm; simp [hv]
    · cases hsb : stop.base with
      | none => simp [IndexBound.terms, hsb] at ht
      | some ts =>
        simp only [IndexBound.terms, hsb, List.mem_singleton] at ht; subst ht
        simp only [IndexBound.eval, hsb, Option.map_eq_some_iff] at hn
        obtain ⟨v, hv, -⟩ := hn; simp [hv]
  | atIndex s p idx guard body =>
    obtain ⟨w, sto, ls, i, -, -, -, hi, -⟩ := hF
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    exact IndexShift.eval_defines hi q hq
  | index _ | bound _ _ _ | pastSafe _ | either _ _ | guarded _ _ _ _ | fieldRead _ _ _ | apart _ _ _ _ | spineApart _ _ _ _ | elemSpineApart _ _ _ _ | same _ _ =>
    simp [defines] at ht

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
  | .element v x k => by
    have hk : k.mapM (some ∘ f) = some (k.mapTotal f) := congrFun (IndexShift.mapM_total f) k
    exact ⟨.element (f v) (f x) (k.mapTotal f), by simp only [mapM, hk]; rfl⟩
  | .fieldRead v o fld => ⟨_, rfl⟩
  | .every s p start stop body => by
    obtain ⟨body', hb⟩ := mapBody_some f body
    have hlo : start.mapM (some ∘ f) = some (start.mapM' f) := IndexBound.mapM_eq f start
    have hst : stop.mapM (some ∘ f) = some (stop.mapM' f) := IndexBound.mapM_eq f stop
    exact ⟨.every (f s) p (start.mapM' f) (stop.mapM' f) body', by simp only [mapM, hb, hlo, hst]; rfl⟩
  | .atIndex s p idx guard body => by
    obtain ⟨body', hb⟩ := LinearClause.mapVars_some (Bound.mapTotal f) body
    have hst : idx.mapM (some ∘ f) = some (idx.mapTotal f) := congrFun (IndexShift.mapM_total f) idx
    exact ⟨.atIndex (f s) p (idx.mapTotal f) guard body', by simp only [mapM, Bound.mapM_total, hb, hst]; rfl⟩
  | .apart a p b q => ⟨_, rfl⟩
  | .spineApart a p b q => ⟨_, rfl⟩
  | .elemSpineApart a p b q => ⟨_, rfl⟩
  | .same a b => ⟨_, rfl⟩

/-- A fact reads its slots' values alone. -/
theorem holdsAt_map {F : IndexFact} {f : Nat → Nat} {ρ ρ' : Env} {h : Heap}
    (hf : ∀ s ∈ F.slots, ρ' (f s) = ρ s) : (F.map f).HoldsAt ε ρ' h ↔ F.HoldsAt ε ρ h := by
  obtain ⟨G, hG⟩ := mapM_total f F
  simp only [map, hG, Option.getD_some]
  exact holdsAt_mapM hG (fun s hs t ht => by cases ht; exact hf s hs)

/-- A heap extension preserves a fact: the spine lies in the old heap. -/
theorem holdsAt_extend {F : IndexFact} {ρ : Env} {h : Heap} (vs : List Val) (hF : F.HoldsAt ε ρ h) :
    F.HoldsAt ε ρ (h ++ vs) := by
  induction F with
  | either A B ihA ihB => exact hF.imp ihA ihB
  | apart a p b q =>
    obtain ⟨u, w, hu, hw, hr⟩ := hF
    exact ⟨u, w, readPath_extend vs hu, readPath_extend vs hw, regionsApart_extend vs hr⟩
  | spineApart a p b q => exact PathSpinesApart.extend vs hF
  | elemSpineApart a p b q => exact PathElemSpinesApart.extend vs hF
  | same _ _ => exact hF
  | guarded s p t B ih =>
    obtain ⟨v, hv, hor⟩ := hF
    exact ⟨v, readGuard_extend vs hv, hor.imp id ih⟩
  | element v x k =>
    obtain ⟨s, ls, i, hs, hl, hk, hlt, hp, hh⟩ := hF
    refine ⟨s, ls, i, hs, spineEntries_extend vs hl, IndexShift.eval_extend vs hk, hlt, fun l hli => ?_, hh⟩
    have := hp l hli
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp this).1]; exact this
  | fieldRead v o fld => exact readPath_extend vs hF
  | every s p start stop body =>
    obtain ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩ := hF
    exact ⟨w, st, ls, m, n, readPath_extend vs hw, hsto, spineEntries_extend vs hls,
      IndexBound.eval_extend vs hm, IndexBound.eval_extend vs hn,
      fun i hlo hi F hF => BodyClause.holdsAt_extend vs (hall i hlo hi F hF)⟩
  | atIndex s p idx guard body =>
    obtain ⟨w, st, ls, i, hw, hsto, hls, hi, hlt, hrest⟩ := hF
    refine ⟨w, st, ls, i, readPath_extend vs hw, hsto, spineEntries_extend vs hls,
      IndexShift.eval_extend vs hi, hlt, ?_⟩
    have hbody : body.HoldsAt (boundValue ε ρ h ls i) → body.HoldsAt (boundValue ε ρ (h ++ vs) ls i) :=
      LinearClause.holdsAt_extend (fun _ _ _ hm => boundValue_extend vs hm)
    cases guard with
    | none => exact hbody hrest
    | some g =>
      rcases hrest with ⟨l, v, hli, hv, hg⟩ | ⟨hli, hg⟩ | hB
      · exact .inl ⟨l, v, hli, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv, hg⟩
      · exact .inr (.inl ⟨hli, hg⟩)
      · exact .inr (.inr (hbody hB))
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
  | apart a p b q =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2]
  | spineApart a p b q =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2]
  | elemSpineApart a p b q =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2]
  | same a b =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2]
  | guarded s p t B ih =>
    simp only [slots, List.mem_cons, forall_eq_or_imp] at hs
    simp only [HoldsAt, hs.1, ih hs.2]
  | element v x k =>
    have hv : ρ v = ρ' v := hs v (by simp [slots])
    have hx : ρ x = ρ' x := hs x (by simp [slots])
    have hk : k.eval ε ρ h 0 = k.eval ε ρ' h 0 :=
      IndexShift.eval_congr fun z hz => hs z (by simp [slots, hz])
    simp only [HoldsAt, hv, hx, hk]
  | fieldRead v o fld =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2]
  | every s p start stop body =>
    have h0 : ρ s = ρ' s := hs s (by simp [slots])
    have hlo : start.eval ε ρ h = start.eval ε ρ' h :=
      IndexBound.eval_congr fun x hx => hs x (by simp [slots, hx])
    have hst : stop.eval ε ρ h = stop.eval ε ρ' h :=
      IndexBound.eval_congr fun x hx => hs x (by simp [slots, hx])
    have hb : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body,
        (F.HoldsAt ε ρ h ls i ↔ F.HoldsAt ε ρ' h ls i) := fun ls i F hF =>
      BodyClause.holdsAt_congr fun x hx =>
        hs x (by simp only [slots, List.mem_cons, List.mem_append, List.mem_flatMap]; exact .inr ⟨F, hF, hx⟩)
    simp only [HoldsAt, h0, hlo, hst]
    constructor
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      exact ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo' hi F hF => (hb ls i F hF).mp (hall i hlo' hi F hF)⟩
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      exact ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo' hi F hF => (hb ls i F hF).mpr (hall i hlo' hi F hF)⟩
  | atIndex s p idx guard body =>
    have h0 : ρ s = ρ' s := hs s (by simp [slots])
    have hst : idx.eval ε ρ h 0 = idx.eval ε ρ' h 0 :=
      IndexShift.eval_congr fun z hz => hs z (List.mem_cons_of_mem _ (List.mem_append_left _ hz))
    have hbe : ∀ (ls : List (Option Nat)) (i : Nat),
        body.HoldsAt (boundValue ε ρ h ls i) ↔ body.HoldsAt (boundValue ε ρ' h ls i) :=
      fun ls i => BodyClause.holdsAt_congr (B := .clause body) fun x hx =>
        hs x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
    simp only [HoldsAt, h0, hst]
    cases guard with
    | none => simp only [hbe]
    | some g => simp only [hbe]
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
  | element v x k =>
    simp only [HoldsAt, IndexShift.eval_congr_entry hh hs]
  | every s p start stop body =>
    have hlo : start.eval ε ρ h = start.eval ε' ρ h :=
      IndexBound.eval_congr_entry hh fun x hx => hs x (by simp [entrySlots, hx])
    have hst : stop.eval ε ρ h = stop.eval ε' ρ h :=
      IndexBound.eval_congr_entry hh fun x hx => hs x (by simp [entrySlots, hx])
    have hb : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body,
        (F.HoldsAt ε ρ h ls i ↔ F.HoldsAt ε' ρ h ls i) := fun ls i F hF =>
      BodyClause.holdsAt_congr_entry hh fun x hx =>
        hs x (by simp only [entrySlots, List.mem_append, List.mem_flatMap]; exact .inr ⟨F, hF, hx⟩)
    simp only [HoldsAt, hlo, hst]
    constructor
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      exact ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo' hi F hF => (hb ls i F hF).mp (hall i hlo' hi F hF)⟩
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      exact ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo' hi F hF => (hb ls i F hF).mpr (hall i hlo' hi F hF)⟩
  | atIndex s p idx guard body =>
    have hst : idx.eval ε ρ h 0 = idx.eval ε' ρ h 0 :=
      IndexShift.eval_congr_entry hh fun z hz => hs z (List.mem_append_left _ hz)
    have hbe : ∀ (ls : List (Option Nat)) (i : Nat),
        body.HoldsAt (boundValue ε ρ h ls i) ↔ body.HoldsAt (boundValue ε' ρ h ls i) :=
      fun ls i => BodyClause.holdsAt_congr_entry (B := .clause body) hh fun x hx =>
        hs x (List.mem_append_right _ hx)
    simp only [HoldsAt, hst]
    cases guard with
    | none => simp only [hbe]
    | some g => simp only [hbe]
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
  | element v x k =>
    simp only [HoldsAt, IndexShift.eval_entry (ε' := ε') hF]
  | every s p start stop body =>
    simp only [entrySlots, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at hF
    have hlo : start.eval ε ρ h = start.eval ε' ρ h := IndexBound.eval_entry hF.1.1 ε'
    have hst : stop.eval ε ρ h = stop.eval ε' ρ h := IndexBound.eval_entry hF.1.2 ε'
    have hb : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body,
        (F.HoldsAt ε ρ h ls i ↔ F.HoldsAt ε' ρ h ls i) := fun ls i F hF' =>
      BodyClause.holdsAt_entry (hF.2 F hF')
    simp only [HoldsAt, hlo, hst]
    constructor
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      exact ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo' hi F hF => (hb ls i F hF).mp (hall i hlo' hi F hF)⟩
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      exact ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo' hi F hF => (hb ls i F hF).mpr (hall i hlo' hi F hF)⟩
  | atIndex s p idx guard body =>
    simp only [entrySlots, List.append_eq_nil_iff] at hF
    have hst : idx.eval ε ρ h 0 = idx.eval ε' ρ h 0 := IndexShift.eval_entry (ε' := ε') hF.1
    have hbe : ∀ (ls : List (Option Nat)) (i : Nat),
        body.HoldsAt (boundValue ε ρ h ls i) ↔ body.HoldsAt (boundValue ε' ρ h ls i) :=
      fun ls i => BodyClause.holdsAt_entry (B := .clause body) hF.2
    simp only [HoldsAt, hst]
    cases guard with
    | none => simp only [hbe]
    | some g => simp only [hbe]
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

/-- A quantified fact's body with each entry slot translated by `g`. -/
def mapBodyEntry (g : Nat → Option Nat) : List BodyClause → Option (List BodyClause)
  | [] => some []
  | F :: t => do pure ((← F.mapEntry g) :: (← mapBodyEntry g t))

theorem mapBodyEntry_pairs {g : Nat → Option Nat} :
    ∀ {body body' : List BodyClause}, mapBodyEntry g body = some body' →
      (∀ F' ∈ body', ∃ F ∈ body, F.mapEntry g = some F') ∧
      (∀ F ∈ body, ∃ F' ∈ body', F.mapEntry g = some F')
  | [], body', h => by simp only [mapBodyEntry, Option.some.injEq] at h; subst h; simp
  | F :: t, body', h => by
    simp only [mapBodyEntry, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨G, hG, t', ht, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mapBodyEntry_pairs ht
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
  | .element v x k => (k.mapEntry g).map (.element v x)
  | .every s p start stop body => do
    pure (.every s p (← start.mapEntry g) (← stop.mapEntry g) (← mapBodyEntry g body))
  | .atIndex s p idx guard body => do pure (.atIndex s p (← idx.mapEntry g) guard (← body.mapVars (Bound.mapEntry g)))
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
  | every s p start stop body =>
    simp only [mapEntry, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨start', hstart, stop', hstop, body', hbody, rfl⟩ := hm
    have hlo : start'.eval ε' ρ h = start.eval ε ρ h :=
      IndexBound.eval_mapEntry hstart hh fun x hx j hj => hg x (by simp [entrySlots, hx]) j hj
    have hst : stop'.eval ε' ρ h = stop.eval ε ρ h :=
      IndexBound.eval_mapEntry hstop hh fun x hx j hj => hg x (by simp [entrySlots, hx]) j hj
    obtain ⟨hb1, hb2⟩ := mapBodyEntry_pairs hbody
    have hval : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body, ∀ F', F.mapEntry g = some F' →
        (F'.HoldsAt ε' ρ h ls i ↔ F.HoldsAt ε ρ h ls i) := fun ls i F hF F' hm =>
      BodyClause.holdsAt_mapEntry hh hm fun x hx j hj =>
        hg x (by simp only [entrySlots, List.mem_append, List.mem_flatMap]; exact .inr ⟨F, hF, hx⟩) j hj
    simp only [HoldsAt, hlo, hst]
    constructor
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      refine ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo' hi F hF => ?_⟩
      obtain ⟨F', hF', hm⟩ := hb2 F hF
      exact (hval ls i F hF F' hm).mp (hall i hlo' hi F' hF')
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      refine ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo' hi F' hF' => ?_⟩
      obtain ⟨F, hF, hm⟩ := hb1 F' hF'
      exact (hval ls i F hF F' hm).mpr (hall i hlo' hi F hF)
  | atIndex s p idx guard body =>
    simp only [mapEntry, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨idx', hidx, body', hbody, rfl⟩ := hm
    have hst : idx'.eval ε' ρ h 0 = idx.eval ε ρ h 0 :=
      IndexShift.eval_mapEntry hh hidx fun z hz => hg z (List.mem_append_left _ hz)
    have hval : ∀ (ls : List (Option Nat)) (i : Nat),
        body'.HoldsAt (boundValue ε' ρ h ls i) ↔ body.HoldsAt (boundValue ε ρ h ls i) := by
      intro ls i
      refine LinearClause.holdsAt_mapVars hbody fun x hx y hy => ?_
      cases x with
      | free t =>
        simp only [Bound.mapEntry, Option.map_eq_some_iff] at hy
        obtain ⟨t', ht', rfl⟩ := hy
        simp only [boundValue]
        refine termValue_mapEntry ht' hh fun he j hj => hg t.slot ?_ j hj
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.free t, hx, by simp [Bound.entrySlots, Term.entrySlots, he]⟩)
      | project k q =>
        cases hy; simp only [boundValue]
        split
        · rename_i l _
          cases h[l]? with
          | none => rfl
          | some v => simp only [Option.bind_some]; rw [termValue_now rfl, termValue_now rfl]
        · rfl
      | parallel s p sh k ep =>
        simp only [Bound.mapEntry, Option.map_eq_some_iff] at hy
        obtain ⟨sh', hsh', rfl⟩ := hy
        exact boundValue_parallel_entry (IndexShift.eval_mapEntry hh hsh' fun z hz =>
          hg z (List.mem_append_right _ (List.mem_flatMap.mpr ⟨.parallel s p sh k ep, hx, by simp [Bound.entrySlots, hz]⟩)))
      | _ => cases hy; rfl
    simp only [HoldsAt, hst]
    cases guard with
    | none => simp only [hval]
    | some g => simp only [hval]
  | index k => cases hm; exact Iff.rfl
  | length x n => cases hm; exact Iff.rfl
  | bound x k st => cases hm; exact Iff.rfl
  | int k => cases hm; exact Iff.rfl
  | pastSafe k => cases hm; exact Iff.rfl
  | element v x k =>
    simp only [mapEntry, Option.map_eq_some_iff] at hm
    obtain ⟨k', hk', rfl⟩ := hm
    simp only [HoldsAt, IndexShift.eval_mapEntry hh hk' hg]
  | fieldRead v o fld => cases hm; exact Iff.rfl
  | apart a p b q => cases hm; exact Iff.rfl
  | spineApart a p b q => cases hm; exact Iff.rfl
  | elemSpineApart a p b q => cases hm; exact Iff.rfl
  | same a b => cases hm; exact Iff.rfl

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
  | element v x k =>
    simp only [HoldsAt, IndexShift.eval_congr_entryTerms ht]
  | every s p start stop body =>
    have hlo : start.eval ε ρ h = start.eval ε' ρ h :=
      IndexBound.eval_congr_entryTerms fun t htm => ht t (by simp [entryTerms, htm])
    have hst : stop.eval ε ρ h = stop.eval ε' ρ h :=
      IndexBound.eval_congr_entryTerms fun t htm => ht t (by simp [entryTerms, htm])
    have hb : ∀ (ls : List (Option Nat)) (i : Nat), ∀ F ∈ body,
        (F.HoldsAt ε ρ h ls i ↔ F.HoldsAt ε' ρ h ls i) := fun ls i F hF =>
      BodyClause.holdsAt_congr_entryTerms fun t htm =>
        ht t (by simp only [entryTerms, List.mem_append, List.mem_flatMap]; exact .inr ⟨F, hF, htm⟩)
    simp only [HoldsAt, hlo, hst]
    constructor
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      exact ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo' hi F hF => (hb ls i F hF).mp (hall i hlo' hi F hF)⟩
    · rintro ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, hall⟩
      exact ⟨w, st, ls, m, n, hw, hsto, hls, hm, hn, fun i hlo' hi F hF => (hb ls i F hF).mpr (hall i hlo' hi F hF)⟩
  | atIndex s p idx guard body =>
    have hst : idx.eval ε ρ h 0 = idx.eval ε' ρ h 0 :=
      IndexShift.eval_congr_entryTerms fun t htm => ht t (List.mem_append_left _ htm)
    have hbe : ∀ (ls : List (Option Nat)) (i : Nat),
        body.HoldsAt (boundValue ε ρ h ls i) ↔ body.HoldsAt (boundValue ε' ρ h ls i) :=
      fun ls i => BodyClause.holdsAt_congr_entryTerms (B := .clause body) fun t htm =>
        ht t (List.mem_append_right _ htm)
    simp only [HoldsAt, hst]
    cases guard with
    | none => simp only [hbe]
    | some g => simp only [hbe]
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
number, an array spine. A term reads locations of known contents, its path's
objects, then a spine or a number; it denotes the same after a change that
alters no location holding what it reads. -/

/-- What a heap change does to a location holding an array spine: keeps its
contents, keeps its length, grows it (a spine at least as long, at most
`2^32 - 1` long where it was), or neither. -/
inductive SpineChange where
  | keep
  | length
  | grow
  | any
  deriving DecidableEq, Repr

/-- Which locations a heap change may alter, by what they held before it: an
object (`obj`), a number (`num`), an array spine (`spine`). A location
holding any other value may change. -/
structure Changes where
  obj : Bool
  num : Bool
  spine : SpineChange
  deriving DecidableEq, Repr

namespace Changes

/-- Whether the change may alter a location holding `v`. -/
def alters (c : Changes) : Val → Bool
  | .objAt .. => c.obj
  | .num _ => c.num
  | .arr _ | .viewSpine .. => c.spine != .keep
  | _ => true

/-- `h'` meets the change from `h`: every location of `h` holding a value it
does not alter holds it in `h'`, and where it keeps spines' lengths every
spine of `h` is a spine of that length in `h'`. -/
def Holds (c : Changes) (h h' : Heap) : Prop :=
  (∀ (l : Nat) (v : Val), h[l]? = some v → c.alters v = false → h'[l]? = some v) ∧
  (c.spine = .length → ∀ (l : Nat) (ls : List (Option Nat)), h[l]? = some (.arr ls) →
    ∃ ls' : List (Option Nat), h'[l]? = some (.arr ls') ∧ ls'.length = ls.length) ∧
  (c.spine = .grow → ∀ (l : Nat) (ls : List (Option Nat)), h[l]? = some (.arr ls) →
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
  ⟨a.obj || b.obj, a.num || b.num, if a.spine == .keep && b.spine == .keep then .keep else .any⟩

theorem join_alters_left {a b : Changes} {v : Val} (h : a.alters v = true) : (a.join b).alters v = true := by
  cases v <;> simp_all [Changes.join, Changes.alters]

theorem join_alters_right {a b : Changes} {v : Val} (h : b.alters v = true) : (a.join b).alters v = true := by
  cases v <;> simp_all [Changes.join, Changes.alters]

theorem top_holds (h h' : Heap) : top.Holds h h' :=
  ⟨fun _ v _ ha => (by rw [top_alters] at ha; cases ha), fun hs => (by simp [top] at hs),
    fun hs => (by simp [top] at hs)⟩

/-- The change a closed footprint allows: below `any` no location holding an
object changes, at most `init` none holding a number; when both spine classes
keep their spines, every spine is kept (`keep`), otherwise an array class that
keeps array spines keeps every array spine's length (`length`), and `extend` or
`grow` on array spines leaves each array spine no shorter and within
`maxArrayLength` where it was. -/
def ofClosed (Φ : Footprints.Closed) : Changes :=
  ⟨Φ.value == .any, !(Φ.value.le .init),
    match Φ.spines.onSpine with
    | .keep => .keep
    | _ => match Φ.array.onSpine with
      | .keep => .length
      | .extend | .grow => .grow
      | _ => .any⟩

theorem ofClosed_holds {Φ : Footprints.Closed} {h h' : Heap} (hp : Φ.Holds h h') : (ofClosed Φ).Holds h h' := by
  have hpArr := Footprints.Closed.holds_iff.mp hp
  replace hp := Footprints.Closed.holds_iff.mp (hp.mono (Footprints.Closed.le_ofSpines_spines Φ))
  refine ⟨fun l v hv ha => ?_, fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨v', hv', hc⟩ := hp.2 l v hv
    have hkeep : v' = v := by
      cases v
      case arr ls =>
        simp only [alters, ofClosed] at ha
        have hst : Φ.spines = .keep ∨ Φ.spines = .init ∨ Φ.spines = .scalar := by
          cases hΦ : Φ.spines <;> cases hΦa : Φ.array <;> simp_all [Footprints.Change.onSpine]
        simp only [Footprints.Closed.at_ofSpines, Footprints.isArr, ite_true] at hc
        rcases hst with hst | hst | hst
        · rw [hst] at hc; exact hc
        · rw [hst] at hc; exact hc.init_spine
        · rw [hst] at hc; exact hc.scalar_spine
      case viewSpine f cs =>
        simp only [alters, ofClosed] at ha
        have hst : Φ.spines = .keep ∨ Φ.spines = .init ∨ Φ.spines = .scalar := by
          cases hΦ : Φ.spines <;> cases hΦa : Φ.array <;> simp_all [Footprints.Change.onSpine]
        simp only [Footprints.Closed.at_ofSpines, Footprints.isArr, ite_true] at hc
        rcases hst with hst | hst | hst
        · rw [hst] at hc; exact hc
        · rw [hst] at hc; exact hc.init_isArr rfl
        · rw [hst] at hc; exact hc.scalar_isArr rfl
      case objAt =>
        have hva : Φ.value ≠ .any := by
          intro he; simp [alters, ofClosed, he] at ha
        simp only [Footprints.Closed.at_ofSpines, Footprints.isArr] at hc
        exact hc.object_kept hva rfl
      case num =>
        have hva : Φ.value.le .init = true := by
          simpa [alters, ofClosed] using ha
        simp only [Footprints.Closed.at_ofSpines, Footprints.isArr] at hc
        exact hc.defined_kept hva rfl
      all_goals simp [alters] at ha
    exact hkeep ▸ hv'
  · intro l ls hl
    have hst : Φ.array = .keep ∨ Φ.array = .init ∨ Φ.array = .scalar := by
      revert hs; simp only [ofClosed]
      cases hΦs : Φ.spines <;> cases hΦa : Φ.array <;> simp [Footprints.Change.onSpine]
    obtain ⟨v', hv', hc⟩ := hpArr.2 l _ hl
    have hat : Φ.at (.arr ls) = Φ.array := by
      rw [Footprints.Closed.at_category]; rfl
    rw [hat] at hc
    have hkeep : v' = .arr ls := by
      rcases hst with hst | hst | hst
      · rw [hst] at hc; exact hc
      · rw [hst] at hc; exact hc.init_spine
      · rw [hst] at hc; exact hc.scalar_spine
    exact ⟨ls, hkeep ▸ hv', rfl⟩
  · intro l ls hl
    have hg : Φ.array.le .grow = true := by
      revert hs; simp only [ofClosed]
      cases hΦs : Φ.spines <;> cases hΦa : Φ.array <;>
        simp [Footprints.Change.onSpine, Footprints.Change.le, Footprints.Change.rank]
    obtain ⟨v', hv', hc⟩ := hpArr.2 l _ hl
    have hat : Φ.at (.arr ls) = Φ.array := by
      rw [Footprints.Closed.at_category]; rfl
    rw [hat] at hc
    rcases hc.mono hg with rfl | ⟨ls₁, ls', h₁, rfl, -, -, hlen⟩ | hsc | ⟨_, _, _, he, -⟩
    · exact ⟨ls, hv', Nat.le_refl _, id⟩
    · cases h₁; exact ⟨ls', hv', hlen.1, hlen.2⟩
    · exact absurd hsc.2.1 (by simp [Footprints.isArr])
    · cases he

end Changes

/-- The location of field `g` of slot `s`'s object keeps its contents from
`h` to `h'` wherever `first s g` says so. -/
def FirstKept (first : Nat → String → Bool) (ρ : Env) (h h' : Heap) : Prop :=
  ∀ s g fs cd o l v, first s g = true → ρ s = .objAt fs cd o → fs.lookup (.str g) = some l →
    h[l]? = some v → h'[l]? = some v

/-- Whether a term denotes the same after a change `c`: each location its
path reads holds an object, but the last, which holds a number for a value
term; a length term then reads a spine, a view term a number. The first
location, field `g` of the root's object, may instead be one `first` keeps. -/
def Term.pathKeptBy (c : Changes) (first : Nat → String → Bool) (t : Term) : Bool :=
  let last := if t.kind.isNum then c.num else c.obj
  match t.path with
    | [] => true
    | g :: q => (first t.slot g || !(if q.isEmpty then last else c.obj)) &&
        (q.isEmpty || (!last && (q.length == 1 || !c.obj)))

/-- Whether a change keeps a spine's length: it keeps the spine or its
length. -/
def Changes.keepsLength (c : Changes) : Bool := c.spine == .keep || c.spine == .length

def Term.keptBy (c : Changes) (first : Nat → String → Bool) (t : Term) : Bool :=
  t.atEntry || t.pathKeptBy c first &&
  (match t.kind with
    | .value | .bitMask _ => true
    | .length => c.keepsLength || (t.path.isEmpty && first t.slot "[]")
    | .view => true
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

/-- A change keeps what a kind of term reads of a value: a spine it keeps or
keeps the length of, and an immutable view length or string length. -/
theorem kindValue_kept {c : Changes} {h h' : Heap} (hc : c.Holds h h') {k : Term.Kind} {w : Val} {n : Int}
    (hk : kindValue h k w = some n) (hlen : k = .length → c.keepsLength = true) :
    kindValue h' k w = some n := by
  cases k with
  | value => exact hk
  | strLength => exact hk
  | bitMask _ => exact hk
  | length =>
    obtain ⟨s, ls, hs, hls, rfl, hm⟩ := lengthOf_spine hk
    have hst := hlen rfl
    cases hcs : c.spine with
    | keep => exact lengthOf_of_spine hs (hc.1 s _ hls (by simp [Changes.alters, hcs])) hm
    | length =>
      obtain ⟨ls', hls', heq⟩ := hc.2.1 hcs s ls hls
      have := lengthOf_of_spine hs hls' (by omega)
      simp only [kindValue, this, heq]
    | grow | any => simp [Changes.keepsLength, hcs] at hst
  | view => exact hk

/-- A change keeps the value a term's path reads where it keeps the path
(`Term.pathKeptBy`) and that value is of the class the term's kind reads. -/
theorem pathRead_kept {c : Changes} {first : Nat → String → Bool} {ρ : Env} {h h' : Heap}
    {kind : Term.Kind} {s : Nat} {p : List String} {w : Val}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h')
    (hpath : Term.pathKeptBy c first ⟨kind, s, p, false⟩ = true)
    (hlast : c.alters w = (if kind.isNum then c.num else c.obj))
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
  simp only [termValue, termAt, Bool.false_eq_true, ite_false, Option.bind_eq_some_iff] at ht ⊢
  obtain ⟨w, hw, hkw⟩ := ht
  simp only [Term.keptBy, Term.pathKeptBy, Bool.false_or, Bool.and_eq_true] at hk
  obtain ⟨hpath, hkind⟩ := hk
  by_cases hstr : kind = .strLength
  · -- A string's length reads the slot's own value alone.
    subst hstr
    simp only [List.isEmpty_iff] at hkind
    subst hkind
    exact ⟨w, hw, hkw⟩
  have hlast : c.alters w = (if kind.isNum then c.num else c.obj) := by
    cases kind with
    | value =>
      simp only [kindValue] at hkw
      obtain ⟨b, rfl, -⟩ := intValue_safe hkw
      rfl
    | bitMask m =>
      cases w <;> simp only [kindValue, bitMaskOf, reduceCtorEq] at hkw
      rfl
    | length =>
      obtain ⟨st, ls, hs, -⟩ := lengthOf_spine hkw
      cases w
      case objAt => rfl
      all_goals simp [Footprints.spineOf, Footprints.fieldsOf] at hs
    | view =>
      obtain ⟨fs, cd, o, l, b, rfl, -⟩ := viewLengthOf_inv hkw
      rfl
    | strLength => exact absurd rfl hstr
  by_cases hfs : kind = .length ∧ p = [] ∧ first s "[]" = true
  · -- The spine at field `[]` of the root's object, kept by `first`.
    obtain ⟨rfl, rfl, hfs⟩ := hfs
    refine ⟨w, hw, ?_⟩
    simp only [readPath, Option.some.injEq] at hw
    subst hw
    simp only [kindValue] at hkw ⊢
    obtain ⟨st, ls, hst, hls, rfl, hm⟩ := lengthOf_spine hkw
    cases hv : ρ s
    case objAt fs cd o =>
      rw [hv] at hst
      have hl : fs.lookup (.str "[]") = some st := by
        simpa [Footprints.fieldsOf, arraySpineKey] using Footprints.spineOf_lookup hst
      exact lengthOf_of_spine hst (hf s "[]" fs cd o st _ hfs hv hl hls) hm
    all_goals rw [hv] at hst; simp [Footprints.spineOf, Footprints.fieldsOf] at hst
  have hkind' : (match kind with
      | .value | .bitMask _ => true
      | .length => c.keepsLength
      | .view => true
      | .strLength => true) = true := by
    cases kind with
    | value | bitMask _ => rfl
    | strLength => rfl
    | view => rfl
    | length =>
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at hkind
      rcases hkind with h1 | ⟨h2, h3⟩
      · simpa using h1
      · exact absurd ⟨rfl, h2, h3⟩ hfs
  refine ⟨w, ?_, kindValue_kept hc hkw (fun he => by subst he; simpa using hkind')⟩
  exact pathRead_kept hc hf (by simpa [Term.pathKeptBy] using hpath) hlast hw

/-- Whether a change grows what a length term denotes: it keeps the term's
path and grows every spine (`SpineChange.grow`). -/
def Term.grownBy (c : Changes) (first : Nat → String → Bool) (t : Term) : Bool :=
  t.kind == .length && c.spine == .grow && t.pathKeptBy c first

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
  simp only [termValue, termAt, Bool.false_eq_true, ite_false, Option.bind_eq_some_iff] at ht ⊢
  obtain ⟨w, hw, hkw⟩ := ht
  simp only [kindValue] at hkw
  obtain ⟨st, ls, hst, hls, rfl, hm⟩ := lengthOf_spine hkw
  have hlast : c.alters w = (if Term.Kind.length == .value then c.num else c.obj) := by
    cases w
    case objAt => rfl
    all_goals simp [Footprints.spineOf, Footprints.fieldsOf] at hst
  obtain ⟨ls', hls', hle, hmax⟩ := hc.2.2 hs st ls hls
  refine ⟨ls'.length, ⟨w, pathRead_kept hc hf hpath hlast hw, ?_⟩, by exact_mod_cast hle⟩
  simp only [kindValue]
  exact lengthOf_of_spine hst hls' (hmax hm)

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

def IndexShift.keptBy (c : Changes) (first : Nat → String → Bool) (sh : IndexShift) : Bool :=
  sh.terms.all fun p => p.1.keptBy c first

/-- Whether a change keeps what a body variable denotes (`Term.keptBy`): the
index and the element are read apart, and an element projection is kept where
the change keeps that term read from the element value. -/
def Bound.keptBy (c : Changes) (first : Nat → String → Bool) : Bound → Bool
  | .index | .elem => true
  | .project k p => (Term.now k 0 p).keptBy c (fun _ _ => false)
  | .parallel _ _ _ _ _ | .offset _ => false
  | .free t => t.keptBy c first

/-- Whether a change grows what a body variable denotes (`Term.grownBy`): a
free length term or a projected element's length term grown by the change. -/
def Bound.grownBy (c : Changes) (first : Nat → String → Bool) : Bound → Bool
  | .project k p => (Term.now k 0 p).grownBy c (fun _ _ => false)
  | .free t => t.grownBy c first
  | _ => false

/-- Whether a change keeps what an element guard target reads at an index whose
element cell it keeps. -/
def ElemTarget.keptBy : ElemTarget → Bool
  | .self ep => ep.isEmpty
  | .parallel _ _ _ _ => false

/-- Whether a change keeps a body fact of a quantified fact at an index whose
element it keeps: each term kept, or grown at a coefficient at most `0`. -/
def bodyKeptBy (c : Changes) (first : Nat → String → Bool) : LinearClause Bound → Bool :=
  LinearClause.monotone (Bound.keptBy c first) (Bound.grownBy c first)

/-- Whether a change keeps a body clause of a quantified fact at an index whose
element it keeps: an unguarded linear clause kept by `bodyKeptBy`, or a guarded
clause whose target and body are kept. -/
def bodyClauseKeptBy (c : Changes) (first : Nat → String → Bool) : BodyClause → Bool
  | .clause F => bodyKeptBy c first F
  | .guarded t _ b => t.keptBy && bodyClauseKeptBy c first b
  | .either a b => bodyClauseKeptBy c first a && bodyClauseKeptBy c first b

theorem BodyClause.holdsAt_monotone {c : Changes} {first : Nat → String → Bool}
    {ρ : Env} {h h' : Heap} {ls ls' : List (Option Nat)} {i : Nat}
    (ht : ∀ (t : ElemTarget), t.keptBy = true → ∀ w, t.read ε ρ h ls i = some w → t.read ε ρ h' ls' i = some w)
    (hk : ∀ (x : Bound) n, x.keptBy c first = true → boundValue ε ρ h ls i x = some n → boundValue ε ρ h' ls' i x = some n)
    (hg : ∀ (x : Bound) n, x.grownBy c first = true → boundValue ε ρ h ls i x = some n →
      ∃ n', boundValue ε ρ h' ls' i x = some n' ∧ n ≤ n') :
    ∀ {B : BodyClause}, bodyClauseKeptBy c first B = true → B.HoldsAt ε ρ h ls i → B.HoldsAt ε ρ h' ls' i
  | .clause _, hm, hF => LinearClause.holdsAt_monotone hk hg hm hF
  | .guarded t _ _, hm, hB => by
    simp only [bodyClauseKeptBy, Bool.and_eq_true] at hm
    rcases hB with ⟨w, hw, htg⟩ | ⟨hp, hb⟩
    · exact .inl ⟨w, ht t hm.1 w hw, htg⟩
    · refine .inr ⟨fun hne => ?_, holdsAt_monotone ht hk hg hm.2 hb⟩
      obtain ⟨w, hw⟩ := hp hne
      exact ⟨w, ht t hm.1 w hw⟩
  | .either _ _, hm, hB => by
    simp only [bodyClauseKeptBy, Bool.and_eq_true] at hm
    exact hB.imp (holdsAt_monotone ht hk hg hm.1) (holdsAt_monotone ht hk hg hm.2)

def IndexBound.keptBy (c : Changes) (first : Nat → String → Bool) (b : IndexBound) : Bool :=
  match b.base with
  | none => true
  | some t => t.keptBy c first

theorem IndexBound.eval_kept {c : Changes} {first : Nat → String → Bool} {ρ : Env} {h h' : Heap} {b : IndexBound} {n : Int}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hk : b.keptBy c first = true)
    (he : b.eval ε ρ h = some n) : b.eval ε ρ h' = some n := by
  cases b with
  | mk base offset =>
    cases base with
    | none => exact he
    | some t =>
      simp only [eval, Option.map_eq_some_iff] at he ⊢
      obtain ⟨v, hv, rfl⟩ := he
      exact ⟨v, termValue_kept hc hf hk hv, rfl⟩

namespace IndexFact

/-- A footprint frames a quantified clause when it keeps the spine and
numeric element cells, its array path, bounds and every free body term. -/
def everyKept (c : Changes) (first : Nat → String → Bool) : IndexFact → Bool
  | .every s p start stop body => c.spine == .keep && !c.num &&
      (Term.mk .length s p false).pathKeptBy c first && start.keptBy c first && stop.keptBy c first &&
      body.all fun
        | .clause F => F.vars.all fun b => match b with
            | .free t => t.keptBy c first
            | .project _ _ | .parallel _ _ _ _ _ => false
            | _ => true
        | .guarded _ _ _ | .either _ _ => false
  | _ => false

theorem everyKept_sound {c : Changes} {first : Nat → String → Bool} {F : IndexFact} {ρ h h'}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h')
    (hk : F.everyKept c first = true) (hF : F.HoldsAt ε ρ h) : F.HoldsAt ε ρ h' := by
  cases F <;> simp only [everyKept] at hk
  all_goals try contradiction
  rename_i s p start stop body
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.all_eq_true] at hk
  obtain ⟨⟨⟨⟨⟨hspine, hnum⟩, hpath⟩, hstart⟩, hstop⟩, hbody⟩ := hk
  obtain ⟨w, st, ls, m, z, hw, hst, hls, hm, hz, hall⟩ := hF
  have hobj : c.alters w = c.obj := by
    cases w <;> simp_all [elementsOf, Changes.alters]
  have hpath' := pathRead_kept (kind := .length) hc hf hpath hobj hw
  have hls' : h'[st]?.bind spineEntries = some ls := by
    obtain ⟨u, hu, he⟩ := Option.bind_eq_some_iff.mp hls
    rw [hc.1 st u hu (by cases u <;> simp_all [spineEntries, Changes.alters])]; exact he
  refine ⟨w, st, ls, m, z, hpath', hst, hls',
    IndexBound.eval_kept hc hf hstart hm, IndexBound.eval_kept hc hf hstop hz, fun i hlo hi F hFm => ?_⟩
  have hBF := hbody F hFm
  cases F with
  | guarded _ _ _ | either _ _ => simp at hBF
  | clause C =>
    have hA := hall i hlo hi (.clause C) hFm
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
    | free t => exact termValue_kept (ε := ε) hc hf (List.all_eq_true.mp hBF (.free t) hx) ha
    | elem => exact elem i ha
    | offset d => exact elem (i + d) ha
    | project k p => have := List.all_eq_true.mp hBF (.project k p) hx; contradiction
    | parallel s p sh k ep => have := List.all_eq_true.mp hBF (.parallel s p sh k ep) hx; contradiction

/-- A change keeping every spine keeps every region: its spine cell holds
the same spine, and a raw spine reads no heap. -/
theorem regionOf_kept {c : Changes} {h h' : Heap} {v : Val} {s xs}
    (hc : c.Holds h h') (hk : c.spine = .keep) (hr : RegionOf h v s xs) : RegionOf h' v s xs := by
  rcases hr with hr | ⟨st, hs, hst, hx⟩
  · exact .inl hr
  · exact .inr ⟨st, hs, hst, hc.1 st _ hx (by simp [Changes.alters, hk])⟩

theorem regionsApart_kept {c : Changes} {h h' : Heap} {u v : Val}
    (hc : c.Holds h h') (hk : c.spine = .keep) (ha : RegionsApart h u v) : RegionsApart h' u v := by
  obtain ⟨sa, xs, sb, ys, hx, hy, hab⟩ := ha
  exact ⟨sa, xs, sb, ys, regionOf_kept hc hk hx, regionOf_kept hc hk hy, hab⟩

/-- Whether a change preserves a fact (`Term.keptBy`): `index` and `int` read
no heap, `length` and `bound` a spine's length. -/
def keptBy (c : Changes) (first : Nat → String → Bool) : IndexFact → Bool
  | .index _ | .int _ | .pastSafe _ => true
  | .length x _ => c.keepsLength || first x "[]"
  | .bound x _ _ => c.spine != .any || first x "[]"
  | .linear F => F.vars.all (Term.keptBy c first) || match F with
    | .le G _ => Term.formKeptBy c first G
    | .ne _ _ => false
  | .either A B => A.keptBy c first && B.keptBy c first
  | .guarded s p _ B => guardKept first s p && B.keptBy c first
  | .fieldRead _ o fld => guardKept first o [fld]
  | .element .. | .every .. | .atIndex .. | .elemSpineApart .. => false
  | .apart a p b q => c.spine == .keep && guardKept first a p && guardKept first b q
  | .spineApart a p b q => guardKept first a p && guardKept first b q
  | .same .. => true

theorem holdsAt_kept {c : Changes} {first : Nat → String → Bool} {F : IndexFact} {ρ : Env} {h h' : Heap}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hk : F.keptBy c first = true) (hF : F.HoldsAt ε ρ h) :
    F.HoldsAt ε ρ h' := by
  have spine : ∀ {x s : Nat} {ls : List (Option Nat)}, (c.spine != .any || first x "[]") = true →
      Footprints.spineOf (ρ x) = some s → h[s]? = some (.arr ls) →
      ∃ ls' : List (Option Nat), h'[s]? = some (.arr ls') ∧ ls.length ≤ ls'.length ∧
        ((c.keepsLength || first x "[]") = true → ls'.length = ls.length) := by
    intro x s ls hk hs hls
    by_cases hfs : first x "[]" = true
    · cases hv : ρ x
      case objAt fs cd o =>
        rw [hv] at hs
        have hl : fs.lookup (.str "[]") = some s := by
          simpa [Footprints.fieldsOf, arraySpineKey] using Footprints.spineOf_lookup hs
        exact ⟨ls, hf x "[]" fs cd o s _ hfs hv hl hls, Nat.le_refl _, fun _ => rfl⟩
      all_goals rw [hv] at hs; simp [Footprints.spineOf, Footprints.fieldsOf] at hs
    · simp only [hfs, Bool.or_false] at hk ⊢
      cases hcs : c.spine with
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
  | apart a p b q =>
    simp only [keptBy, Bool.and_eq_true, beq_iff_eq] at hk
    obtain ⟨u, w, hu, hw, hr⟩ := hF
    exact ⟨u, w, readPath_guardKept hf hk.1.2 hu, readPath_guardKept hf hk.2 hw, regionsApart_kept hc hk.1.1 hr⟩
  | spineApart a p b q =>
    simp only [keptBy, Bool.and_eq_true] at hk
    obtain ⟨u, w, hu, hw, hne⟩ := hF
    exact ⟨u, w, readPath_guardKept hf hk.1 hu, readPath_guardKept hf hk.2 hw, hne⟩
  | elemSpineApart _ _ _ _ => simp [keptBy] at hk
  | same _ _ => exact hF
  | guarded s p t B ih =>
    simp only [keptBy, Bool.and_eq_true] at hk
    obtain ⟨v, hv, hor⟩ := hF
    exact ⟨v, readGuard_kept hf hk.1 hv, hor.imp id (ih hk.2)⟩
  | element _ _ _ => simp [keptBy] at hk
  | fieldRead _ o fld => exact readPath_guardKept hf hk hF
  | every _ _ _ _ => simp [keptBy] at hk
  | atIndex _ _ _ _ _ => simp [keptBy] at hk
  | index k => exact hF
  | int k => exact hF
  | pastSafe k => exact hF
  | length x m =>
    simp only [keptBy] at hk
    obtain ⟨s, ls, hs, hls, hm, hmax⟩ := hF
    have hk' : (c.spine != .any || first x "[]") = true := by
      rcases Bool.or_eq_true_iff.mp hk with h1 | h1
      · cases hcs : c.spine <;> simp_all [Changes.keepsLength]
      · simp [h1]
    obtain ⟨ls', hls', -, heq⟩ := spine hk' hs hls
    have heq := heq hk
    exact ⟨s, ls', hs, hls', heq ▸ hm, heq ▸ hmax⟩
  | bound x k st =>
    simp only [keptBy] at hk
    obtain ⟨s, ls, b, i, hs, hls, hb, hi, hle⟩ := hF
    obtain ⟨ls', hls', hgrow, -⟩ := spine hk hs hls
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


/-- Whether a change keeps the length of a typed array read through one
field (`view-path-stable`): the field's location is one `first` keeps or holds
an object the change keeps; the length is the typed array's descriptor's. -/
def Term.viewFramed (c : Changes) (first : Nat → String → Bool) (t : Term) : Bool :=
  t.kind == .view && match t.path with
    | [g] => first t.slot g || !c.obj
    | _ => false

theorem termValue_viewFramed {c : Changes} {first : Nat → String → Bool} {ρ : Env} {h h' : Heap}
    {t : Term} {n : Int} (hc : c.Holds h h') (hf : FirstKept first ρ h h')
    (hk : t.viewFramed c first = true) (ht : termValue ε ρ h t = some n) : termValue ε ρ h' t = some n := by
  obtain ⟨kind, s, p, a⟩ := t
  cases a
  case true => exact termValue_entry_some rfl ht
  simp only [Term.viewFramed, Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨rfl, hp⟩ := hk
  match p, hp with
  | [g], hp =>
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hp
    have hfirst := hp
    simp only [termValue, termAt, Bool.false_eq_true, ite_false, Option.bind_eq_some_iff] at ht ⊢
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
            · obtain ⟨fs, o, st, fm, N, rfl, -⟩ := viewLengthOf_inv hkw
              exact hc.1 l _ hu (by simp [Changes.alters, hobj])
          exact ⟨u, by simp [hu'], hkw⟩
        · cases hw
      · cases hw
    all_goals rw [hs] at hw; simp [readPath] at hw

namespace IndexFact

/-- Whether a change preserves a fact, each of its terms kept by `Term.keptBy` or
framed by `Term.viewFramed`, or the fact kept by `keptBy`. -/
def keptWith (c : Changes) (first : Nat → String → Bool) : IndexFact → Bool
  | .linear F => (F.vars.all fun t => t.keptBy c first || t.viewFramed c first) ||
      (IndexFact.linear F).keptBy c first
  | F => F.keptBy c first

theorem holdsAt_keptWith {c : Changes} {first : Nat → String → Bool} {F : IndexFact} {ρ : Env} {h h' : Heap}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h')
    (hk : F.keptWith c first = true) (hF : F.HoldsAt ε ρ h) : F.HoldsAt ε ρ h' := by
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
    · exact termValue_viewFramed hc hf hk hm
  | index _ => exact holdsAt_kept hc hf (by simp [keptWith] at hk ⊢; exact hk) hF
  | int _ => exact holdsAt_kept hc hf (by simp [keptWith] at hk ⊢; exact hk) hF
  | pastSafe _ => exact holdsAt_kept hc hf (by simp [keptWith] at hk ⊢; exact hk) hF
  | length _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | bound _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | either _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | guarded _ _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | element _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | fieldRead _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | every _ _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | atIndex _ _ _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | apart _ _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | spineApart _ _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | elemSpineApart _ _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | same _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF

end IndexFact


end Verification.HeapKnowledge
