import Verification.Semantics.ClosedFootprints
import Verification.Semantics.SafeIntegers
import Verification.Semantics.Linear

/-! Index facts: what a slot holds as an array index, a length, a bound by a
store's length, a safe integer or a linear fact (PROGRAM-TYPING.md, "Writes at
a checked index" and "Linear facts"). Heap knowledge carries them as atoms
(`HeapKnowledge.IndexAtom`); a signature states its precondition with them
(`CallEffects.Effect.pre`). -/
namespace Verification.HeapKnowledge

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
(`value`), the length of its array store (`length`), or the element count of
the typed array it is (`view`). -/
inductive Term.Kind where
  | value
  | length
  | view
  deriving DecidableEq, Repr, Hashable

/-- A term of a linear fact (PROGRAM-TYPING.md, "Linear facts"): a root slot,
a path of named data fields read in turn from the value it holds, and what
the term reads of the value the path ends at (`Term.Kind`): the safe integer
it is; the length of its array store, as the calculus's `lenOf` gives it
(`Step.lenV`), at most `maxArrayLength`; or the element count of the typed
array it is, the safe integer at least `0` the location of its
`viewLengthKey` holds (`viewLengthOf`). The empty path reads the slot's
value itself. -/
structure Term where
  kind : Term.Kind
  slot : Nat
  path : List String
  deriving DecidableEq, Repr, Hashable

namespace Term

/-- The safe integer a slot holds. -/
def value (s : Nat) : Term := ⟨.value, s, []⟩
/-- The length of the array store a slot holds. -/
def length (s : Nat) : Term := ⟨.length, s, []⟩
/-- The element count of the typed array a slot holds. -/
def view (s : Nat) : Term := ⟨.view, s, []⟩

/-- The term of a kind at a slot, its path empty. -/
def ofKind (k : Kind) (s : Nat) : Term := ⟨k, s, []⟩

/-- Whether a term reads the environment alone: a slot's own value. -/
def envOnly (t : Term) : Bool := t.kind == .value && t.path.isEmpty

def Kind.code : Kind → Nat
  | .value => 0
  | .length => 1
  | .view => 2

/-- A term's place by slot and kind, which normal forms sort by. -/
def code (t : Term) : Nat := 3 * t.slot + t.kind.code

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

/-- The term with its slot renamed, where the map names one. -/
def mapM (f : Nat → Option Nat) (t : Term) : Option Term := (f t.slot).map fun s => { t with slot := s }

theorem mapM_slot {f : Nat → Option Nat} {t t' : Term} (h : t.mapM f = some t') : f t.slot = some t'.slot := by
  simp only [mapM, Option.map_eq_some_iff] at h
  obtain ⟨s, hs, rfl⟩ := h
  exact hs

theorem mapM_eq_some {f : Nat → Option Nat} {t t' : Term} (h : t.mapM f = some t') :
    t' = { t with slot := t'.slot } := by
  simp only [mapM, Option.map_eq_some_iff] at h
  obtain ⟨s, -, rfl⟩ := h
  rfl

/-- The term with its slot renamed by a total map. -/
def mapM' (f : Nat → Nat) (t : Term) : Term := { t with slot := f t.slot }

theorem mapM_eq (f : Nat → Nat) : Term.mapM (some ∘ f) = some ∘ mapM' f := by
  funext t; rfl

end Term

/-- The value a path of named data fields reads from a value: each step an
object owning the field as a string key, whose location the heap
allocates. -/
def readPath (h : Heap) : Val → List String → Option Val
  | v, [] => some v
  | .objAt fs _ _, f :: p => match fs.lookup (.str f) with
    | some l => match h[l]? with
      | some v => readPath h v p
      | none => none
    | none => none
  | _, _ :: _ => none

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

/-- What a guard compares the value a path reads with (PROGRAM-TYPING.md,
"Guarded clauses"): `null` or `undefined`. -/
inductive GuardTag where
  | null
  | undef
  deriving DecidableEq, Repr, Hashable

/-- The value a guard tag names. -/
def GuardTag.val : GuardTag → Val
  | .null => .nul
  | .undef => .undef

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

/-- The element count of the typed array a value is, read in the heap: the
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

/-- A heap extension keeps the element count of what a value is: its
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

/-- What a kind of term reads of a value. -/
def kindValue (h : Heap) : Term.Kind → Val → Option Int
  | .value, v => intValue v
  | .length, v => lengthOf h v
  | .view, v => viewLengthOf h v

/-- The integer a term denotes, where it denotes one: what its kind reads of
the value its path reads from its slot's value. -/
def termValue (ρ : Env) (h : Heap) (t : Term) : Option Int :=
  (readPath h (ρ t.slot) t.path).bind (kindValue h t.kind)

theorem termValue_nil {ρ : Env} {h : Heap} {k : Term.Kind} {s : Nat} :
    termValue ρ h ⟨k, s, []⟩ = kindValue h k (ρ s) := rfl

@[simp] theorem termValue_value {ρ : Env} {h : Heap} {s : Nat} : termValue ρ h (.value s) = intValue (ρ s) := rfl
@[simp] theorem termValue_length {ρ : Env} {h : Heap} {s : Nat} : termValue ρ h (.length s) = lengthOf h (ρ s) := rfl
@[simp] theorem termValue_view {ρ : Env} {h : Heap} {s : Nat} : termValue ρ h (.view s) = viewLengthOf h (ρ s) := rfl

theorem termValue_slot {ρ ρ' : Env} {h : Heap} {t : Term} {s : Nat} (hs : ρ' s = ρ t.slot) :
    termValue ρ' h { t with slot := s } = termValue ρ h t := by
  simp only [termValue, hs]

theorem termValue_isSome {ρ : Env} {h : Heap} {t : Term} (ht : (termValue ρ h t).isSome) :
    ∃ v n, readPath h (ρ t.slot) t.path = some v ∧ kindValue h t.kind v = some n ∧ termValue ρ h t = some n := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ht
  simp only [termValue, Option.bind_eq_some_iff] at hn
  obtain ⟨v, hv, hk⟩ := hn
  exact ⟨v, n, hv, hk, by simp [termValue, hv, hk]⟩

/-- The integers terms denote, `0` where one denotes none: the valuation the
linear facts are read at. -/
def termValuation (ρ : Env) (h : Heap) (t : Term) : Int := (termValue ρ h t).getD 0

/-- A linear form over slots' values as one over value terms. -/
def valueForm (F : Linear.Form Nat) : Linear.Form Term := F.map fun p => (.value p.1, p.2)

/-- A linear fact over slots' values as one over value terms. -/
def valueFact : Linear.Fact Nat → Linear.Fact Term
  | .le F d => .le (valueForm F) d
  | .ne F d => .ne (valueForm F) d

theorem eval_valueForm (ρ : Env) (h : Heap) (F : Linear.Form Nat) :
    Linear.Form.eval (termValuation ρ h) (valueForm F) = Linear.Form.eval (valuation ρ) F := by
  induction F with
  | nil => rfl
  | cons p t ih => simp only [valueForm, List.map_cons, Linear.Form.eval] at ih ⊢; rw [ih]; rfl

theorem holds_valueFact {ρ : Env} {h : Heap} {F : Linear.Fact Nat} :
    (valueFact F).Holds (termValuation ρ h) ↔ F.Holds (valuation ρ) := by
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
    termValue ρ h t = termValue ρ h' t := by
  obtain ⟨k, s, p⟩ := t
  simp only [Term.envOnly, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at ht
  obtain ⟨rfl, rfl⟩ := ht
  rfl

theorem kindValue_extend {h : Heap} (vs : List Val) {k : Term.Kind} {v : Val} {n : Int} (hk : kindValue h k v = some n) :
    kindValue (h ++ vs) k v = some n := by
  cases k with
  | value => exact hk
  | length => exact lengthOf_extend vs hk
  | view => exact viewLengthOf_extend vs hk

theorem termValue_extend {ρ : Env} {h : Heap} (vs : List Val) {t : Term} {n : Int} (ht : termValue ρ h t = some n) :
    termValue ρ (h ++ vs) t = some n := by
  simp only [termValue, Option.bind_eq_some_iff] at ht ⊢
  obtain ⟨v, hv, hk⟩ := ht
  exact ⟨v, readPath_extend vs hv, kindValue_extend vs hk⟩

/-- An index fact (DESIGN of the guarded write, PROGRAM-TYPING.md, "Writes at
a checked index"): the slot `k` holds a number that is an array index
(`index`); the slot `n` holds the length of the store the array in slot `x`
holds (`length`); the slot `k` holds an array index at most that length
(`bound`), below it where `strict`; the slot `k` holds a safe integer (`int`); the slots of a linear
fact denote integers meeting it (`linear`, PROGRAM-TYPING.md, "Linear
facts"), its terms (`Term`) rooted at slots. `index`, `int` and a linear fact
of slots' values read no heap; the others read the locations their terms or
the array's store field read. A guarded fact (`guarded`, PROGRAM-TYPING.md,
"Guarded clauses") holds where the path `path` from the slot `slot` reads a
value (`readGuard`) that is the tag's, or its body holds. -/
inductive IndexFact where
  | index (slot : Nat)
  | length (array length : Nat)
  | bound (array index : Nat) (strict : Bool)
  | int (slot : Nat)
  | linear (fact : Linear.Fact Term)
  | guarded (slot : Nat) (path : List String) (tag : GuardTag) (body : IndexFact)
  deriving DecidableEq, Repr, Hashable

namespace IndexFact

/-- The slots a fact names. -/
def slots : IndexFact → List Nat
  | .index k => [k]
  | .length x n => [x, n]
  | .bound x k _ => [x, k]
  | .int k => [k]
  | .linear F => F.vars.map Term.slot
  | .guarded s _ _ B => s :: B.slots

/-- The fact with each slot renamed by a partial map, where it maps every slot. -/
def mapM (f : Nat → Option Nat) : IndexFact → Option IndexFact
  | .index k => (f k).map .index
  | .length x n => do pure (.length (← f x) (← f n))
  | .bound x k st => do pure (.bound (← f x) (← f k) st)
  | .int k => (f k).map .int
  | .linear F => (F.mapVars (Term.mapM f)).map .linear
  | .guarded s p t B => do pure (.guarded (← f s) p t (← B.mapM f))

/-- The fact with each slot renamed. -/
def map (f : Nat → Nat) (F : IndexFact) : IndexFact := (F.mapM (some ∘ f)).getD F

def HoldsAt : IndexFact → Env → Heap → Prop
  | .index k, ρ, _ => ∃ b i, ρ k = .num b ∧ indexOfBits b = some i
  | .length x n, ρ, h => ∃ s ls, Footprints.storeOf (ρ x) = some s ∧ h[s]? = some (.arr ls) ∧
      ρ n = .num (bitsOfNat ls.length) ∧ ls.length ≤ maxArrayLength
  | .bound x k st, ρ, h => ∃ s ls b i, Footprints.storeOf (ρ x) = some s ∧ h[s]? = some (.arr ls) ∧
      ρ k = .num b ∧ indexOfBits b = some i ∧ i + (if st then 1 else 0) ≤ ls.length
  | .int k, ρ, _ => (intValue (ρ k)).isSome
  | .linear F, ρ, h => (∀ t ∈ F.vars, (termValue ρ h t).isSome) ∧ F.Holds (termValuation ρ h)
  | .guarded s p t B, ρ, h => ∃ v, readGuard h (ρ s) p = some v ∧ (v = t.val ∨ B.HoldsAt ρ h)

theorem holdsAt_mapM {F F' : IndexFact} {f : Nat → Option Nat} {ρ ρ' : Env} {h : Heap}
    (hm : F.mapM f = some F') (hf : ∀ s ∈ F.slots, ∀ t, f s = some t → ρ' t = ρ s) :
    F'.HoldsAt ρ' h ↔ F.HoldsAt ρ h := by
  induction F generalizing F' with
  | guarded s p t B ih =>
    simp only [mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
    obtain ⟨s', hs, B', hB, rfl⟩ := hm
    have hB' := ih hB (fun x hx y hy => hf x (by simp [slots, hx]) y hy)
    simp only [HoldsAt, hf s (by simp [slots]) s' hs, hB']
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
  | linear G =>
    simp only [mapM, Option.map_eq_some_iff] at hm
    obtain ⟨G', hG, rfl⟩ := hm
    simp only [HoldsAt]
    -- A renamed term denotes what its source denotes: its slot holds the same value.
    have hterm : ∀ x ∈ G.vars, ∀ y, x.mapM f = some y → termValue ρ' h y = termValue ρ h x := by
      intro x hx y hy
      have hs := hf x.slot (List.mem_map_of_mem hx) y.slot (Term.mapM_slot hy)
      rw [Term.mapM_eq_some hy]
      exact termValue_slot hs
    have hv : ∀ x ∈ G.vars, ∀ y, x.mapM f = some y → termValuation ρ' h y = termValuation ρ h x := by
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
    (hm : F.mapVars f = some F') (hf : ∀ x ∈ F.vars, ∀ y, f x = some y → termValue ρ h y = termValue ρ h x) :
    (linear F').HoldsAt ρ h ↔ (linear F).HoldsAt ρ h := by
  have hv : ∀ x ∈ F.vars, ∀ y, f x = some y → termValuation ρ h y = termValuation ρ h x := by
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

/-- A total renaming renames every fact. -/
theorem mapM_total (f : Nat → Nat) : ∀ F : IndexFact, ∃ G, F.mapM (some ∘ f) = some G
  | .index k => ⟨_, rfl⟩
  | .length x n => ⟨_, rfl⟩
  | .bound x k st => ⟨_, rfl⟩
  | .int k => ⟨_, rfl⟩
  | .linear G => by
    obtain ⟨G', h⟩ := Linear.Fact.mapVars_some (Term.mapM' f) G
    exact ⟨.linear G', by simp only [mapM, Term.mapM_eq, h, Option.map_some]⟩
  | .guarded s p t B => by
    obtain ⟨B', hB⟩ := mapM_total f B
    exact ⟨.guarded (f s) p t B', by simp [mapM, hB]⟩

/-- A fact reads its slots' values alone. -/
theorem holdsAt_map {F : IndexFact} {f : Nat → Nat} {ρ ρ' : Env} {h : Heap}
    (hf : ∀ s ∈ F.slots, ρ' (f s) = ρ s) : (F.map f).HoldsAt ρ' h ↔ F.HoldsAt ρ h := by
  obtain ⟨G, hG⟩ := mapM_total f F
  simp only [map, hG, Option.getD_some]
  exact holdsAt_mapM hG (fun s hs t ht => by cases ht; exact hf s hs)

/-- A heap extension keeps a fact: the store lies in the old heap. -/
theorem holdsAt_extend {F : IndexFact} {ρ : Env} {h : Heap} (vs : List Val) (hF : F.HoldsAt ρ h) :
    F.HoldsAt ρ (h ++ vs) := by
  induction F with
  | guarded s p t B ih =>
    obtain ⟨v, hv, hor⟩ := hF
    exact ⟨v, readGuard_extend vs hv, hor.imp id ih⟩
  | index k => exact hF
  | length x n =>
    obtain ⟨s, ls, hs, hl, hn⟩ := hF
    exact ⟨s, ls, hs, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl, hn⟩
  | bound x k st =>
    obtain ⟨s, ls, b, i, hs, hl, hk, hi, hle⟩ := hF
    exact ⟨s, ls, b, i, hs, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hl).1]; exact hl,
      hk, hi, hle⟩
  | int k => exact hF
  | linear G =>
    obtain ⟨hi, hh⟩ := hF
    have heq : ∀ t ∈ G.vars, termValue ρ (h ++ vs) t = termValue ρ h t := by
      intro t ht
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hi t ht)
      rw [hn, termValue_extend vs hn]
    refine ⟨fun t ht => by rw [heq t ht]; exact hi t ht, ?_⟩
    rw [Linear.Fact.holds_congr (v' := termValuation ρ h) (fun t ht => by simp only [termValuation, heq t ht])]
    exact hh

/-- A fact reads the values of the slots it names alone. -/
theorem holdsAt_congr {F : IndexFact} {ρ ρ' : Env} {h : Heap} (hs : ∀ s ∈ F.slots, ρ s = ρ' s) :
    F.HoldsAt ρ h ↔ F.HoldsAt ρ' h := by
  induction F with
  | guarded s p t B ih =>
    simp only [slots, List.mem_cons, forall_eq_or_imp] at hs
    simp only [HoldsAt, hs.1, ih hs.2]
  | index k => simp only [slots, List.mem_singleton, forall_eq] at hs; simp only [HoldsAt, hs]
  | length x n =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2]
  | bound x k st =>
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
    simp only [HoldsAt, hs.1, hs.2]
  | int k => simp only [slots, List.mem_singleton, forall_eq] at hs; simp only [HoldsAt, hs]
  | linear G =>
    simp only [slots] at hs
    simp only [HoldsAt]
    have heq : ∀ t ∈ G.vars, termValue ρ h t = termValue ρ' h t := by
      intro t ht
      have := hs t.slot (List.mem_map_of_mem ht)
      simp only [termValue, this]
    rw [Linear.Fact.holds_congr (v' := termValuation ρ' h) (fun t ht => by simp only [termValuation, heq t ht])]
    exact ⟨fun ⟨a, b⟩ => ⟨fun t hm => heq t hm ▸ a t hm, b⟩, fun ⟨a, b⟩ => ⟨fun t hm => (heq t hm).symm ▸ a t hm, b⟩⟩

/-- A linear fact over slots' values holds where its slots hold safe integers
meeting it. -/
theorem holdsAt_valueFact {F : Linear.Fact Nat} {ρ : Env} {h : Heap} :
    (IndexFact.linear (valueFact F)).HoldsAt ρ h ↔ (∀ x ∈ F.vars, (intValue (ρ x)).isSome) ∧ F.Holds (valuation ρ) := by
  simp only [HoldsAt, vars_valueFact, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    termValue_value, holds_valueFact]

/-- A linear fact whose terms read the environment alone holds in every heap. -/
theorem holdsAt_linear_heap {F : Linear.Fact Term} {ρ : Env} {h h' : Heap} (hv : F.vars.all Term.envOnly = true)
    (hF : (IndexFact.linear F).HoldsAt ρ h) : (IndexFact.linear F).HoldsAt ρ h' := by
  have heq : ∀ t ∈ F.vars, termValue ρ h t = termValue ρ h' t :=
    fun t ht => termValue_envOnly (List.all_eq_true.mp hv t ht)
  refine ⟨fun t ht => heq t ht ▸ hF.1 t ht, ?_⟩
  exact (Linear.Fact.holds_congr (v' := termValuation ρ h') (fun t ht => by simp only [termValuation, heq t ht])).mp hF.2

/-- A linear fact holds in a heap where each of its terms denotes what it
denoted in the heap the fact held in. -/
theorem holdsAt_linear_terms {F : Linear.Fact Term} {ρ : Env} {h h' : Heap}
    (heq : ∀ t ∈ F.vars, termValue ρ h' t = termValue ρ h t)
    (hF : (IndexFact.linear F).HoldsAt ρ h) : (IndexFact.linear F).HoldsAt ρ h' := by
  refine ⟨fun t ht => by rw [heq t ht]; exact hF.1 t ht, ?_⟩
  exact (Linear.Fact.holds_congr (v' := termValuation ρ h')
    (fun t ht => by simp only [termValuation, heq t ht])).mp hF.2

end IndexFact

/-! ## Facts a heap change keeps (PROGRAM-TYPING.md, "Linear facts")

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

/-- The change a closed footprint allows: `grow` on a value is `keep`. -/
def ofClosed (Φ : Footprints.Closed) : Changes :=
  ⟨Φ.value == .any, Φ.value == .any, if Φ.store == .keep then .keep else .any⟩

theorem ofClosed_holds {Φ : Footprints.Closed} {h h' : Heap} (hp : Φ.Holds h h') : (ofClosed Φ).Holds h h' := by
  rw [Footprints.Closed.holds_iff] at hp
  refine ⟨fun l v hv ha => ?_, fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨v', hv', hc⟩ := hp.2 l v hv
    have hkeep : v' = v := by
      cases v
      case arr ls =>
        simp only [alters, ofClosed] at ha
        have hst : Φ.store = .keep := by
          cases hΦ : Φ.store <;> simp_all
        simp only [Footprints.Closed.at, Footprints.isArr, hst, ite_true] at hc
        exact hc
      all_goals
        have hva : Φ.value ≠ .any := by
          intro he; simp [alters, ofClosed, he] at ha
        simp only [Footprints.Closed.at, Footprints.isArr] at hc
        cases hΦ : Φ.value
        · rw [hΦ] at hc; exact hc
        · rw [hΦ] at hc; exact hc.grow_value rfl
        · exact absurd hΦ hva
    exact hkeep ▸ hv'
  · revert hs; simp only [ofClosed]; split <;> simp
  · revert hs; simp only [ofClosed]; split <;> simp

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
  t.pathKeptBy c first &&
  (match t.kind with
    | .value => true
    | .length => c.keepsLength || (t.path.isEmpty && first t.slot "[]")
    | .view => !c.num)

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
    (hpath : Term.pathKeptBy c first ⟨kind, s, p⟩ = true)
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
    (ht : termValue ρ h t = some n) : termValue ρ h' t = some n := by
  obtain ⟨kind, s, p⟩ := t
  simp only [termValue, Option.bind_eq_some_iff] at ht ⊢
  obtain ⟨w, hw, hkw⟩ := ht
  simp only [Term.keptBy, Term.pathKeptBy, Bool.and_eq_true] at hk
  obtain ⟨hpath, hkind⟩ := hk
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
      | .view => !c.num) = true := by
    cases kind with
    | value => rfl
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
    (ht : termValue ρ h t = some n) : ∃ n', termValue ρ h' t = some n' ∧ n ≤ n' := by
  obtain ⟨kind, s, p⟩ := t
  simp only [Term.grownBy, Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨⟨rfl, hs⟩, hpath⟩ := hg
  simp only [termValue, Option.bind_eq_some_iff] at ht ⊢
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
      (∀ t ∈ F.map (·.1), (termValue ρ h t).isSome) →
      (∀ t ∈ F.map (·.1), (termValue ρ h' t).isSome) ∧
        Linear.Form.eval (termValuation ρ h') F ≤ Linear.Form.eval (termValuation ρ h) F
  | [], _, _ => ⟨by simp, Int.le_refl _⟩
  | (t, a) :: F, hk, hd => by
    simp only [Term.formKeptBy, List.all_cons, Bool.and_eq_true] at hk
    obtain ⟨hk1, hk2⟩ := hk
    obtain ⟨hdr, hev⟩ := formKept_eval hc hf (F := F) hk2 (fun u hu => hd u (by simp [hu]))
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hd t (by simp))
    have hv : termValuation ρ h t = n := by simp [termValuation, hn]
    rcases Bool.or_eq_true_iff.mp hk1 with hkt | hgt
    · have hn' := termValue_kept hc hf hkt hn
      have hv' : termValuation ρ h' t = n := by simp [termValuation, hn']
      refine ⟨fun u hu => ?_, ?_⟩
      · simp only [List.map_cons, List.mem_cons] at hu
        rcases hu with rfl | hu
        · simp [hn']
        · exact hdr u hu
      · simp only [Linear.Form.eval, hv, hv']; omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hgt
      obtain ⟨ha, hg⟩ := hgt
      obtain ⟨n', hn', hle⟩ := termValue_grown hc hf hg hn
      have hv' : termValuation ρ h' t = n' := by simp [termValuation, hn']
      refine ⟨fun u hu => ?_, ?_⟩
      · simp only [List.map_cons, List.mem_cons] at hu
        rcases hu with rfl | hu
        · simp [hn']
        · exact hdr u hu
      · simp only [Linear.Form.eval, hv, hv']
        have : a * n' ≤ a * n := Int.mul_le_mul_of_nonpos_left ha hle
        omega

namespace IndexFact

/-- Whether a change keeps a fact (`Term.keptBy`): `index` and `int` read
no heap, `length` and `bound` a store's length. -/
def keptBy (c : Changes) (first : Nat → String → Bool) : IndexFact → Bool
  | .index _ | .int _ => true
  | .length x _ => c.keepsLength || first x "[]"
  | .bound x _ _ => c.store != .any || first x "[]"
  | .linear F => F.vars.all (Term.keptBy c first) || match F with
    | .le G _ => Term.formKeptBy c first G
    | .ne _ _ => false
  | .guarded s p _ B => guardKept first s p && B.keptBy c first

theorem holdsAt_kept {c : Changes} {first : Nat → String → Bool} {F : IndexFact} {ρ : Env} {h h' : Heap}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hk : F.keptBy c first = true) (hF : F.HoldsAt ρ h) :
    F.HoldsAt ρ h' := by
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
  | guarded s p t B ih =>
    simp only [keptBy, Bool.and_eq_true] at hk
    obtain ⟨v, hv, hor⟩ := hF
    exact ⟨v, readGuard_kept hf hk.1 hv, hor.imp id (ih hk.2)⟩
  | index k => exact hF
  | int k => exact hF
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
      have heq : ∀ t ∈ G.vars, termValue ρ h' t = termValue ρ h t := by
        intro t ht
        obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hi t ht)
        rw [hn, termValue_kept hc hf (hk t ht) hn]
      refine ⟨fun t ht => by rw [heq t ht]; exact hi t ht, ?_⟩
      rw [Linear.Fact.holds_congr (v' := termValuation ρ h) (fun t ht => by simp only [termValuation, heq t ht])]
      exact hh
    · cases G with
      | ne _ _ => simp at hk
      | le G d =>
        simp only at hk
        obtain ⟨hd, hev⟩ := formKept_eval hc hf hk hF.1
        exact ⟨hd, Int.le_trans hev hF.2⟩

end IndexFact


/-- Where `views s g` holds, the view the field `g` of slot `s`'s object held
keeps its element count from `h` to `h'`. -/
def ViewsKept (views : Nat → String → Bool) (ρ : Env) (h h' : Heap) : Prop :=
  ∀ s g fs cd o l w, views s g = true → ρ s = .objAt fs cd o → fs.lookup (.str g) = some l →
    h[l]? = some w → viewLengthOf h' w = viewLengthOf h w

/-- Whether a change keeps the element count of a view read through one
field (`view-path-stable`): the field's location is one `first` keeps or holds
an object the change keeps, and `views` frames the view's count. -/
def Term.viewFramed (c : Changes) (first views : Nat → String → Bool) (t : Term) : Bool :=
  t.kind == .view && match t.path with
    | [g] => (first t.slot g || !c.obj) && views t.slot g
    | _ => false

theorem termValue_viewFramed {c : Changes} {first views : Nat → String → Bool} {ρ : Env} {h h' : Heap}
    {t : Term} {n : Int} (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hv : ViewsKept views ρ h h')
    (hk : t.viewFramed c first views = true) (ht : termValue ρ h t = some n) : termValue ρ h' t = some n := by
  obtain ⟨kind, s, p⟩ := t
  simp only [Term.viewFramed, Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨rfl, hp⟩ := hk
  match p, hp with
  | [g], hp =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hp
    obtain ⟨hfirst, hvs⟩ := hp
    simp only [termValue, Option.bind_eq_some_iff] at ht ⊢
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

/-- Whether a change keeps a fact, each of its terms kept by `Term.keptBy` or
framed by `Term.viewFramed`. -/
def keptWith (c : Changes) (first views : Nat → String → Bool) : IndexFact → Bool
  | .linear F => F.vars.all fun t => t.keptBy c first || t.viewFramed c first views
  | F => F.keptBy c first

theorem holdsAt_keptWith {c : Changes} {first views : Nat → String → Bool} {F : IndexFact} {ρ : Env} {h h' : Heap}
    (hc : c.Holds h h') (hf : FirstKept first ρ h h') (hv : ViewsKept views ρ h h')
    (hk : F.keptWith c first views = true) (hF : F.HoldsAt ρ h) : F.HoldsAt ρ h' := by
  cases F with
  | linear G =>
    simp only [keptWith, List.all_eq_true, Bool.or_eq_true] at hk
    refine holdsAt_linear_terms (fun t ht => ?_) hF
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (hF.1 t ht)
    rw [hm]
    rcases hk t ht with hk | hk
    · exact termValue_kept hc hf hk hm
    · exact termValue_viewFramed hc hf hv hk hm
  | index _ => exact holdsAt_kept hc hf (by simp [keptWith] at hk ⊢; exact hk) hF
  | int _ => exact holdsAt_kept hc hf (by simp [keptWith] at hk ⊢; exact hk) hF
  | length _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | bound _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF
  | guarded _ _ _ _ => exact holdsAt_kept hc hf (by simpa [keptWith] using hk) hF

end IndexFact

end Verification.HeapKnowledge
