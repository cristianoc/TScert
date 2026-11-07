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
the array's store field read. -/
inductive IndexFact where
  | index (slot : Nat)
  | length (array length : Nat)
  | bound (array index : Nat) (strict : Bool)
  | int (slot : Nat)
  | linear (fact : Linear.Fact Term)
  deriving DecidableEq, Repr, Hashable

namespace IndexFact

/-- The slots a fact names. -/
def slots : IndexFact → List Nat
  | .index k => [k]
  | .length x n => [x, n]
  | .bound x k _ => [x, k]
  | .int k => [k]
  | .linear F => F.vars.map Term.slot

/-- The fact with each slot renamed by a partial map, where it maps every slot. -/
def mapM (f : Nat → Option Nat) : IndexFact → Option IndexFact
  | .index k => (f k).map .index
  | .length x n => do pure (.length (← f x) (← f n))
  | .bound x k st => do pure (.bound (← f x) (← f k) st)
  | .int k => (f k).map .int
  | .linear F => (F.mapVars (Term.mapM f)).map .linear

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

theorem holdsAt_mapM {F F' : IndexFact} {f : Nat → Option Nat} {ρ ρ' : Env} {h : Heap}
    (hm : F.mapM f = some F') (hf : ∀ s ∈ F.slots, ∀ t, f s = some t → ρ' t = ρ s) :
    F'.HoldsAt ρ' h ↔ F.HoldsAt ρ h := by
  cases F with
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

/-- A fact reads its slots' values alone. -/
theorem holdsAt_map {F : IndexFact} {f : Nat → Nat} {ρ ρ' : Env} {h : Heap}
    (hf : ∀ s ∈ F.slots, ρ' (f s) = ρ s) : (F.map f).HoldsAt ρ' h ↔ F.HoldsAt ρ h := by
  obtain ⟨G, hG⟩ : ∃ G, F.mapM (some ∘ f) = some G := by
    cases F with
    | index k => exact ⟨_, rfl⟩
    | length x n => exact ⟨_, rfl⟩
    | bound x k st => exact ⟨_, rfl⟩
    | int k => exact ⟨_, rfl⟩
    | linear G =>
      obtain ⟨G', h⟩ := Linear.Fact.mapVars_some (Term.mapM' f) G
      exact ⟨.linear G', by simp only [mapM, Term.mapM_eq, h, Option.map_some]⟩
  simp only [map, hG, Option.getD_some]
  exact holdsAt_mapM hG (fun s hs t ht => by cases ht; exact hf s hs)

/-- A heap extension keeps a fact: the store lies in the old heap. -/
theorem holdsAt_extend {F : IndexFact} {ρ : Env} {h : Heap} (vs : List Val) (hF : F.HoldsAt ρ h) :
    F.HoldsAt ρ (h ++ vs) := by
  cases F with
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
  cases F with
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

end IndexFact

end Verification.HeapKnowledge
