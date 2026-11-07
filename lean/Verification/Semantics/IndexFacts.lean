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

/-- A term of a linear fact: the safe integer a slot holds (`value`); the
length of the array store a slot holds (`length`), as the calculus's `lenOf`
gives it (`Step.lenV`), at most `maxArrayLength`; or the element count of
the typed array a slot holds (`view`), the safe integer at least `0` the
location of its `viewLengthKey` holds (`viewLengthOf`). -/
inductive Term where
  | value (slot : Nat)
  | length (slot : Nat)
  | view (slot : Nat)
  deriving DecidableEq, Repr, Hashable

namespace Term

/-- The slot a term reads. -/
def slot : Term → Nat
  | .value s | .length s | .view s => s

/-- Whether a term reads the environment alone. -/
def envOnly : Term → Bool
  | .value _ => true
  | .length _ | .view _ => false

/-- An order on terms, by slot and kind, which normal forms sort by. -/
def code : Term → Nat
  | .value s => 3 * s
  | .length s => 3 * s + 1
  | .view s => 3 * s + 2

instance : LT Term := ⟨fun a b => a.code < b.code⟩

instance : DecidableRel (α := Term) (· < ·) := fun a b => inferInstanceAs (Decidable (a.code < b.code))

/-- The term with its slot renamed, where the map names one. -/
def mapM (f : Nat → Option Nat) : Term → Option Term
  | .value s => (f s).map .value
  | .length s => (f s).map .length
  | .view s => (f s).map .view

theorem mapM_slot {f : Nat → Option Nat} {t t' : Term} (h : t.mapM f = some t') : f t.slot = some t'.slot := by
  cases t <;> simp only [mapM, Option.map_eq_some_iff] at h <;> obtain ⟨s, hs, rfl⟩ := h <;> exact hs

/-- The term with its slot renamed by a total map. -/
def mapM' (f : Nat → Nat) : Term → Term
  | .value s => .value (f s)
  | .length s => .length (f s)
  | .view s => .view (f s)

theorem mapM_eq (f : Nat → Nat) : Term.mapM (some ∘ f) = some ∘ mapM' f := by
  funext t; cases t <;> rfl

/-- What a term reads of its slot: the value, the array store's length, or
the typed array's element count. -/
inductive Kind where
  | value
  | length
  | view
  deriving DecidableEq, Repr

/-- The term of a kind at a slot. -/
def ofKind : Kind → Nat → Term
  | .value => .value
  | .length => .length
  | .view => .view

end Term

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

/-- The integer a term denotes, where it denotes one. -/
def termValue (ρ : Env) (h : Heap) : Term → Option Int
  | .value s => intValue (ρ s)
  | .length s => lengthOf h (ρ s)
  | .view s => viewLengthOf h (ρ s)

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
  cases t <;> simp_all [Term.envOnly, termValue]

theorem termValue_extend {ρ : Env} {h : Heap} (vs : List Val) {t : Term} {n : Int} (ht : termValue ρ h t = some n) :
    termValue ρ (h ++ vs) t = some n := by
  cases t with
  | value s => exact ht
  | length s => exact lengthOf_extend vs ht
  | view s => exact viewLengthOf_extend vs ht

/-- An index fact (DESIGN of the guarded write, PROGRAM-TYPING.md, "Writes at
a checked index"): the slot `k` holds a number that is an array index
(`index`); the slot `n` holds the length of the store the array in slot `x`
holds (`length`); the slot `k` holds an array index at most that length
(`bound`), below it where `strict`; the slot `k` holds a safe integer (`int`); the slots of a linear
fact denote safe integers meeting it (`linear`, PROGRAM-TYPING.md, "Linear
facts"), its terms a slot's value or the length of what a slot holds.
`index`, `int` and a linear fact of values read no heap; the others read
the location of the array's store field. -/
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
      cases x <;> simp only [Term.mapM, Option.map_eq_some_iff] at hy <;> obtain ⟨s, _, rfl⟩ := hy <;>
        simp only [termValue, Term.slot] at hs ⊢ <;> rw [hs]
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
      cases t <;> simp only [termValue, Term.slot] at this ⊢ <;> rw [this]
    rw [Linear.Fact.holds_congr (v' := termValuation ρ' h) (fun t ht => by simp only [termValuation, heq t ht])]
    exact ⟨fun ⟨a, b⟩ => ⟨fun t hm => heq t hm ▸ a t hm, b⟩, fun ⟨a, b⟩ => ⟨fun t hm => (heq t hm).symm ▸ a t hm, b⟩⟩

/-- A linear fact over slots' values holds where its slots hold safe integers
meeting it. -/
theorem holdsAt_valueFact {F : Linear.Fact Nat} {ρ : Env} {h : Heap} :
    (IndexFact.linear (valueFact F)).HoldsAt ρ h ↔ (∀ x ∈ F.vars, (intValue (ρ x)).isSome) ∧ F.Holds (valuation ρ) := by
  simp only [HoldsAt, vars_valueFact, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    termValue, holds_valueFact]

/-- A linear fact whose terms read the environment alone holds in every heap. -/
theorem holdsAt_linear_heap {F : Linear.Fact Term} {ρ : Env} {h h' : Heap} (hv : F.vars.all Term.envOnly = true)
    (hF : (IndexFact.linear F).HoldsAt ρ h) : (IndexFact.linear F).HoldsAt ρ h' := by
  have heq : ∀ t ∈ F.vars, termValue ρ h t = termValue ρ h' t :=
    fun t ht => termValue_envOnly (List.all_eq_true.mp hv t ht)
  refine ⟨fun t ht => heq t ht ▸ hF.1 t ht, ?_⟩
  exact (Linear.Fact.holds_congr (v' := termValuation ρ h') (fun t ht => by simp only [termValuation, heq t ht])).mp hF.2

end IndexFact

end Verification.HeapKnowledge
