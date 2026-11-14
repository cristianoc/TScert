import Verification.Semantics.IndexFacts
import Verification.Semantics.Kinds
/-!
# Element writes and the view-element write

A typed array's element write as a relation between two world-heap pairs
(the Tolerant frames note, kinded worlds; location-kinds draft, §6), and
what it states of the two heaps alone.

- **The view-element write** (`Kinds.ViewWrite`, `Kinds.ViewWriteOf`): the
  exit world extends the entry one, the exit heap meets it in both parts,
  every old location whose role in the entry world is no view store keeps
  its contents, and a view store's newly listed cells are fresh; for the
  exact form, the designated view's element at the index holds the element
  type's conversion of the value (`CallEffects.ExactWrite`,
  `ElementKind.convert`). A call's postcondition states it from the call's
  entry world and heap (`CallEffects.Effect.viewPost`).
- **What it states of the heaps** (`CallEffects.ElementWrite.Holds`): the
  coarse change (`ElementWrite.changes`) and, where exact, `ExactWrite`;
  both follow from the relation from a well-formed entry
  (`Kinds.ViewWriteOf.holds`).

This module is below the call effects (`Semantics/CallEffects.lean`), which
state an element write by these relations.
-/
namespace Verification.CallEffects


/-- A typed array's element type: the element of a `Uint8Array`, a
`Uint16Array`, an `Int32Array` or a `Float64Array` (`%ByteSet%`'s exact
signatures, one per element type). -/
inductive ElementKind where
  | uint8
  | uint16
  | int32
  | float64
  deriving Repr, DecidableEq

/-- **The value an element of type `k` holds after a write of `v`**, for
every value `k` takes (`ElementKind.Takes`: a number denoting a safe integer
within `k`'s range), the host's conversion there (ECMA-262,
NumericToRawBytes, then RawBytesToNumeric; `ElementKind.convert_takes`): an
integer type converts `v` (ToUint8, ToUint16, ToInt32), which within its
range gives the number denoting `v`'s integer (`int32Bits`, so `+0` of
`-0`); a `Float64Array` element holds `v` itself. Every statement of an
exact write applies it to a value `k` takes (`ExactWrite`); on other values
it is the identity, which no statement reads. -/
def ElementKind.convert : ElementKind → Tm → Tm
  | .float64, v => v
  | _, .num b => match SafeIntegers.safeIntOfBits b with
    | some i => .num (int32Bits i)
    | none => .num b
  | _, v => v

/-- The range of an element type's integers: `0` to `255` of a
`Uint8Array`, `0` to `65535` of a `Uint16Array`, `-2^31` to `2^31 - 1` of
an `Int32Array`; a `Float64Array` holds every safe integer. -/
def ElementKind.range : ElementKind → Option (Int × Int)
  | .uint8 => some (0, 255)
  | .uint16 => some (0, 65535)
  | .int32 => some (-2147483648, 2147483647)
  | .float64 => none

/-- **The values an exact write of element type `k` takes**: a number
denoting a safe integer within `k`'s range (`%ByteSet%`'s exact
signatures). -/
def ElementKind.Takes (k : ElementKind) (v : Tm) : Prop :=
  ∃ b i, v = .num b ∧ SafeIntegers.SafeInt b i ∧ ∀ lo hi, k.range = some (lo, hi) → lo ≤ i ∧ i ≤ hi

/-- **The conversion is the host's on every value the element type
takes**: an integer type holds the number denoting the value's integer, the
same integer, `+0` of `-0` (ToUint8, ToUint16 and ToInt32 are the identity on
their range); a `Float64Array` holds the value. -/
theorem ElementKind.convert_takes {k : ElementKind} {b : UInt64} {i : Int}
    (hs : SafeIntegers.SafeInt b i) :
    k.convert (.num b) = if k = .float64 then .num b else .num (int32Bits i) := by
  have hb := SafeIntegers.safeIntOfBits_complete hs
  cases k <;> simp [ElementKind.convert, hb]

/-- The precondition facts of an exact write of element type `k`, at the
call's positions (`3` the value): the value is a safe integer, and, for a
bounded type, at least the range's low end and at most its high end. An
exact effect's precondition states each (`EffectJson`). -/
def ElementKind.preFacts (k : ElementKind) : List HeapKnowledge.IndexFact :=
  .int 3 :: match k.range with
    | none => []
    | some (lo, hi) => [.linear (.le [(.value 3, -1)] (-lo)), .linear (.le [(.value 3, 1)] hi)]

/-- A typed array's element write (`%ByteSet%`, a view's `fill`,
`copyWithin` and `set`; SOURCE-CONTRACTS.md, "Stated library types"). The
model holds a view's elements as a store (`viewElementsKey`) of fixed
length, and a write replaces entries of the stores of the views over the
written bytes by fresh cells (`ElementWrite.Holds`). -/
inductive ElementWrite where
  | stores
  /-- Besides, the element store of the view (the first actual), whose
  element type is `k`, changed only at the index (the second actual, a safe
  integer below its length), whose entry is a location holding `k`'s
  conversion of the value (the third actual, `ElementKind.convert`): each
  element of a view is its own bytes of the buffer, and the value is a safe
  integer within `k`'s range (`%ByteSet%`'s exact signatures). -/
  | exact (k : ElementKind)
  deriving Repr, DecidableEq

/-- The coarse change an element write implies (`ElementWrite.Holds.changes`):
no object or number altered, every store's length kept. The checker frames
facts through it. -/
def ElementWrite.changes : ElementWrite → HeapKnowledge.Changes
  | _ => ⟨false, false, .length⟩

/-- An exact element write of the actuals `args` into a view of element
type `k`: the value (`args[2]`) is one `k` takes (`ElementKind.Takes`), and
where the store of elements of `args[0]` held entries `ls`, it lists after
the call the same entries but at the safe integer `args[1]`, below their
number, where it lists a location holding `k`'s conversion of the value
(`ElementKind.convert`, the host's on what `k` takes). -/
def ExactWrite (k : ElementKind) (args : List Tm) (before after : Heap) : Prop :=
  k.Takes (args.getD 2 .undef) ∧
  ∀ s ls, HeapKnowledge.elementsOf (args.getD 0 .undef) = some s → before[s]? = some (.arr ls) →
    ∃ ls' b, ∃ i : Nat, after[s]? = some (.arr ls') ∧ args.getD 1 .undef = .num b ∧
      SafeIntegers.SafeInt b (i : Int) ∧ i < ls.length ∧ (∀ j, j ≠ i → ls'[j]? = ls[j]?) ∧
      ∃ l, ls'[i]? = some (some l) ∧ after[l]? = some (k.convert (args.getD 2 .undef))

/-- The double `int32Bits i` denotes the safe integer `i`. -/
theorem safeInt_int32Bits {i : Int} (hi : i.natAbs < 2 ^ 53) : SafeIntegers.SafeInt (int32Bits i) i := by
  have hlt := SafeIntegers.bitsOfNat_lt hi
  refine ⟨hi, ?_⟩
  by_cases hn : i < 0
  · refine .inr ⟨by omega, ?_⟩
    have he : (-i).toNat = i.natAbs := by omega
    simp only [int32Bits, if_pos hn, he, UInt64.toNat_or]
    have hor := Nat.two_pow_add_eq_or_of_lt hlt 1
    rw [Nat.mul_one] at hor
    rw [show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl, Nat.or_comm, ← hor]
    omega
  · refine .inl ⟨by omega, ?_⟩
    simp only [int32Bits, if_neg hn]
    congr 3
    omega

/-- **The conversion keeps the integer a value denotes.** -/
theorem ElementKind.intValue_convert (k : ElementKind) (v : Tm) :
    HeapKnowledge.intValue (k.convert v) = HeapKnowledge.intValue v := by
  cases k <;> cases v <;> simp only [ElementKind.convert] <;>
    first
      | rfl
      | (rename_i b
         cases hb : SafeIntegers.safeIntOfBits b with
         | none => rfl
         | some i =>
           simp only [HeapKnowledge.intValue, hb]
           exact SafeIntegers.safeIntOfBits_complete
             (safeInt_int32Bits (SafeIntegers.safeIntOfBits_sound hb).1))

/-- **Every integer a term reads of a converted value is the one it reads of
the value**: a number has no field, and its kinds read its integer alone. -/
theorem ElementKind.readPath_convert (k : ElementKind) (h : Heap) (v : Tm) (p : List String)
    (kd : HeapKnowledge.Term.Kind) :
    (HeapKnowledge.readPath h (k.convert v) p).bind (HeapKnowledge.kindValue h kd) =
      (HeapKnowledge.readPath h v p).bind (HeapKnowledge.kindValue h kd) := by
  have hnum : ∀ b b', HeapKnowledge.intValue (.num b) = HeapKnowledge.intValue (.num b') →
      (HeapKnowledge.readPath h (.num b) p).bind (HeapKnowledge.kindValue h kd) =
        (HeapKnowledge.readPath h (.num b') p).bind (HeapKnowledge.kindValue h kd) := by
    intro b b' he
    cases p with
    | cons _ _ => rfl
    | nil =>
      cases kd <;> simp [HeapKnowledge.readPath, HeapKnowledge.kindValue, HeapKnowledge.lengthOf,
        HeapKnowledge.viewLengthOf, HeapKnowledge.strLengthOf, Footprints.storeOf, Footprints.fieldsOf, he]
  have hc := k.intValue_convert v
  cases v with
  | num b =>
    obtain ⟨b', hb'⟩ : ∃ b', k.convert (.num b) = .num b' := by
      cases k <;> simp only [ElementKind.convert] <;> first | exact ⟨_, rfl⟩ | (split <;> exact ⟨_, rfl⟩)
    rw [hb'] at hc ⊢
    exact hnum _ _ hc
  | _ => cases k <;> rfl

/-- A number in its canonical form, a natural below `2^53`, is its own
conversion. -/
theorem ElementKind.convert_bitsOfNat (k : ElementKind) {n : Nat} (hn : n < 2 ^ 53) :
    k.convert (.num (bitsOfNat n)) = .num (bitsOfNat n) := by
  have hs : SafeIntegers.safeIntOfBits (bitsOfNat n) = some (n : Int) :=
    SafeIntegers.safeIntOfBits_complete ⟨by simpa using hn, .inl ⟨by omega, by simp⟩⟩
  cases k <;> simp [ElementKind.convert, hs, IndexNumbers.int32Bits_nat]

/-- **An integer element converts `-0` to `+0`; a `Float64Array` element
keeps it**: the exact write's statement separates the element types at
`-0`, which every integer element type's precondition admits (`-0`
denotes `0`). -/
theorem ElementKind.convert_negZero :
    SafeIntegers.SafeInt 0x8000000000000000 0 ∧
      (∀ k : ElementKind, k ≠ .float64 → k.convert (.num 0x8000000000000000) = .num 0) ∧
      ElementKind.float64.convert (.num 0x8000000000000000) = .num 0x8000000000000000 ∧
      (Tm.num 0 : Tm) ≠ .num 0x8000000000000000 := by
  have hz : SafeIntegers.SafeInt 0x8000000000000000 0 := ⟨by decide, .inr ⟨by decide, by
    rw [show (0 : Int).natAbs = 0 from rfl, SafeIntegers.bitsOfNat_zero]; rfl⟩⟩
  have hs := SafeIntegers.safeIntOfBits_complete hz
  refine ⟨hz, fun k hk => ?_, rfl, by simp⟩
  cases k <;> simp_all [ElementKind.convert, int32Bits, bitsOfNat] <;> decide

/-- **What an element write states of the heaps alone**, of a call with
actuals `args`: its coarse change (`ElementWrite.changes`: no object or
number altered, every store's length kept), and, where exact, `ExactWrite`.
Both are consequences of the kinded view-element write from a well-formed
entry (`Kinds.ViewWriteOf.holds`), which the call's postcondition states
beside it (`CallEffects.Effect.viewPost`). -/
def ElementWrite.Holds (w : ElementWrite) (args : List Tm) (before after : Heap) : Prop :=
  w.changes.Holds before after ∧ (∀ k, w = .exact k → ExactWrite k args before after)

theorem ElementWrite.Holds.changes {w : ElementWrite} {args : List Tm} {before after : Heap}
    (h : w.Holds args before after) : w.changes.Holds before after := h.1

theorem ExactWrite.prefix_left {k : ElementKind} {args : List Tm} {before middle after : Heap}
    (hx : ExactWrite k args middle after) (hprefix : before.IsPrefix middle) : ExactWrite k args before after := by
  refine ⟨hx.1, fun s ls hs hls => ?_⟩
  apply hx.2 s ls hs
  obtain ⟨t, rfl⟩ := hprefix
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hls).1, hls]

theorem ElementWrite.Holds.prefix_left {w : ElementWrite} {args : List Tm} {before middle after : Heap}
    (hx : w.Holds args middle after) (hprefix : before.IsPrefix middle) : w.Holds args before after :=
  ⟨HeapKnowledge.Changes.Holds.prefix_left hx.1 hprefix, fun k he => (hx.2 k he).prefix_left hprefix⟩

/-- An element write of any actuals keeps what a write of stores does. -/
theorem ElementWrite.Holds.stores {w : ElementWrite} {args args' : List Tm} {before after : Heap}
    (h : w.Holds args before after) : ElementWrite.stores.Holds args' before after :=
  ⟨by cases w <;> exact h.1, fun _ he => by cases he⟩
end Verification.CallEffects

namespace Verification.Kinds
open Verification

/-! ## The view-element write -/

/-- **The view-element write**, from the entry world `W` and heap `h` to the
exit world `W'` and heap `h'`. The exit world extends the entry one
truncated to its budget; the exit heap meets the exit world in both parts,
so its domain is the exit world's, each location has its role's shape and
its contract's contents, the fresh ones included; every old location whose
role is no view store keeps its contents; and each cell an old view store
newly lists is fresh against `h`. The relation constrains every view store,
whichever view the call names. -/
structure ViewWrite {n n' : Nat} (W : WorldT n) (h : Heap) (W' : WorldT n') (h' : Heap) : Prop where
  le : n' ≤ n
  ext : WExt (trunc n' le W) W'
  ok : HeapOk n' W' h'
  keep : ∀ (l : Nat) (r : Role), roleAt W l = some r → (∀ N, r ≠ .store (.view N)) → h'[l]? = h[l]?
  grow : ∀ (l N : Nat) (ls ls' : List (Option Nat)), roleAt W l = some (.store (.view N)) →
    h[l]? = some (Tm.arr ls) → h'[l]? = some (Tm.arr ls') →
    ∀ c, some c ∈ ls' → some c ∈ ls ∨ h.length ≤ c

namespace ViewWrite
variable {n n' : Nat} {W : WorldT n} {h : Heap} {W' : WorldT n'} {h' : Heap}

/-- Every location keeps its role. -/
theorem roleAt (hw : ViewWrite W h W' h') {l : Nat} {r : Role} (hl : Verification.roleAt W l = some r) :
    Verification.roleAt W' l = some r := WExt_roleAt hw.ext (by simpa using hl)

/-- **An ordinary array's store is kept.** -/
theorem keeps_array (hw : ViewWrite W h W' h') {l : Nat} (hl : Verification.roleAt W l = some (.store .array)) :
    h'[l]? = h[l]? := hw.keep l _ hl (fun N hN => by cases hN)

/-- **An old view store holds a replacement store of its fixed length, whose
present entries are element cells of the exit world and locations of the
exit heap.** -/
theorem view_store (hw : ViewWrite W h W' h') {l N : Nat}
    (hl : Verification.roleAt W l = some (.store (.view N))) :
    ∃ ls', h'[l]? = some (Tm.arr ls') ∧ ls'.length = N ∧
      ∀ c, some c ∈ ls' → Verification.roleAt W' c = some .elem ∧ c < h'.length := by
  obtain ⟨u, hu, ⟨ls', rfl, hlen⟩, -⟩ := hw.ok.2 l _ (hw.roleAt hl)
  exact ⟨ls', hu, hlen, fun c hc => hw.ok.store_cells hu hc⟩

/-- **A fresh location has its role's shape.** -/
theorem fresh (hw : ViewWrite W h W' h') {l : Nat} {r : Role} (hl : Verification.roleAt W' l = some r) :
    ∃ u, h'[l]? = some u ∧ Shape W' r u := hw.ok.2 l r hl

/-- **The coarse change is a consequence**: from a well-formed entry heap,
every location holding an object or a number keeps its contents, and every
store keeps its length (`CallEffects.ElementWrite.changes`). -/
theorem changes (hw : ViewWrite W h W' h') (hok : HeapOk n W h) (w : CallEffects.ElementWrite) :
    w.changes.Holds h h' := by
  have role_of : ∀ {l : Nat} {v : Val}, h[l]? = some v → ∃ r, Verification.roleAt W l = some r ∧ Shape W r v := by
    intro l v hv
    have hlt : l < (entries W).length := by
      have h1 := (List.getElem?_eq_some_iff.mp hv).1
      have h2 : h.length = (entries W).length := by simpa using hok.1.1
      omega
    obtain ⟨r, hr⟩ := roleAt_some hlt
    obtain ⟨u, hu, hs⟩ := hok.2 l r hr
    rw [hv] at hu; cases hu
    exact ⟨r, hr, hs⟩
  refine ⟨fun l v hv halt => ?_, fun _ l ls hl => ?_, fun hg => by cases w <;> cases hg⟩
  · obtain ⟨r, hr, hc, -⟩ := role_of hv
    rw [hw.keep l r hr (fun N hN => ?_), hv]
    subst hN
    obtain ⟨ls, rfl, -⟩ := hc
    cases w <;> simp [CallEffects.ElementWrite.changes, HeapKnowledge.Changes.alters] at halt
  · obtain ⟨r, hr, hc, -⟩ := role_of hl
    cases r with
    | store f =>
      cases f with
      | array => exact ⟨ls, by rw [hw.keeps_array hr, hl], rfl⟩
      | view N =>
        obtain ⟨ls₀, he, hlen⟩ := hc
        cases he
        obtain ⟨ls', hl', hlen', -⟩ := hw.view_store hr
        exact ⟨ls', hl', by omega⟩
    | field | cell | elem => simp [Cat, isSourceVal] at hc
    | identity => simp [Cat] at hc

end ViewWrite

/-- **The view-element write of a call's actuals**: the relation, and for the
exact form the designated view's store changed at the index alone
(`CallEffects.ExactWrite`). Exactness constrains the designated view; every
other view store may change. -/
def ViewWriteOf (w : CallEffects.ElementWrite) (args : List Tm) {n n' : Nat} (W : WorldT n) (h : Heap)
    (W' : WorldT n') (h' : Heap) : Prop :=
  ViewWrite W h W' h' ∧ (∀ k, w = .exact k → CallEffects.ExactWrite k args h h')

/-- **What an element write states of the heaps follows from the
relation**: from a well-formed entry, the coarse change
(`ViewWrite.changes`), and for the exact form `ExactWrite`. -/
theorem ViewWriteOf.holds {w : CallEffects.ElementWrite} {args : List Tm} {n n' : Nat} {W : WorldT n}
    {h : Heap} {W' : WorldT n'} {h' : Heap} (hw : ViewWriteOf w args W h W' h') (hok : HeapOk n W h) :
    w.Holds args h h' :=
  ⟨hw.1.changes hok w, hw.2⟩

/-! ## The view write from a prefix -/

/-- **The view write from a prefix of the entry**: a view write from a
world and heap extending an entry world and heap is one from the entry. -/
theorem ViewWrite.prefix_left {n m n' : Nat} {W : WorldT n} {M : WorldT m} {h hm : Heap}
    {W' : WorldT n'} {h' : Heap} (hle : m ≤ n) (hx : WExt (trunc m hle W) M) (hok : HeapOk n W h)
    (hp : h.IsPrefix hm) (hw : ViewWrite M hm W' h') : ViewWrite W h W' h' := by
  have hlen : h.length = (entries W).length := by simpa using hok.1.1
  have hrole : ∀ {l r}, Verification.roleAt W l = some r → Verification.roleAt M l = some r := fun hr =>
    WExt_roleAt hx (by simpa using hr)
  have hget : ∀ {l r}, Verification.roleAt W l = some r → hm[l]? = h[l]? := by
    intro l r hr
    obtain ⟨t, rfl⟩ := hp
    exact List.getElem?_append_left (by have := roleAt_lt hr; omega)
  refine ⟨Nat.le_trans hw.le hle, ?_, hw.ok, fun l r hr hne => ?_, fun l N ls ls' hr hl hl' c hc => ?_⟩
  · have := WExt_trunc hw.le hx
    rw [trunc_trunc] at this
    exact WExt_trans this hw.ext
  · rw [hw.keep l r (hrole hr) hne, hget hr]
  · rcases hw.grow l N ls ls' (hrole hr) (by rw [hget hr]; exact hl) hl' c hc with h1 | h1
    · exact .inl h1
    · exact .inr (Nat.le_trans hp.length_le h1)

end Verification.Kinds
