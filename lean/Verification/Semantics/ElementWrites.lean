import Verification.Semantics.IndexFacts
import Verification.Semantics.Kinds
import Verification.Semantics.ViewConversion
/-!
# Element writes and the view-element write

A typed array's element write as a relation between two world-heap pairs
(the Tolerant frames note, kinded worlds; location-kinds draft, §6), and
what it states of the two heaps alone.

- **The write of an element** (`CallEffects.ExactWrite`, the note's
  View-Write): for every number written at a valid index of a typed array of
  format `t`, the index reads `t`'s total conversion of the number
  (`ViewFormat.conv`) and every other index of the typed array reads what it
  read; at a number that is no valid index no location changes. Where the
  value is an integer the format stores, the conversion keeps it
  (`ExactWrite.taken`, `ElementKind.convert`).
- **The view-element write** (`Kinds.ViewWrite`, `Kinds.ViewWriteOf`): the
  exit world extends the entry one, the exit heap meets it in both parts,
  every old location whose role in the entry world is no view store keeps
  its contents, and a view store's newly listed cells are fresh. On
  well-formed states its frame is the action of the effect
  `{all-views: grow}` (`Kinds.ViewWrite.frame_iff`). A call's postcondition
  states it from the call's entry world and heap
  (`CallEffects.Effect.viewPost`).
- **What it states of the heaps** (`CallEffects.ElementWrite.Holds`): the
  coarse change (`ElementWrite.changes`) and, where exact, `ExactWrite` and
  the facts the exact signature's precondition gives (`ExactPre`); all
  follow from the relation and the precondition from a well-formed entry
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
call's positions (`1` the typed array, `2` the index, `3` the value): the
index is a safe integer, at least `0` and below the typed array's length;
the value is a safe integer, and, for a bounded type, at least the range's
low end and at most its high end. An exact effect's precondition states each
(`EffectJson`). -/
def ElementKind.preFacts (k : ElementKind) : List HeapKnowledge.IndexFact :=
  .int 2 :: .linear (.le [(.value 2, -1)] 0) ::
    .linear (.le [(.value 2, 1), (.now .view 1 [], -1)] (-1)) :: .int 3 :: match k.range with
    | none => []
    | some (lo, hi) => [.linear (.le [(.value 3, -1)] (-lo)), .linear (.le [(.value 3, 1)] hi)]

/-- A typed array's element write (`%ByteSet%`, a view's `fill`,
`copyWithin` and `set`; SOURCE-CONTRACTS.md, "Stated library types"). A
typed array's elements are its view store's cells, the view store of fixed
format and length that its descriptor names, and a write replaces entries of
the view stores of the typed arrays over the written bytes by fresh cells
(`ElementWrite.Holds`). -/
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

/-- The format of an element type's typed array. -/
def ElementKind.format : ElementKind → ViewFormat
  | .uint8 => .uint8
  | .uint16 => .uint16
  | .int32 => .int32
  | .float64 => .float64

theorem ElementKind.range_format (k : ElementKind) : k.format.range = k.range := by cases k <;> rfl

/-- A typed array's length, as its descriptor states it. -/
def viewLength : Val → Option Nat
  | .viewAt _ _ _ _ N => some N
  | _ => none

theorem viewLength_of_viewLengthOf {v : Val} {n : Int} (h : HeapKnowledge.viewLengthOf v = some n) :
    viewLength v = some n.toNat := by
  unfold HeapKnowledge.viewLengthOf at h
  split at h
  · split at h
    · cases h; simp [viewLength]
    · cases h
  · cases h

/-- **The write of an element** (the note *Tolerant frames*, View-Write),
of the actuals `args`, a typed array of format `k` (`args[0]`), a number
(`args[1]`) and the number written (`args[2]`), from `before` to `after`.
Where the index denotes an integer `i` below the typed array's length (a
valid index; `-0` denotes `0`; every typed array's length is below `2^53`,
so a valid index is a safe integer), where its store (`elementsOf`) listed
the entries `ls`, it lists after the write a cell at `i` holding the
format's conversion of the number (`ViewFormat.conv`), and at every other
index a cell holding what that index's cell held. At a number that is no
valid index no location changes. -/
def ExactWrite (k : ElementKind) (args : List Tm) (before after : Heap) : Prop :=
  ∀ x ib N, args.getD 2 .undef = .num x → args.getD 1 .undef = .num ib →
    viewLength (args.getD 0 .undef) = some N →
    (∀ i : Nat, SafeIntegers.SafeInt ib i → i < N →
      ∀ s ls, HeapKnowledge.elementsOf (args.getD 0 .undef) = some s → before[s]?.bind storeEntries = some ls →
        ∃ ls', after[s]?.bind storeEntries = some ls' ∧
          (∃ l, ls'[i]? = some (some l) ∧ after[l]? = some (.num (k.format.conv x))) ∧
          ∀ j, j ≠ i → ∀ l u, ls[j]? = some (some l) → before[l]? = some u →
            ∃ l', ls'[j]? = some (some l') ∧ after[l']? = some u) ∧
    ((∀ i : Nat, SafeIntegers.SafeInt ib i → N ≤ i) → before.IsPrefix after)

/-- **The facts an exact write's precondition gives** (`ElementKind.preFacts`,
`ElementKind.exactPre_of_requires`): the value is one `k` takes, and the
index a safe integer below the typed array's length. -/
def ExactPre (k : ElementKind) (args : List Tm) : Prop :=
  k.Takes (args.getD 2 .undef) ∧ ∃ (b : UInt64) (i : Nat) (N : Int), args.getD 1 .undef = .num b ∧
    SafeIntegers.SafeInt b i ∧ HeapKnowledge.viewLengthOf (args.getD 0 .undef) = some N ∧ (i : Int) < N

/-- **On a value `k` takes, the conversion is `ElementKind.convert`**. -/
theorem ElementKind.convert_conv {k : ElementKind} {x : UInt64} (hk : k.Takes (.num x)) :
    k.convert (.num x) = .num (k.format.conv x) := by
  obtain ⟨b, i, hb, hs, hr⟩ := hk
  cases hb
  rw [ElementKind.convert_takes hs, ViewFormat.conv_safeInt hs (fun lo hi he => hr lo hi (by
    rw [← ElementKind.range_format]; exact he))]
  cases k <;> rfl

/-- **The exact write at a value `k` takes and a valid index**: the
designated store lists at the index a cell holding `k`'s conversion of the
value (`ElementKind.convert`, which keeps its integer), and at every other
index a cell holding what that index's cell held. -/
theorem ExactWrite.taken {k : ElementKind} {args : List Tm} {before after : Heap}
    (hx : ExactWrite k args before after) (hp : ExactPre k args) :
    ∀ s ls, HeapKnowledge.elementsOf (args.getD 0 .undef) = some s → before[s]?.bind storeEntries = some ls →
      ∃ ls' b, ∃ i : Nat, after[s]?.bind storeEntries = some ls' ∧ args.getD 1 .undef = .num b ∧
        SafeIntegers.SafeInt b (i : Int) ∧
        (∀ j, j ≠ i → ∀ l u, ls[j]? = some (some l) → before[l]? = some u →
          ∃ l', ls'[j]? = some (some l') ∧ after[l']? = some u) ∧
        ∃ l, ls'[i]? = some (some l) ∧ after[l]? = some (k.convert (args.getD 2 .undef)) := by
  intro s ls hs hls
  obtain ⟨hk, b, i, N, hb, hsi, hN, hlt⟩ := hp
  obtain ⟨x, hxv⟩ : ∃ x, args.getD 2 .undef = .num x := by
    obtain ⟨x, _, hxe, -⟩ := hk; exact ⟨x, hxe⟩
  have hN' := viewLength_of_viewLengthOf hN
  obtain ⟨ls', hls', ⟨l, hl, hlv⟩, hj⟩ :=
    (hx x b N.toNat hxv hb hN').1 i hsi (by omega) s ls hs hls
  rw [hxv] at hk ⊢
  exact ⟨ls', b, i, hls', hb, hsi, hj, l, hl, by rw [ElementKind.convert_conv hk]; exact hlv⟩

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
             (SafeIntegers.safeInt_int32Bits (SafeIntegers.safeIntOfBits_sound hb).1))

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
number altered, every store's length kept), and, where exact, `ExactWrite`
and the facts its precondition gives (`ExactPre`). They are consequences
of the kinded view-element write from a well-formed entry
(`Kinds.ViewWriteOf.holds`), which the call's postcondition states beside it
(`CallEffects.Effect.viewPost`), and of the precondition
(`ElementKind.exactPre_of_requires`). -/
def ElementWrite.Holds (w : ElementWrite) (args : List Tm) (before after : Heap) : Prop :=
  w.changes.Holds before after ∧ (∀ k, w = .exact k → ExactWrite k args before after ∧ ExactPre k args)

theorem ElementWrite.Holds.changes {w : ElementWrite} {args : List Tm} {before after : Heap}
    (h : w.Holds args before after) : w.changes.Holds before after := h.1

theorem ExactWrite.prefix_left {k : ElementKind} {args : List Tm} {before middle after : Heap}
    (hx : ExactWrite k args middle after) (hprefix : before.IsPrefix middle) : ExactWrite k args before after := by
  intro x ib N hxv hb hN
  obtain ⟨hv, hinv⟩ := hx x ib N hxv hb hN
  refine ⟨fun i hi hlt s ls hs hls => ?_, fun h => hprefix.trans (hinv h)⟩
  obtain ⟨t, rfl⟩ := hprefix
  obtain ⟨ls', hls', hw, hj⟩ := hv i hi hlt s ls hs (HeapKnowledge.storeEntries_extend t hls)
  exact ⟨ls', hls', hw, fun j hji l u hl hu =>
    hj j hji l u hl (List.getElem?_append_left (List.getElem?_eq_some_iff.mp hu).1 ▸ hu)⟩

theorem ElementWrite.Holds.prefix_left {w : ElementWrite} {args : List Tm} {before middle after : Heap}
    (hx : w.Holds args middle after) (hprefix : before.IsPrefix middle) : w.Holds args before after :=
  ⟨HeapKnowledge.Changes.Holds.prefix_left hx.1 hprefix, fun k he =>
    ⟨(hx.2 k he).1.prefix_left hprefix, (hx.2 k he).2⟩⟩

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
whichever typed array the call names. -/
structure ViewWrite {n n' : Nat} (W : WorldT n) (h : Heap) (W' : WorldT n') (h' : Heap) : Prop where
  le : n' ≤ n
  ext : WExt (trunc n' le W) W'
  ok : HeapOk n' W' h'
  keep : ∀ (l : Nat) (r : Role), roleAt W l = some r → (∀ f N, r ≠ .store (.view f N)) → h'[l]? = h[l]?
  grow : ∀ (l : Nat) (f : ViewFormat) (N : Nat) (cs cs' : List Nat), roleAt W l = some (.store (.view f N)) →
    h[l]? = some (Tm.viewStore f cs) → h'[l]? = some (Tm.viewStore f cs') →
    ∀ c ∈ cs', c ∈ cs ∨ h.length ≤ c

namespace ViewWrite
variable {n n' : Nat} {W : WorldT n} {h : Heap} {W' : WorldT n'} {h' : Heap}

/-- Every location keeps its role. -/
theorem roleAt (hw : ViewWrite W h W' h') {l : Nat} {r : Role} (hl : Verification.roleAt W l = some r) :
    Verification.roleAt W' l = some r := WExt_roleAt hw.ext (by simpa using hl)

/-- **An ordinary array's store is kept.** -/
theorem keeps_array (hw : ViewWrite W h W' h') {l : Nat} (hl : Verification.roleAt W l = some (.store .array)) :
    h'[l]? = h[l]? := hw.keep l _ hl (fun f N hN => by cases hN)

/-- **An old view store holds a replacement view store of its fixed format
and length, whose cells are element cells of the exit world and locations of
the exit heap.** -/
theorem view_store (hw : ViewWrite W h W' h') {l : Nat} {f : ViewFormat} {N : Nat}
    (hl : Verification.roleAt W l = some (.store (.view f N))) :
    ∃ cs', h'[l]? = some (Tm.viewStore f cs') ∧ cs'.length = N ∧
      ∀ c ∈ cs', Verification.roleAt W' c = some .elem ∧ c < h'.length := by
  obtain ⟨u, hu, ⟨cs', rfl, hlen⟩, -⟩ := hw.ok.2 l _ (hw.roleAt hl)
  exact ⟨cs', hu, hlen, fun c hc => hw.ok.view_cells hu hc⟩

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
    rw [hw.keep l r hr (fun f N hN => ?_), hv]
    subst hN
    obtain ⟨cs, rfl, -⟩ := hc
    cases w <;> simp [CallEffects.ElementWrite.changes, HeapKnowledge.Changes.alters] at halt
  · obtain ⟨r, hr, hc, -⟩ := role_of hl
    cases r with
    | store f =>
      cases f with
      | array => exact ⟨ls, by rw [hw.keeps_array hr, hl], rfl⟩
      | view fm N =>
        obtain ⟨cs, he, -⟩ := hc
        cases he
    | field | cell | elem => simp [Cat, isSourceVal] at hc
    | identity => simp [Cat] at hc

end ViewWrite

/-- **The view-element write of a call's actuals**: the relation, and for the
exact form the write of the designated typed array's element
(`CallEffects.ExactWrite`) and the facts its precondition gives
(`CallEffects.ExactPre`). Exactness constrains the designated typed array;
every other view store may change. -/
def ViewWriteOf (w : CallEffects.ElementWrite) (args : List Tm) {n n' : Nat} (W : WorldT n) (h : Heap)
    (W' : WorldT n') (h' : Heap) : Prop :=
  ViewWrite W h W' h' ∧ (∀ k, w = .exact k → CallEffects.ExactWrite k args h h' ∧ CallEffects.ExactPre k args)

/-- **What an element write states of the heaps follows from the
relation**: from a well-formed entry, the coarse change
(`ViewWrite.changes`), and for the exact form `ExactWrite`. -/
theorem ViewWriteOf.holds {w : CallEffects.ElementWrite} {args : List Tm} {n n' : Nat} {W : WorldT n}
    {h : Heap} {W' : WorldT n'} {h' : Heap} (hw : ViewWriteOf w args W h W' h') (hok : HeapOk n W h) :
    w.Holds args h h' :=
  ⟨hw.1.changes hok w, hw.2⟩

/-! ## The frame of the view write is the effect `{all-views: grow}` -/

/-- **The view write's frame is the action of the effect `{all-views:
grow}`** (the note *Tolerant frames*, View-Write's effect): from a
well-formed entry, a transition to a well-formed exit of an extending world
is a view write exactly when it meets that effect's footprint
(`Post [(.cls Selector.views, .grow)]`): a location holding no view store
keeps its contents, and a view store may be replaced by one of its format
and length every cell of which it listed or is fresh (`ViewStep`). The
environment is any: a class region reads no slot. -/
theorem ViewWrite.frame_iff {n n' : Nat} {W : WorldT n} {h : Heap} {W' : WorldT n'} {h' : Heap}
    (hok : HeapOk n W h) (ρ : Env) :
    ViewWrite W h W' h' ↔ (∃ hle : n' ≤ n, WExt (trunc n' hle W) W') ∧ HeapOk n' W' h' ∧
      Footprints.Post [(.cls Footprints.Selector.views, .grow)] ρ h h' := by
  have hlen : h.length = (entries W).length := by simpa using hok.1.1
  have role_of : ∀ {l : Nat} {v : Val}, h[l]? = some v → ∃ r, Verification.roleAt W l = some r ∧ Cat r v := by
    intro l v hv
    have hlt : l < (entries W).length := by
      have := (List.getElem?_eq_some_iff.mp hv).1; omega
    obtain ⟨r, hr⟩ := roleAt_some hlt
    obtain ⟨u, hu, hc, -⟩ := hok.2 l r hr
    rw [hv] at hu; cases hu
    exact ⟨r, hr, hc⟩
  constructor
  · intro hw
    refine ⟨⟨hw.le, hw.ext⟩, hw.ok, ?_, fun l v hv => ?_⟩
    · have h1 : h'.length = (entries W').length := by simpa using hw.ok.1.1
      have h2 := WExt_length hw.ext
      simp only [entries_trunc, List.length_map] at h2
      omega
    · obtain ⟨r, hr, hc⟩ := role_of hv
      cases r with
      | store sf =>
        cases sf with
        | array => exact ⟨v, by rw [hw.keeps_array hr, hv], .inl rfl⟩
        | view f N =>
          obtain ⟨cs, rfl, hcs⟩ := hc
          obtain ⟨cs', hcs', hlen', -⟩ := hw.view_store hr
          refine ⟨_, hcs', .inr ⟨_, List.mem_singleton.mpr rfl, ?_, ?_⟩⟩
          · simp [Footprints.Region.mem, hv, Footprints.Selector.selects, contentsCategory,
              Footprints.Selector.has]
          · exact .inr (.inr (.inr ⟨f, cs, cs', rfl, rfl, by omega, hw.grow l f N cs cs' hr hv hcs'⟩))
      | field | cell | elem | identity =>
        exact ⟨v, by rw [hw.keep l _ hr (fun f N hN => by cases hN), hv], .inl rfl⟩
  · rintro ⟨⟨hle, hx⟩, hok', hlen', hall⟩
    have step : ∀ {l : Nat} {v : Val}, h[l]? = some v → ∃ v', h'[l]? = some v' ∧
        (v' = v ∨ (contentsCategory v = .view ∧ Footprints.Change.grow.Holds h.length v v')) := by
      intro l v hv
      obtain ⟨v', hv', hal⟩ := hall l v hv
      refine ⟨v', hv', ?_⟩
      rcases hal with rfl | ⟨e, he, hm, hc⟩
      · exact .inl rfl
      · simp only [List.mem_singleton] at he
        subst he
        simp only [Footprints.Region.mem, hv, Footprints.Selector.selects] at hm
        refine .inr ⟨?_, hc⟩
        revert hm; cases contentsCategory v <;> simp [Footprints.Selector.has]
    refine ⟨hle, hx, hok', fun l r hr hne => ?_, fun l f N cs cs' hr hl hl' c hc => ?_⟩
    · have hlt : l < h.length := by have := roleAt_lt hr; omega
      obtain ⟨v, hv⟩ : ∃ v, h[l]? = some v := ⟨h[l], List.getElem?_eq_getElem hlt⟩
      obtain ⟨r', hr', hcat⟩ := role_of hv
      rw [hr] at hr'; cases hr'
      obtain ⟨v', hv', hor⟩ := step hv
      rcases hor with rfl | ⟨hcv, -⟩
      · rw [hv', hv]
      · rw [hcat.category] at hcv
        cases r with
        | store sf => cases sf with
          | array => cases hcv
          | view f N => exact absurd rfl (hne f N)
        | field | cell | elem | identity => cases hcv
    · obtain ⟨v', hv', hor⟩ := step hl
      rw [hl'] at hv'; cases hv'
      rcases hor with he | ⟨-, hg⟩
      · cases he; exact .inl hc
      · rcases hg with he | ⟨ls, ls', he, -⟩ | ⟨-, ha, -⟩ | ⟨f', ds, ds', he, he', -, hnew⟩
        · cases he; exact .inl hc
        · cases he
        · cases ha
        · cases he; cases he'; exact hnew c hc

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
  refine ⟨Nat.le_trans hw.le hle, ?_, hw.ok, fun l r hr hne => ?_, fun l f N cs cs' hr hl hl' c hc => ?_⟩
  · have := WExt_trunc hw.le hx
    rw [trunc_trunc] at this
    exact WExt_trans this hw.ext
  · rw [hw.keep l r (hrole hr) hne, hget hr]
  · rcases hw.grow l f N cs cs' (hrole hr) (by rw [hget hr]; exact hl) hl' c hc with h1 | h1
    · exact .inl h1
    · exact .inr (Nat.le_trans hp.length_le h1)

end Verification.Kinds
