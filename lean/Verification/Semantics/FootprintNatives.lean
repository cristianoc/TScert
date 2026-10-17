import Verification.Semantics.FootprintStability

/-! # Native footprints

Each native's footprint is a footprint of the step-1 vocabulary, never a rule
of its own. This module proves what the native's specification steps decide
about it, where the model has those steps: the array mutators. An array
native writes its store and the contents of element locations, and allocates
fresh ones: on the store's list of element locations it performs `Set` of an
index (a present index keeps its location, whose contents change; an absent
one gets a fresh location), `Delete` of an index, and a length change. The
mutators are those steps in the order their specification gives
(ECMA-262 `push`, `pop`, `shift`, `unshift`, `reverse`, and `sort`'s
writeback). The heap side, that a native changes nothing but its store and
element contents, is the audited part of each native's row; `array_native_post`
turns it, with the proved store relation, into the footprint's postcondition.

`map` relies on density between callbacks: `rely_chain` is the one framing
mechanism applied to a sequence of steps, and `denseCheck_stable` shows the
closed check of `map`'s bound to be an instance of the stability check. -/
namespace Verification.Footprints

/-! ## Stores and their steps -/

/-- Whether index `i` of a store is present. -/
def present (ls : List (Option Nat)) (i : Nat) : Bool :=
  match ls[i]? with
  | some (some _) => true
  | _ => false

/-- A store's element locations and the next location an allocation takes. -/
structure Arr where
  ls : List (Option Nat)
  next : Nat
  deriving DecidableEq, Repr

/-- `Set(O, k, v)`: a present index keeps its location, an absent one gets a
fresh location, holes filling any gap before it. -/
def Arr.set (a : Arr) (k : Nat) : Arr :=
  if present a.ls k then a else ⟨placeAt a.ls k a.next, a.next + 1⟩

/-- `DeletePropertyOrThrow(O, k)`. -/
def Arr.delete (a : Arr) (k : Nat) : Arr := ⟨a.ls.set k none, a.next⟩

/-- `Set(O, "length", n)`. -/
def Arr.setLength (a : Arr) (n : Nat) : Arr :=
  ⟨if n ≤ a.ls.length then a.ls.take n else a.ls ++ List.replicate (n - a.ls.length) none, a.next⟩

theorem present_lt {ls : List (Option Nat)} {i} (h : present ls i = true) : i < ls.length := by
  unfold present at h
  split at h
  · rename_i _ hi; exact (List.getElem?_eq_some_iff.mp hi).1
  · cases h

theorem dense_iff_present {n : Nat} {ls : List (Option Nat)} :
    DensePrefix n ls ↔ ∀ i, i < n → present ls i = true := by
  constructor
  · rintro ⟨hlen, hall⟩ i hi
    have hl : i < ls.length := by omega
    have hne := hall i hi
    rw [List.getElem?_eq_getElem hl] at hne
    unfold present
    rw [List.getElem?_eq_getElem hl]
    cases hc : ls[i] with
    | none => rw [hc] at hne; exact absurd rfl hne
    | some _ => rfl
  · intro h
    refine ⟨?_, fun i hi hn => ?_⟩
    · cases n with
      | zero => exact Nat.zero_le _
      | succ n => exact present_lt (h n (by omega))
    · have := h i hi
      simp [present, hn] at this

private theorem padded_get {ls : List (Option Nat)} {m i : Nat} :
    (ls ++ List.replicate m none)[i]? = some (some l) → ls[i]? = some (some l) := by
  intro h
  by_cases hi : i < ls.length
  · rwa [List.getElem?_append_left hi] at h
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate] at h
    split at h <;> simp at h

theorem present_placeAt_self (ls : List (Option Nat)) (k l : Nat) : present (placeAt ls k l) k = true := by
  unfold present placeAt
  rw [List.getElem?_set_self (by simp; omega)]

theorem present_placeAt_other {ls : List (Option Nat)} {k l i : Nat} (hi : i ≠ k) :
    present (placeAt ls k l) i = present ls i := by
  unfold present placeAt
  rw [List.getElem?_set_ne (Ne.symm hi)]
  by_cases hl : i < ls.length
  · rw [List.getElem?_append_left hl]
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate,
      List.getElem?_eq_none (by omega)]
    by_cases h : i - ls.length < k + 1 - ls.length <;> simp [h]

theorem present_set_self (a : Arr) (k : Nat) : present (a.set k).ls k = true := by
  unfold Arr.set
  split
  · assumption
  · exact present_placeAt_self _ _ _

theorem present_set_other (a : Arr) {k i : Nat} (hi : i ≠ k) : present (a.set k).ls i = present a.ls i := by
  unfold Arr.set
  split
  · rfl
  · exact present_placeAt_other hi

theorem present_delete_other (a : Arr) {k i : Nat} (hi : i ≠ k) :
    present (a.delete k).ls i = present a.ls i := by
  simp [Arr.delete, present, List.getElem?_set_ne (Ne.symm hi)]

theorem present_setLength {a : Arr} {n i : Nat} (hi : i < n) :
    present (a.setLength n).ls i = present a.ls i := by
  have : (a.setLength n).ls[i]? = a.ls[i]? ∨ ((a.setLength n).ls[i]? = some none ∧ a.ls[i]? = none) := by
    simp only [Arr.setLength]
    split
    · left; rw [List.getElem?_take]; simp [hi]
    · by_cases hl : i < a.ls.length
      · left; rw [List.getElem?_append_left hl]
      · right
        rw [List.getElem?_append_right (by omega), List.getElem?_replicate_of_lt (by omega),
          List.getElem?_eq_none (by omega)]
        exact ⟨rfl, rfl⟩
  rcases this with h | ⟨h1, h2⟩
  · simp [present, h]
  · simp [present, h1, h2]

/-- **Locations.** Every step keeps the store's element locations among the
original ones and fresh ones, at least `b`. -/
def Arr.Within (b : Nat) (orig : List (Option Nat)) (a : Arr) : Prop :=
  b ≤ a.next ∧ ∀ l, some l ∈ a.ls → some l ∈ orig ∨ b ≤ l

theorem Arr.Within.refl {b : Nat} {a : Arr} (h : b ≤ a.next) : a.Within b a.ls :=
  ⟨h, fun _ hl => .inl hl⟩

theorem Arr.Within.set {b orig} {a : Arr} (h : a.Within b orig) (k : Nat) : (a.set k).Within b orig := by
  unfold Arr.set
  split
  · exact h
  · refine ⟨Nat.le_succ_of_le h.1, fun l hl => ?_⟩
    rcases List.mem_or_eq_of_mem_set hl with hl | hl
    · rcases List.mem_append.mp hl with hl | hl
      · exact h.2 l hl
      · simp [List.mem_replicate] at hl
    · cases hl; exact .inr h.1

theorem Arr.Within.delete {b orig} {a : Arr} (h : a.Within b orig) (k : Nat) : (a.delete k).Within b orig := by
  refine ⟨h.1, fun l hl => ?_⟩
  rcases List.mem_or_eq_of_mem_set hl with hl | hl
  · exact h.2 l hl
  · cases hl

theorem Arr.Within.setLength {b orig} {a : Arr} (h : a.Within b orig) (n : Nat) :
    (a.setLength n).Within b orig := by
  refine ⟨h.1, fun l hl => ?_⟩
  simp only [Arr.setLength] at hl
  split at hl
  · exact h.2 l (List.mem_of_mem_take hl)
  · rcases List.mem_append.mp hl with hl | hl
    · exact h.2 l hl
    · simp [List.mem_replicate] at hl

/-- A store change within the original and fresh locations that keeps every
dense prefix is `grow`. -/
theorem grow_of_steps {b : Nat} {orig : List (Option Nat)} {a : Arr} (hw : a.Within b orig)
    (hd : ∀ n, DensePrefix n orig → DensePrefix n a.ls) : Change.grow.Holds b (.arr orig) (.arr a.ls) :=
  .inr ⟨orig, a.ls, rfl, rfl, hd, hw.2⟩

/-! ## The mutators -/

/-- `push(v)`: `Set(O, len, v)`, then the length. -/
def Arr.push (a : Arr) : Arr := a.set a.ls.length

/-- `pop()`: delete the last index and shorten. -/
def Arr.pop (a : Arr) : Arr :=
  if a.ls.length = 0 then a.setLength 0 else (a.delete (a.ls.length - 1)).setLength (a.ls.length - 1)

/-- `shift()`: each index from 1 moves down by `Set` where present and by
`Delete` where a hole, then the last index is deleted and the length shortened. -/
def Arr.shift (a : Arr) : Arr :=
  if a.ls.length = 0 then a.setLength 0 else
  let len := a.ls.length
  let moved := (List.range (len - 1)).foldl (fun s j =>
    if present s.ls (j + 1) then s.set j else s.delete j) a
  (moved.delete (len - 1)).setLength (len - 1)

/-- `unshift(v)`'s moves: from the last index down, index `j` moves up by
`Set` where present and by `Delete` where a hole. -/
def Arr.unshiftMoves : Nat → Arr → Arr
  | 0, a => a
  | j + 1, a => Arr.unshiftMoves j (if present a.ls j then a.set (j + 1) else a.delete (j + 1))

/-- `unshift(v)`: the moves, then `Set(O, 0, v)`. -/
def Arr.unshift (a : Arr) : Arr := (Arr.unshiftMoves a.ls.length a).set 0

/-- `reverse()`: each pair of a lower and an upper index, from the outside in:
both present, two `Set`s; only the upper, `Set` lower and `Delete` upper; only
the lower, `Delete` lower and `Set` upper. -/
def Arr.reverse (a : Arr) : Arr :=
  let len := a.ls.length
  (List.range (len / 2)).foldl (fun s lower =>
    let upper := len - 1 - lower
    match present s.ls lower, present s.ls upper with
    | true, true => (s.set lower).set upper
    | false, true => (s.set lower).delete upper
    | true, false => (s.delete lower).set upper
    | false, false => s) a

/-- `sort`'s writeback: the `itemCount` sorted values to indices below it,
then `Delete` of every index from it up to the length read at the start. -/
def Arr.writeback (itemCount len : Nat) (a : Arr) : Arr :=
  (List.range (len - itemCount)).foldl (fun s j => s.delete (itemCount + j))
    ((List.range itemCount).foldl (fun s j => s.set j) a)

/-- The number of present indices below `len`: the values `sort` snapshots. -/
def itemCount (ls : List (Option Nat)) (len : Nat) : Nat :=
  ((ls.take len).filter Option.isSome).length

/-! ## Locations of the mutators -/

private theorem foldl_within {b orig} {f : Arr → Nat → Arr} (hf : ∀ a k, a.Within b orig → (f a k).Within b orig) :
    ∀ (xs : List Nat) (a : Arr), a.Within b orig → (xs.foldl f a).Within b orig
  | [], _, h => h
  | x :: xs, a, h => foldl_within hf xs (f a x) (hf a x h)

theorem Arr.push_within {b} {a : Arr} (h : b ≤ a.next) : a.push.Within b a.ls := (Arr.Within.refl h).set _

theorem Arr.unshiftMoves_within {b orig} : ∀ (j : Nat) (a : Arr), a.Within b orig → (Arr.unshiftMoves j a).Within b orig
  | 0, _, h => h
  | j + 1, a, h => by
    unfold Arr.unshiftMoves
    apply Arr.unshiftMoves_within j
    split
    · exact h.set _
    · exact h.delete _

theorem Arr.unshift_within {b} {a : Arr} (h : b ≤ a.next) : a.unshift.Within b a.ls :=
  (Arr.unshiftMoves_within _ _ (Arr.Within.refl h)).set _

theorem Arr.writeback_within {b orig} (n len : Nat) {a : Arr} (h : a.Within b orig) :
    (a.writeback n len).Within b orig :=
  foldl_within (fun _ _ hs => hs.delete _) _ _ (foldl_within (fun _ _ hs => hs.set _) _ _ h)

/-! ## Density -/

/-- **`push` keeps every dense prefix.** -/
theorem Arr.push_dense {a : Arr} {n} (hd : DensePrefix n a.ls) : DensePrefix n a.push.ls := by
  rw [dense_iff_present] at hd ⊢
  intro i hi
  have hlt := present_lt (hd i hi)
  rw [Arr.push, present_set_other _ (by omega)]
  exact hd i hi

/-- Moves from index `j` down change no index above `j`. -/
theorem Arr.unshiftMoves_above : ∀ (j : Nat) (a : Arr) (i : Nat), j < i →
    present (Arr.unshiftMoves j a).ls i = present a.ls i
  | 0, _, _, _ => rfl
  | j + 1, a, i, hi => by
    unfold Arr.unshiftMoves
    rw [Arr.unshiftMoves_above j _ i (by omega)]
    split
    · exact present_set_other _ (by omega)
    · exact present_delete_other _ (by omega)

/-- Moves from index `j` down: each index below `j` present before moves up
one, and is present there after. -/
theorem Arr.unshiftMoves_up : ∀ (j : Nat) (a : Arr) (i : Nat), i < j → present a.ls i = true →
    present (Arr.unshiftMoves j a).ls (i + 1) = true
  | 0, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | j + 1, a, i, hi, hp => by
    unfold Arr.unshiftMoves
    by_cases hij : i = j
    · subst hij
      rw [if_pos hp, Arr.unshiftMoves_above i _ (i + 1) (by omega)]
      exact present_set_self _ _
    · apply Arr.unshiftMoves_up j _ i (by omega)
      split
      · rw [present_set_other _ (by omega)]; exact hp
      · rw [present_delete_other _ (by omega)]; exact hp

/-- **`unshift` keeps every dense prefix**: the moves only delete above a
hole, beyond every dense prefix, and `Set(O, 0, v)` fills index 0. -/
theorem Arr.unshift_dense {a : Arr} {n} (hd : DensePrefix n a.ls) : DensePrefix n a.unshift.ls := by
  rw [dense_iff_present] at hd ⊢
  intro i hi
  unfold Arr.unshift
  cases i with
  | zero => exact present_set_self _ _
  | succ i =>
    rw [present_set_other _ (by omega)]
    have hp := hd i (by omega)
    exact Arr.unshiftMoves_up _ _ i (present_lt hp) hp

private theorem foldl_set_present : ∀ (xs : List Nat) (a : Arr) (i : Nat),
    (i ∈ xs ∨ present a.ls i = true) → present (xs.foldl (fun s j => s.set j) a).ls i = true
  | [], _, _, h => by simpa using h
  | x :: xs, a, i, h => by
    apply foldl_set_present xs
    by_cases hx : i = x
    · subst hx; exact .inr (present_set_self _ _)
    · rcases h with h | h
      · rcases List.mem_cons.mp h with h | h
        · exact absurd h hx
        · exact .inl h
      · exact .inr (by rw [present_set_other _ hx]; exact h)

private theorem foldl_delete_present (c : Nat) : ∀ (xs : List Nat) (a : Arr) (i : Nat), i < c →
    present a.ls i = true → present (xs.foldl (fun s j => s.delete (c + j)) a).ls i = true
  | [], _, _, _, h => h
  | x :: xs, a, i, hi, h => foldl_delete_present c xs _ i hi
      (by rw [present_delete_other _ (by omega)]; exact h)

/-- **`sort`'s writeback leaves every index below `itemCount` present**,
whatever the store was before it. -/
theorem Arr.writeback_dense (c len : Nat) (a : Arr) : DensePrefix c (a.writeback c len).ls := by
  rw [dense_iff_present]
  intro i hi
  exact foldl_delete_present c _ _ i hi (foldl_set_present _ _ i (.inl (List.mem_range.mpr hi)))

theorem itemCount_ge {ls : List (Option Nat)} {n len : Nat} (hd : DensePrefix n ls) (hn : n ≤ len) :
    n ≤ itemCount ls len := by
  rw [dense_iff_present] at hd
  unfold itemCount
  induction ls generalizing n len with
  | nil =>
    cases n with
    | zero => exact Nat.zero_le _
    | succ n => exact absurd (hd 0 (by omega)) (by simp [present])
  | cons o ls ih =>
    cases n with
    | zero => exact Nat.zero_le _
    | succ n =>
      cases len with
      | zero => omega
      | succ len =>
        have h0 := hd 0 (by omega)
        cases o with
        | none => simp [present] at h0
        | some l =>
          simp only [List.take_succ_cons, List.filter_cons, Option.isSome_some, if_true,
            List.length_cons]
          exact Nat.succ_le_succ (ih (fun i hi => by simpa [present] using hd (i + 1) (by omega)) (by omega))

/-- **`sort` keeps every dense prefix of its receiver at entry**, judged over
the whole call: the snapshot counts at least the prefix, and the writeback
fills every index below the count, whatever the comparator did meanwhile. -/
theorem sort_dense {ls : List (Option Nat)} {n : Nat} (hd : DensePrefix n ls) (mid : Arr) :
    DensePrefix n (mid.writeback (itemCount ls ls.length) ls.length).ls := by
  have hc := itemCount_ge hd hd.1
  have hw := Arr.writeback_dense (itemCount ls ls.length) ls.length mid
  rw [dense_iff_present] at hw ⊢
  exact fun i hi => hw i (by omega)

/-- `sort` grows its store over the whole call when the comparator's own
store changes keep the store's locations among the entry's and fresh ones. -/
theorem sort_grow {b} {ls : List (Option Nat)} {mid : Arr} (hmid : mid.Within b ls) :
    Change.grow.Holds b (.arr ls) (.arr (mid.writeback (itemCount ls ls.length) ls.length).ls) :=
  grow_of_steps (Arr.writeback_within _ _ hmid) fun _ hd => sort_dense hd mid

theorem Arr.push_grow {b} {a : Arr} (h : b ≤ a.next) : Change.grow.Holds b (.arr a.ls) (.arr a.push.ls) :=
  grow_of_steps (Arr.push_within h) fun _ => Arr.push_dense

theorem Arr.unshift_grow {b} {a : Arr} (h : b ≤ a.next) : Change.grow.Holds b (.arr a.ls) (.arr a.unshift.ls) :=
  grow_of_steps (Arr.unshift_within h) fun _ => Arr.unshift_dense

/-- A longer length keeps every dense prefix; a shorter one need not. -/
theorem Arr.setLength_grow {b} {a : Arr} {m : Nat} (h : b ≤ a.next) (hm : a.ls.length ≤ m) :
    Change.grow.Holds b (.arr a.ls) (.arr (a.setLength m).ls) := by
  refine grow_of_steps ((Arr.Within.refl h).setLength m) fun n hd => ?_
  rw [dense_iff_present] at hd ⊢
  intro i hi
  have := present_lt (hd i hi)
  rw [present_setLength (by omega)]
  exact hd i hi

/-! ## From the store to the footprint -/

/-- **The footprint of an array native.** A native that changes its
receiver's store by `grow`, any other old location only where it holds no
store (an element's contents), and allocates the rest, meets the footprint
`store(x): grow, class(value): any`. The heap-side premise is the audited
part of the native's row. -/
theorem array_native_post {ρ x s h h' ls ls'} (hs : (fieldsOf (ρ x)).lookup arrayStoreKey = some s)
    (hv : h[s]? = some (.arr ls)) (hv' : h'[s]? = some (.arr ls')) (hlen : h.length ≤ h'.length)
    (hg : Change.grow.Holds h.length (.arr ls) (.arr ls'))
    (hrest : ∀ l v, h[l]? = some v → l ≠ s → h'[l]? = some v ∨
      ((Region.cls .value).mem ρ h l = true ∧ ∃ v', h'[l]? = some v')) :
    Post [(.field x arrayStoreKey, .grow), (.cls .value, .any)] ρ h h' := by
  refine ⟨hlen, fun l v hl => ?_⟩
  by_cases hls : l = s
  · subst hls
    rw [hv] at hl; cases hl
    exact ⟨_, hv', .inr ⟨(.field x arrayStoreKey, .grow), List.mem_cons_self .., by simp [Region.mem, hs], hg⟩⟩
  · rcases hrest l v hl hls with h | ⟨hc, v', hv''⟩
    · exact ⟨v, h, .inl rfl⟩
    · exact ⟨v', hv'', .inr ⟨(.cls .value, .any), by simp, hc, trivial⟩⟩

/-- The same for a native that changes its store arbitrarily: the removing
mutators. -/
theorem array_native_post_any {ρ x s h h'} (hs : (fieldsOf (ρ x)).lookup arrayStoreKey = some s)
    (hlen : h.length ≤ h'.length) (hs' : ∃ v', h'[s]? = some v')
    (hrest : ∀ l v, h[l]? = some v → l ≠ s → h'[l]? = some v ∨
      ((Region.cls .value).mem ρ h l = true ∧ ∃ v', h'[l]? = some v')) :
    Post [(.field x arrayStoreKey, .any), (.cls .value, .any)] ρ h h' := by
  refine ⟨hlen, fun l v hl => ?_⟩
  by_cases hls : l = s
  · subst hls
    obtain ⟨v', hv'⟩ := hs'
    exact ⟨v', hv', .inr ⟨(.field x arrayStoreKey, .any), List.mem_cons_self .., by simp [Region.mem, hs], trivial⟩⟩
  · rcases hrest l v hl hls with h | ⟨hc, v', hv''⟩
    · exact ⟨v, h, .inl rfl⟩
    · exact ⟨v', hv'', .inr ⟨(.cls .value, .any), by simp, hc, trivial⟩⟩

/-! ## Relies -/

/-- The separation knowledge a density fact supplies about its own store. -/
def denseK (x : Nat) : SepKnowledge := ⟨denseClass x, ⟨fun _ => none, fun _ => none⟩, fun _ => [], []⟩

theorem denseK_holds {x n ρ h} (hd : Dense x n ρ h) : (denseK x).Holds id ρ h :=
  ⟨dense_classOk hd, ⟨fun _ _ h => by simp [denseK] at h, fun _ _ h => by simp [denseK] at h⟩,
    fun _ _ h => h, fun _ h => by simp [denseK] at h⟩

/-- **The closed check of `map`'s bound is the stability check**, with the
knowledge density gives about its own store. -/
theorem denseCheck_stable {x n : Nat} {Φ : Footprint} (hc : stableDenseClosed Φ = true) :
    stable (denseK x) (FactKind.dense x n).support Φ = true := by
  simp only [stable, FactKind.support, List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true]
  intro e he
  have := List.all_eq_true.mp hc e he
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with hcls | hle
  · rcases e with ⟨r, δ⟩
    simp only at hcls
    subst hcls
    simp [SepKnowledge.apart, SepKnowledge.apart₁, denseK, denseClass]
  · simp [hle]

/-- **A rely holds across a sequence of steps** each of whose footprints the
stability check accepts for the fact, with knowledge holding where the step
starts: the native's own steps and its callbacks alike. -/
theorem rely_chain {F : FactKind} {ρ : Env} (H : Nat → Heap) (Φ : Nat → Footprint)
    (K : Nat → SepKnowledge) (μ : Nat → Nat → Nat) (m : Nat)
    (hstep : ∀ i, i < m → Post (Φ i) ρ (H i) (H (i + 1)) ∧ stable (K i) F.support (Φ i) = true ∧
      (F.Holds ρ (H i) → (K i).Holds (μ i) ρ (H i)))
    (h0 : F.Holds ρ (H 0)) : ∀ i, i ≤ m → F.Holds ρ (H i) := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ i ih =>
    intro hi
    obtain ⟨hp, hs, hk⟩ := hstep i (by omega)
    have hF := ih (by omega)
    exact FactKind.support_sound hF (stable_sound hs (hk hF) hp)

/-- **`map`'s rely.** If the receiver is dense below its length at entry, and
every step until the last presence test (callbacks and `map`'s own steps)
has a footprint the closed check of `bound(dense)` accepts, the receiver is
dense below that length at every test. -/
theorem map_rely {x n : Nat} {ρ : Env} (H : Nat → Heap) (Φ : Nat → Footprint) (m : Nat)
    (hstep : ∀ i, i < m → Post (Φ i) ρ (H i) (H (i + 1)) ∧ stableDenseClosed (Φ i) = true)
    (h0 : Dense x n ρ (H 0)) : ∀ i, i ≤ m → Dense x n ρ (H i) :=
  rely_chain (F := .dense x n) H Φ (fun _ => denseK x) (fun _ => id) m
    (fun i hi => ⟨(hstep i hi).1, denseCheck_stable (hstep i hi).2, denseK_holds⟩) h0

end Verification.Footprints
