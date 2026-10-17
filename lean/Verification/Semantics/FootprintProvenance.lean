import Verification.Semantics.Footprints

/-! # Provenance and classes of contents

**Marks** are ghost heap lengths at allocation points, with mark 0 the
invocation's entry heap. A slot's **stamps** bound its locations against
marks: `after x = m` says every own location of `x` is at least mark `m`;
`before y = m` says every **typed** field location of `y` (one its type gives
a world contract) is below mark `m`. Two slots are apart when `after` of one
is at least `before` of the other, and only in the regions those stamps
cover: the own locations of the first, the typed fields of the second. An
array's listed element locations are not own locations of the array, and a
fresh store may list old element locations.

An edge renames marks by a map from target marks to source marks. A target
valuation is the source's composed with that map. The map must fix mark 0
and be monotone, and each target stamp must be implied by a source stamp in
its direction: `after` may only weaken toward an earlier source mark,
`before` only toward a later one.

The **classes** of contents follow from world contracts, at a positive step
index, and an element location's class from its store's contract one level
deeper. Nothing uses this module yet. -/
namespace Verification.Footprints

/-! ## Marks and stamps -/

/-- A mark valuation: monotone, mark 0 the entry heap's length, every mark at
most the current heap's length. -/
structure MarksOk (μ : Nat → Nat) (b : Nat) (h : Heap) : Prop where
  mono : ∀ i j, i ≤ j → μ i ≤ μ j
  entry : μ 0 = b
  below : ∀ i, μ i ≤ h.length

structure Stamps where
  after : Nat → Option Nat
  before : Nat → Option Nat

/-- `typed y` lists the keys of `y`'s typed fields. -/
def StampsHold (st : Stamps) (typed : Nat → List PropKey) (μ : Nat → Nat) (ρ : Env) : Prop :=
  (∀ x m, st.after x = some m → ∀ l ∈ (fieldsOf (ρ x)).map Prod.snd, μ m ≤ l) ∧
  (∀ y m, st.before y = some m → ∀ k ∈ typed y, ∀ l, (fieldsOf (ρ y)).lookup k = some l → l < μ m)

/-- **Provenance separation**, for the regions the stamps cover. -/
theorem stamps_separate {st typed μ ρ h x y m m' r l k l'} (hs : StampsHold st typed μ ρ)
    (hμ : ∀ i j, i ≤ j → μ i ≤ μ j) (ha : st.after x = some m) (hb : st.before y = some m')
    (hm : m' ≤ m) (hr : (∃ k, r = Region.field x k) ∨ r = .own x) (hrm : r.mem ρ h l = true)
    (hk : k ∈ typed y) (hl' : (fieldsOf (ρ y)).lookup k = some l') : l ≠ l' := by
  have hown : (Region.own x).mem ρ h l = true := by
    rcases hr with ⟨k, rfl⟩ | rfl
    · exact field_mem_own hrm
    · exact hrm
  have h₁ := hs.1 x m ha l (by simpa [Region.mem] using hown)
  have h₂ := hs.2 y m' hb k hk l' hl'
  have h₃ := hμ m' m hm
  omega

/-! ## Edges: renaming marks -/

def sortedB : List Nat → Bool
  | a :: b :: t => decide (a ≤ b) && sortedB (b :: t)
  | _ => true

/-- A target mark's source mark; marks past the list keep the last one. -/
def markAt : List Nat → Nat → Nat
  | [], _ => 0
  | [a], _ => a
  | a :: _ :: _, 0 => a
  | _ :: b :: t, i + 1 => markAt (b :: t) i

theorem head_le_markAt : ∀ (a : Nat) (t : List Nat) (i : Nat), sortedB (a :: t) = true →
    a ≤ markAt (a :: t) i
  | a, [], _, _ => by simp [markAt]
  | a, b :: t, 0, _ => by simp [markAt]
  | a, b :: t, i + 1, hs => by
    simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at hs
    simp only [markAt]
    exact Nat.le_trans hs.1 (head_le_markAt b t i hs.2)

theorem markAt_mono : ∀ (σ : List Nat) (i j : Nat), sortedB σ = true → i ≤ j → markAt σ i ≤ markAt σ j
  | [], _, _, _, _ => by simp [markAt]
  | [a], _, _, _, _ => by simp [markAt]
  | a :: b :: t, 0, j, hs, _ => by
    cases j with
    | zero => exact Nat.le_refl _
    | succ j =>
      simp only [markAt]
      simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at hs
      exact Nat.le_trans hs.1 (head_le_markAt b t j hs.2)
  | a :: b :: t, i + 1, j, hs, hij => by
    cases j with
    | zero => omega
    | succ j =>
      simp only [markAt]
      simp only [sortedB, Bool.and_eq_true] at hs
      exact markAt_mono (b :: t) i j hs.2 (by omega)

theorem markAt_zero {σ : List Nat} (h : σ.head?.all (· == 0) = true) : markAt σ 0 = 0 := by
  match σ, h with
  | [], _ => rfl
  | [a], h => simpa [markAt] using h
  | a :: b :: t, h => simpa [markAt] using h

/-- An edge: target marks to source marks, target slots to source slots. -/
structure StampEdge where
  marks : List Nat
  slot : Nat → Nat

/-- The edge check, over the target slots that carry stamps. -/
def stampEdgeOk (e : StampEdge) (st st' : Stamps) (typed typed' : Nat → List PropKey)
    (slots : List Nat) : Bool :=
  sortedB e.marks && e.marks.head?.all (· == 0) && slots.all fun j =>
    (match st'.after j with
     | none => true
     | some m' => match st.after (e.slot j) with
       | some m => decide (markAt e.marks m' ≤ m)
       | none => false) &&
    (match st'.before j with
     | none => true
     | some m' => match st.before (e.slot j) with
       | some m => decide (m ≤ markAt e.marks m') && (typed' j).all (typed (e.slot j)).contains
       | none => false)

theorem MarksOk.rename {μ b h} {σ : List Nat} (hm : MarksOk μ b h) (hs : sortedB σ = true)
    (h0 : σ.head?.all (· == 0) = true) : MarksOk (fun i => μ (markAt σ i)) b h :=
  ⟨fun i j hij => hm.mono _ _ (markAt_mono σ i j hs hij),
   by simp only [markAt_zero h0]; exact hm.entry, fun i => hm.below _⟩

theorem stamps_transport {e st st' typed typed' slots μ ρ}
    (hc : stampEdgeOk e st st' typed typed' slots = true)
    (hdom : ∀ j, (st'.after j).isSome ∨ (st'.before j).isSome → j ∈ slots)
    (hs : StampsHold st typed μ ρ) (hμ : ∀ i j, i ≤ j → μ i ≤ μ j) :
    StampsHold st' typed' (fun i => μ (markAt e.marks i)) (fun j => ρ (e.slot j)) := by
  simp only [stampEdgeOk, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨_, _⟩, hall⟩ := hc
  refine ⟨fun x m' ha l hl => ?_, fun y m' hb k hk l hl => ?_⟩
  · have hj := (hall x (hdom x (.inl (by simp [ha])))).1
    simp only [ha] at hj
    cases hsrc : st.after (e.slot x) with
    | none => simp [hsrc] at hj
    | some m =>
      simp only [hsrc, decide_eq_true_eq] at hj
      exact Nat.le_trans (hμ _ _ hj) (hs.1 _ m hsrc l hl)
  · have hj := (hall y (hdom y (.inr (by simp [hb])))).2
    simp only [hb] at hj
    cases hsrc : st.before (e.slot y) with
    | none => simp [hsrc] at hj
    | some m =>
      simp only [hsrc, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hj
      exact Nat.lt_of_lt_of_le (hs.2 _ m hsrc k (by simpa using hj.2 k hk) l hl) (hμ _ _ hj.1)

/-! ## Establishing stamps -/

theorem slots_ge : ∀ (b : Nat) (ns : List PropKey), ∀ l ∈ (slots b ns).map Prod.snd, b ≤ l
  | _, [] => by simp [slots]
  | b, f :: fs => by
    intro l hl
    simp only [slots, List.map_cons, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ b) (slots_ge (b + 1) fs l hl)

/-- An allocated object's own locations are at least the heap's length before
the allocation. -/
theorem alloc_after {h c ns vs h' r} (st : Step h (.makeAt c ns vs) h' r) (hv : ∀ v ∈ vs, isVal v = true) :
    ∀ l ∈ (fieldsOf r).map Prod.snd, h.length ≤ l := by
  cases st with
  | makeArg _ _ s =>
    rename_i i a _ hi _
    exact absurd s (value_no_step (hv a (List.mem_of_getElem? hi)))
  | makeFields => exact slots_ge h.length ns

/-- A location with a world contract lies below the heap's length. -/
theorem typed_below {n W h l c} (hh : HeapOk n W h) (hc : lookup W l = some c) : l < h.length := by
  rw [hh.1]
  exact (List.getElem?_eq_some_iff.mp hc).1

/-- At a new mark equal to the heap's length, a slot whose typed fields have
world contracts gets a `before` stamp. -/
theorem before_of_typed {n W h} {μ : Nat → Nat} {m : Nat} {ρ : Env} {y : Nat} {typed : Nat → List PropKey} (hh : HeapOk n W h)
    (hm : μ m = h.length)
    (ht : ∀ k ∈ typed y, ∀ l, (fieldsOf (ρ y)).lookup k = some l → ∃ c, lookup W l = some c) :
    ∀ k ∈ typed y, ∀ l, (fieldsOf (ρ y)).lookup k = some l → l < μ m := by
  intro k hk l hl
  obtain ⟨c, hc⟩ := ht k hk l hl
  rw [hm]; exact typed_below hh hc

/-- A new last mark at the current heap's length keeps the valuation sound. -/
theorem MarksOk.push {μ b h M} (hm : MarksOk μ b h) (hM : 0 < M) {h' : Heap} (hh : h.length ≤ h'.length) :
    MarksOk (fun i => if i < M then μ i else h.length) b h' := by
  refine ⟨fun i j hij => ?_, by simp [hM, hm.entry], fun i => ?_⟩
  · by_cases hi : i < M <;> by_cases hj : j < M <;> simp [hi, hj]
    · exact hm.mono i j hij
    · exact hm.below i
    · omega
  · by_cases hi : i < M <;> simp [hi]
    · exact Nat.le_trans (hm.below i) hh
    · exact hh

/-! ## Classes of contents -/

theorem isArr_of_source {v : Val} (h : isSourceVal v = true) : isArr v = false := by
  cases v <;> simp_all [isSourceVal, isArr]

/-- A location whose contract admits only source values holds no store. -/
theorem contract_class {n W h l c v} (hh : HeapOk (n+1) W h) (hc : lookup W l = some c)
    (hsrc : ∀ U u, c 0 (Nat.zero_lt_succ n) U u → isSourceVal u = true) (hv : h[l]? = some v) :
    isArr v = false := by
  obtain ⟨u, hu, hcu⟩ := hh.2 l c hc
  rw [hv] at hu; cases hu
  exact isArr_of_source (hsrc _ _ (hcu 0 (Nat.zero_lt_succ n)))

/-- A location whose contract admits only stores holds one. -/
theorem contract_store {n W h l c v} (hh : HeapOk (n+1) W h) (hc : lookup W l = some c)
    (hst : ∀ U u, c 0 (Nat.zero_lt_succ n) U u → isArr u = true) (hv : h[l]? = some v) :
    isArr v = true := by
  obtain ⟨u, hu, hcu⟩ := hh.2 l c hc
  rw [hv] at hu; cases hu
  exact hst _ _ (hcu 0 (Nat.zero_lt_succ n))

/-- **Entry-valid class.** A contract the current world states at a location
the entry heap has is the entry world's, so the entry heap's contents meet
it: a source-valued contract gives class `value` at the entry heap. -/
theorem contract_class_entry {N n W₀ h₀ l c} {W : WorldT (n+1)} (hn : n + 1 ≤ N + 1)
    (hh₀ : HeapOk (N+1) W₀ h₀) (hx : WExt (trunc (n+1) hn W₀) W) (hc : lookup W l = some c)
    (hl : l < h₀.length) (hsrc : ∀ U u, c 0 (Nat.zero_lt_succ n) U u → isSourceVal u = true) :
    (Region.cls .value).mem ρ h₀ l = true := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, lookup W₀ l = some c₀ := by
    have : l < (toList W₀).length := by rw [← hh₀.1]; exact hl
    exact ⟨_, List.getElem?_eq_getElem this⟩
  have ht := lookup_trunc hn W₀ l c₀ hc₀
  have hW := WExt_lookup hx ht
  rw [hc] at hW; cases hW
  have hv : h₀[l]? = some h₀[l] := List.getElem?_eq_getElem hl
  have := contract_class hh₀ hc₀ (fun U u hu => hsrc U u hu) hv
  simp [Region.mem, hv, Cls.has, this]

/-! ## Density -/

/-- `x`'s store holds an array whose first `n` indices are present. -/
def Dense (x n : Nat) (ρ : Env) (h : Heap) : Prop :=
  ∃ s ls, (fieldsOf (ρ x)).lookup arrayStoreKey = some s ∧ h[s]? = some (.arr ls) ∧ DensePrefix n ls

theorem dense_class {x n ρ h l} (hd : Dense x n ρ h)
    (hm : (Region.field x arrayStoreKey).mem ρ h l = true) : (Region.cls .store).mem ρ h l = true := by
  obtain ⟨s, ls, hs, hv, -⟩ := hd
  simp only [Region.mem, beq_iff_eq] at hm
  rw [hs] at hm; cases hm
  simp [Region.mem, hv, Cls.has, isArr]

/-- The support lemma of `Dense`: it survives a footprint whose entries that
cover its store change it at most by `grow`. -/
theorem dense_stable {x n ρ h h' Φ} (hd : Dense x n ρ h) (hp : Post Φ ρ h h')
    (hΦ : ∀ e ∈ Φ, ∀ l, (Region.field x arrayStoreKey).mem ρ h l = true → e.1.mem ρ h l = true →
      e.2.le .grow = true) : Dense x n ρ h' := by
  obtain ⟨s, ls, hs, hv, hn⟩ := hd
  obtain ⟨v', hv', ha⟩ := hp.2 s _ hv
  have hsm : (Region.field x arrayStoreKey).mem ρ h s = true := by simp [Region.mem, hs]
  refine ⟨s, ?_⟩
  rcases ha with rfl | ⟨e, he, hem, hh⟩
  · exact ⟨ls, hs, hv', hn⟩
  · rcases (hh.mono (hΦ e he s hsm hem) : Change.grow.Holds _ _ _) with rfl | ⟨ls₁, ls', h₁, rfl, hd, -⟩
    · exact ⟨ls, hs, hv', hn⟩
    · cases h₁; exact ⟨ls', hs, hv', hd n hn⟩

/-- The stability check of `Dense` under a closed footprint with no
knowledge: `class(value)` entries are apart from the store by class, every
other entry must change at most by `grow`. -/
def stableDenseClosed (Φ : Footprint) : Bool :=
  Φ.all fun e => e.1 == .cls .value || e.2.le .grow

theorem stableDenseClosed_sound {x n ρ h h' Φ} (hc : stableDenseClosed Φ = true)
    (hd : Dense x n ρ h) (hp : Post Φ ρ h h') : Dense x n ρ h' := by
  refine dense_stable hd hp fun e he l hsm hem => ?_
  have := List.all_eq_true.mp hc e he
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with hcls | hle
  · have hst := dense_class hd hsm
    rw [hcls] at hem
    obtain ⟨s, ls, hs, hv, -⟩ := hd
    simp only [Region.mem] at hst hem
    split at hst <;> simp_all [Cls.has]
  · exact hle

/-! ## Elements -/

theorem source_of_elements {T : TupleF} {k : Nat} {W : WorldT k} {ls : List (Option Nat)} {l : Nat}
    (hT : listT T k W (.arr ls)) (hl : some l ∈ ls) :
    ∃ (A : Fam) (c : Ctr k), (A ∈ T.required ∨ A ∈ T.optional ∨ T.rest = some A) ∧
      lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), SlotContract T.readonly (c j hj W' u) (A j W' u) := by
  obtain ⟨ls', heq, -, -, -, hreq, hopt, hrest⟩ := hT
  cases heq
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  by_cases hr : i < T.required.length
  · obtain ⟨A, hA⟩ : ∃ A, T.required[i]? = some A := ⟨_, List.getElem?_eq_getElem hr⟩
    obtain ⟨l', c, hl', hw, hag⟩ := hreq i A hA
    rw [hi] at hl'; cases hl'
    exact ⟨A, c, .inl (List.mem_of_getElem? hA), hw, hag⟩
  · by_cases ho : i < T.required.length + T.optional.length
    · obtain ⟨A, hA⟩ : ∃ A, T.optional[i - T.required.length]? = some A :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨c, hw, hag⟩ := hopt (i - T.required.length) A l hA
        (by rw [show T.required.length + (i - T.required.length) = i by omega]; exact hi)
      exact ⟨A, c, .inr (.inl (List.mem_of_getElem? hA)), hw, hag⟩
    · obtain ⟨E, c, hE, hw, hag⟩ := hrest i l (by omega) hi
      exact ⟨E, c, .inr (.inr hE), hw, hag⟩

/-- **The class of an element location**, two levels down: at level 1 the
store's contract relates each element location's contract to its element
family, observed at level 0. -/
theorem elems_class {n W h s cs ls l} {T : TupleF} (hh : HeapOk (n+2) W h)
    (hs : lookup W s = some cs)
    (hcs : ∀ U v, cs 1 (by omega) U v → listT T 1 U v)
    (hsrc : ∀ A, (A ∈ T.required ∨ A ∈ T.optional ∨ T.rest = some A) →
      ∀ U u, A 0 U u → isSourceVal u = true)
    (hv : h[s]? = some (.arr ls)) (hl : some l ∈ ls) :
    ∃ u, h[l]? = some u ∧ isArr u = false := by
  obtain ⟨v, hv', hcv⟩ := hh.2 s cs hs
  rw [hv] at hv'; cases hv'
  have hT := hcs _ _ (hcv 1 (by omega))
  obtain ⟨A, c', hA, hw', hag⟩ := source_of_elements hT hl
  obtain ⟨c, hw, rfl⟩ := lookup_trunc_inv (by omega) W l c' hw'
  obtain ⟨u, hu, hcu⟩ := hh.2 l c hw
  exact ⟨u, hu, isArr_of_source (hsrc A hA _ u
    ((hag 0 (by omega) (trunc 0 (by omega) W) u).1 (hcu 0 (by omega))))⟩

end Verification.Footprints
