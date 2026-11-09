import Verification.Programs.ArgumentPathTracking

/-! # Fresh array stores in a regional body

A step's store region selecting a location allocated during the invocation
selects no location of its entry heap, so it rebases to none
(`Footprints.RebaseEvidence.fresh`). The regional graph tracks which slots
hold such a value, and which hold a cell whose contents are one:

- a **fresh value** (`FreshValue b v`): no store itself, and its array store,
  where it has one, at or above `b`, the entry heap's length
  (`Footprints.FreshIfStore`). `null`, a number and an object of no store
  field meet it; it reads no heap.
- a **fresh cell** (`CellFresh b h c`): the object `c` has the field a cell
  holds its contents in, and its location holds a fresh value at `h`. It is
  an invariant of the cell's contents, read at each heap.

A value is fresh where it is a slot copy of a fresh slot, a constant, an
allocation of an object with a store field, a read of a fresh cell, or the
result of a call whose signature states a fresh result. A cell is fresh
where it is a copy of a fresh cell or an allocation holding a fresh value.
A step keeps every fresh cell where it changes no old location of class
value (`keepsValues`), or writes a fresh value. The facts are
GraphCode's slot facts (`edgesFresh`, `handlerFresh`) at these
properties. -/
namespace Verification.GraphCode.ArgumentRegionFresh
open ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules Footprints

/-- The field a cell holds its contents in. -/
def cellKey : PropKey := .str "value"

/-- A value of no store whose array store, where it has one, lies at or
above `b`. -/
def FreshValue (b : Nat) (v : Tm) : Prop := isArr v = false ∧ FreshIfStore b v

theorem FreshValue.lower {b b' : Nat} {v : Tm} (hb : b ≤ b') (h : FreshValue b' v) : FreshValue b v :=
  ⟨h.1, h.2.lower hb⟩

theorem freshAt_value {b : Nat} {v : Tm} (h : FreshAt b v) : FreshValue b v := by
  refine ⟨?_, FreshAt.ifStore h⟩
  obtain ⟨s, hs, -⟩ := h
  cases v <;> simp_all [storeOf, fieldsOf, isArr]

/-- A value of no field: a constant. -/
theorem freshValue_of_fields {b : Nat} {v : Tm} (ha : isArr v = false) (hf : fieldsOf v = []) :
    FreshValue b v :=
  ⟨ha, fun s hs => by simp [storeOf, hf] at hs⟩

/-- An object whose cell field's location holds a fresh value at `h`. -/
def CellFresh (b : Nat) (h : Heap) (c : Tm) : Prop :=
  ∃ l v, (fieldsOf c).lookup cellKey = some l ∧ h[l]? = some v ∧ FreshValue b v

/-- The cells the slots `C` hold are fresh at `h`. -/
def CellsHold (C : List Nat) (b : Nat) (ρ : Env) (h : Heap) : Prop := ∀ i ∈ C, CellFresh b h (ρ i)

/-- The slot facts of a node: the values at `F` fresh, the cells at `C`. -/
structure FreshHold (F C : List Nat) (b : Nat) (ρ : Env) (h : Heap) : Prop where
  values : ∀ i ∈ F, FreshValue b (ρ i)
  cells : CellsHold C b ρ h

/-! ## Keeping cells -/

/-- A region every location of which holds a store where it is read. -/
def storeOnly : Region → Bool
  | .cls .store => true
  | .inCls _ .store => true
  | _ => false

theorem storeOnly_mem {r : Region} {σ : Env} {h : Heap} {l : Nat} {v : Tm} (hs : storeOnly r = true)
    (hm : r.mem σ h l = true) (hv : h[l]? = some v) : isArr v = true := by
  cases r <;> simp only [storeOnly, Bool.false_eq_true] at hs
  case cls c =>
    cases c <;> simp only [Bool.false_eq_true] at hs
    simpa [Region.mem, hv, Cls.has] using hm
  case inCls r c =>
    cases c <;> simp only [Bool.false_eq_true] at hs
    simp only [Region.mem, hv, Bool.and_eq_true] at hm
    simpa [Cls.has] using hm.2

/-- A frame changing no location of class value: every entry keeps its
locations, or holds only stores. -/
def keepsValues (Ψ : Footprint) : Bool := Ψ.all fun e => e.2 == .keep || storeOnly e.1

/-- **A frame keeping values keeps every fresh cell**: a cell's location
holds a value of no store, which no entry of the frame changes. -/
theorem CellFresh.post {Ψ : Footprint} {σ : Env} {h h' : Heap} {b : Nat} {c : Tm}
    (hk : keepsValues Ψ = true) (hp : Post Ψ σ h h') (hc : CellFresh b h c) : CellFresh b h' c := by
  obtain ⟨l, v, hl, hv, hf⟩ := hc
  obtain ⟨v', hv', ha⟩ := hp.2 l v hv
  refine ⟨l, v', hl, hv', ?_⟩
  rcases ha with rfl | ⟨e, he, hm, hh⟩
  · exact hf
  · have hx := List.all_eq_true.mp hk e he
    simp only [Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with hkeep | hs
    · rw [hkeep] at hh
      simp only [Change.Holds] at hh
      rw [hh]; exact hf
    · have := storeOnly_mem hs hm hv
      rw [hf.1] at this; cases this

theorem CellsHold.post {Ψ : Footprint} {σ : Env} {C : List Nat} {b : Nat} {ρ : Env} {h h' : Heap}
    (hk : keepsValues Ψ = true) (hp : Post Ψ σ h h') (hc : CellsHold C b ρ h) : CellsHold C b ρ h' :=
  fun i hi => (hc i hi).post hk hp

/-- Writing a fresh value anywhere keeps every fresh cell. -/
theorem CellFresh.set {b : Nat} {h : Heap} {c u : Tm} {l : Nat} (hu : FreshValue b u)
    (hc : CellFresh b h c) : CellFresh b (h.set l u) c := by
  obtain ⟨l', v, hl, hv, hf⟩ := hc
  by_cases he : l = l'
  · subst he
    have hlt := (List.getElem?_eq_some_iff.mp hv).1
    exact ⟨l, u, hl, by simp [hlt], hu⟩
  · exact ⟨l', v, hl, by rw [List.getElem?_set_ne he]; exact hv, hf⟩

/-- Allocation keeps every fresh cell. -/
theorem CellFresh.append {b : Nat} {h : Heap} {c : Tm} (vs : List Tm) (hc : CellFresh b h c) :
    CellFresh b (h ++ vs) c := by
  obtain ⟨l, v, hl, hv, hf⟩ := hc
  exact ⟨l, v, hl, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1]; exact hv, hf⟩

/-! ## Runs of a node -/

/-- A property of each state a run passes through gives the run's
postconditions. -/
theorem safePostExc_invariant {Ξ T : Fam} {I : Heap → Tm → Prop} {Q : Heap → Tm → Prop}
    {R : Heap → Prop}
    (hstep : ∀ {h t h' t'}, I h t → Step h t h' t' → I h' t')
    (hval : ∀ {h v}, I h v → isVal v = true → Q h v)
    (hraise : ∀ {h t v}, I h t → Raises t v → R h) :
    ∀ {n W h t}, I h t → Safe Ξ T n W h t → HeapObservations.SafePostExc Ξ T Q R n W h t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hi hs
    rcases hs with (⟨hv, ht⟩ | hth) | ⟨U, h', t', hx, hu, st, hh, hs⟩
    · exact .inl (.inl ⟨hv, ht, hval hi hv⟩)
    · exact .inl (.inr ⟨hth, hraise hi hth.choose_spec.1⟩)
    · exact .inr ⟨U, h', t', hx, hu, st, hh, ih (hstep hi st) hs⟩

/-- A slot's value, unchanged heap. -/
theorem value_run {Ξ T : Fam} {Q : Heap → Tm → Prop} {R : Heap → Prop} {n W h v}
    (hv : isVal v = true) (hq : Q h v) (hs : Safe Ξ T n W h v) :
    HeapObservations.SafePostExc Ξ T Q R n W h v :=
  safePostExc_invariant (I := fun h' t => h' = h ∧ t = v)
    (fun ⟨_, ht⟩ st => by subst ht; exact absurd st (value_no_step hv))
    (fun ⟨hh, ht⟩ _ => by subst hh; subst ht; exact hq)
    (fun ⟨_, ht⟩ hr => by subst ht; rw [raises_not_val hr] at hv; cases hv) ⟨rfl, rfl⟩ hs

/-! ## Allocation -/

/-- A term allocating an object with a store field, its initializers first
or a binding before it. -/
def AllocShape (t : Tm) : Prop :=
  (∃ c ns inits, t = .makeAt c ns inits ∧ arrayStoreKey ∈ ns) ∨
    (∃ a c ns inits, t = .letE a (.makeAt c ns inits) ∧ arrayStoreKey ∈ ns)

theorem lookup_slots_mem {k : PropKey} : ∀ {ns : List PropKey} {b : Nat}, k ∈ ns →
    ∃ l, (slots b ns).lookup k = some l ∧ b ≤ l
  | [], _, hk => by simp at hk
  | a :: ns, b, hk => by
    by_cases he : k = a
    · subst he; exact ⟨b, by simp [slots], Nat.le_refl _⟩
    · have hk' : k ∈ ns := by simpa [he] using hk
      obtain ⟨l, hl, hle⟩ := lookup_slots_mem (b := b + 1) hk'
      refine ⟨l, ?_, by omega⟩
      simp only [slots, List.lookup]
      have : (k == a) = false := by simpa using he
      rw [this]; exact hl

theorem subst_makeAt (j : Nat) (a : Tm) (c : CallCode) (ns : List PropKey) (xs : List Tm) :
    ∃ c' xs', subst j a (.makeAt c ns xs) = .makeAt c' ns xs' := by
  cases c <;> simp only [subst] <;> exact ⟨_, _, rfl⟩

/-- An allocation's step: it stays an allocation, or returns an object whose
store field's location is past the heap it allocated in. -/
theorem alloc_step {b : Nat} {h h' : Heap} {t t' : Tm} (hb : b ≤ h.length) (hs : AllocShape t)
    (st : Step h t h' t') : b ≤ h'.length ∧ (AllocShape t' ∨ (isVal t' = true ∧ FreshAt b t')) := by
  refine ⟨Nat.le_trans hb (step_length_le st), ?_⟩
  rcases hs with ⟨c, ns, inits, rfl, hk⟩ | ⟨a, c, ns, inits, rfl, hk⟩
  · cases st with
    | makeArg _ _ _ => exact .inl (.inl ⟨_, _, _, rfl, hk⟩)
    | makeFields _ _ =>
      obtain ⟨l, hl, hle⟩ := lookup_slots_mem (b := h.length) hk
      exact .inr ⟨rfl, l, by simpa [storeOf, fieldsOf] using hl, Nat.le_trans hb hle⟩
  · cases st with
    | letC _ => exact .inl (.inr ⟨_, _, _, _, rfl, hk⟩)
    | letV _ =>
      obtain ⟨c', xs', he⟩ := subst_makeAt 0 a c ns inits
      exact .inl (.inl ⟨c', ns, xs', he, hk⟩)

theorem allocShape_not_val {t : Tm} (hs : AllocShape t) : isVal t = false := by
  rcases hs with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _⟩ <;> rfl

/-- **An allocation returns a fresh store**: its store field's location is
at least the heap's length where it started, so at least `b`. -/
theorem alloc_fresh {Ξ T : Fam} {n W h t} {b : Nat} (hb : b ≤ h.length) (hs : AllocShape t)
    (hsafe : Safe Ξ T n W h t) : HeapObservations.SafePostExc Ξ T (fun _ v => FreshAt b v) (fun _ => True) n W h t :=
  safePostExc_invariant
    (I := fun h t => b ≤ h.length ∧ (AllocShape t ∨ (isVal t = true ∧ FreshAt b t)))
    (fun ⟨hb, hi⟩ st => by
      rcases hi with hi | ⟨hv, _⟩
      · exact alloc_step hb hi st
      · exact absurd st (value_no_step hv))
    (fun ⟨_, hi⟩ hv => by
      rcases hi with hi | ⟨_, hf⟩
      · rw [allocShape_not_val hi] at hv; cases hv
      · exact hf)
    (fun _ _ => trivial) ⟨hb, .inl hs⟩ hsafe

/-- **A cell allocated holding a fresh value is fresh**: the object's cell
field, its first, is at the location the allocation gives the value. -/
theorem cellAlloc_fresh {Ξ T : Fam} {n W h} {b : Nat} {code : CallCode} {ns : List PropKey} {vs : List Tm}
    {i : Nat} (hnd : ns.Nodup) (hi : i < ns.length) (hk : ns[i] = cellKey) (hlen : ns.length = vs.length)
    (hvals : ∀ v ∈ vs, isVal v = true) (hf : ∀ v, vs[i]? = some v → FreshValue b v)
    (hsafe : Safe Ξ T n W h (.makeAt code ns vs)) :
    HeapObservations.SafePostExc Ξ T (fun h' v => CellFresh b h' v ∧ h.IsPrefix h') (fun _ => True)
      n W h (.makeAt code ns vs) := by
  cases n with
  | zero => trivial
  | succ n =>
    have st : Step h (.makeAt code ns vs) (h ++ vs ++ [.nul]) (.objAt (slots h.length ns) code (h.length + vs.length)) :=
      .makeFields hvals hlen
    rcases hsafe with (⟨hv, _⟩ | hth) | ⟨U, h', t', hx, hu, st', hh, hs⟩
    · simp [isVal] at hv
    · exact absurd st hth.no_step
    · obtain ⟨rfl, rfl⟩ := Step_det st' st
      refine .inr ⟨U, _, _, hx, hu, st', hh, value_run rfl ⟨?_, ⟨vs ++ [.nul], by simp⟩⟩ hs⟩
      have hvi : i < vs.length := hlen ▸ hi
      refine ⟨h.length + i, vs[i], ?_, ?_, hf _ (List.getElem?_eq_getElem hvi)⟩
      · rw [← hk]; exact lookup_slots hnd hi
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega)]
        simp [hvi]

/-! ## Reading and writing a cell -/

/-- **A fresh cell's read returns a fresh value**, at the same heap. -/
theorem cellRead_fresh {Ξ T : Fam} {n W h} {b : Nat} {c : Tm} (hc : CellFresh b h c)
    (hvals : ∀ (l : Nat) (v : Tm), h[l]? = some v → isVal v = true)
    (hsafe : Safe Ξ T n W h (.readAt cellKey c)) :
    HeapObservations.SafePostExc Ξ T (fun h' v => h' = h ∧ FreshValue b v) (fun h' => h' = h)
      n W h (.readAt cellKey c) := by
  obtain ⟨l, u, hl, hu, hf⟩ := hc
  obtain ⟨fs, code, oid, rfl⟩ : ∃ fs code oid, c = .objAt fs code oid := by
    cases c <;> simp [fieldsOf] at hl
    exact ⟨_, _, _, rfl⟩
  have hl' : fs.lookup cellKey = some l := by simpa [fieldsOf] using hl
  refine safePostExc_invariant
    (I := fun h' t => h' = h ∧ (t = .readAt cellKey (.objAt fs code oid) ∨ (isVal t = true ∧ FreshValue b t)))
    (fun ⟨hh, hi⟩ st => ?_) (fun ⟨hh, hi⟩ hv => ?_) (fun ⟨hh, _⟩ _ => hh) ⟨rfl, .inl rfl⟩ hsafe
  · subst hh
    rcases hi with rfl | ⟨hv, _⟩
    · cases st with
      | readC s => exact absurd s (value_no_step rfl)
      | readField hl₁ hv₁ =>
        rw [hl'] at hl₁; cases hl₁
        rw [hu] at hv₁; cases hv₁
        exact ⟨rfl, .inr ⟨hvals _ _ hu, hf⟩⟩
      | readProto hn _ _ => rw [hl'] at hn; cases hn
      | readMissing hn _ => rw [hl'] at hn; cases hn
    · exact absurd st (value_no_step hv)
  · rcases hi with rfl | ⟨_, hf'⟩
    · simp [isVal] at hv
    · exact ⟨hh, hf'⟩

/-- **A write of a fresh value keeps every fresh cell**: it changes one
location, to that value. -/
theorem freshWrite_cells {Ξ T : Fam} {n W h} {b : Nat} {f : PropKey} {a u : Tm} {C : List Nat} {ρ : Env}
    (ha : isVal a = true) (hu : isVal u = true) (hf : FreshValue b u) (hc : CellsHold C b ρ h)
    (hsafe : Safe Ξ T n W h (.writeAt f a u)) :
    HeapObservations.SafePostExc Ξ T (fun h' _ => CellsHold C b ρ h') (fun h' => CellsHold C b ρ h')
      n W h (.writeAt f a u) :=
  safePostExc_invariant (I := fun h' t => CellsHold C b ρ h' ∧ (t = .writeAt f a u ∨ isVal t = true))
    (fun ⟨hc, hi⟩ st => by
      rcases hi with rfl | hv
      · obtain ⟨-, -, -, l, -, -, -, rfl, rfl⟩ := HeapExpressionRules.write_inv ha hu st
        exact ⟨fun i hi => (hc i hi).set hf, .inr rfl⟩
      · exact absurd st (value_no_step hv))
    (fun ⟨hc, _⟩ _ => hc) (fun ⟨hc, _⟩ _ => hc) ⟨hc, .inl rfl⟩ hsafe

/-! ## A node's freshness obligation -/

/-- The fresh slot facts at each label: values, and cells. -/
structure FreshTables where
  values : List (List Nat)
  cells : List (List Nat)

/-- A node's run keeps its fresh facts: from a context ordinary graph
checking established, with the values at `F` fresh and the cells at `C`
fresh against `b`, a bound at most the heap's length, its normal return
keeps every cell at `C` fresh, and returns a fresh value where `outF` and a
fresh cell where `outC`; where `thr`, a throw keeps every cell at `C`
fresh. -/
def FreshWithin [DecidableEq ι] (G : NormalGraph ι) (c : NodeEvidence ι) (t : Tm) (F C : List Nat)
    (outF outC thr : Bool) : Prop :=
  ∀ n W h ρ (b : Nat), b ≤ h.length → FreshHold F C b ρ h →
    EnvOk G (entry c) ρ n W → PromiseCalls.ImpliesOk G c.implies ρ n W →
    HeapKnowledge.Holds (entryFacts G c) ρ h → WorldAdm W → HeapOk n W h →
    HeapObservations.SafePostExc (excOf G) (meaning G (result c))
      (fun h' v => (outF = true → FreshValue b v) ∧ (outC = true → CellFresh b h' v) ∧ CellsHold C b ρ h')
      (fun h' => thr = true → CellsHold C b ρ h') n W h (instantiate 0 ρ t)

end Verification.GraphCode.ArgumentRegionFresh
