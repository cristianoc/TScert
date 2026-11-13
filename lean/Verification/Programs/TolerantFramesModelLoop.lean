import Verification.Programs.TolerantFramesExamples

/-! # Tolerant frames: the note's loop, one closed instance of graph safety

The loop `for (j = from; j < to; j++) out[j] = xs[j]` as a graph of six
nodes (`loopGraph`): the initialisation `j = from`, the guard `j < to`, the
read `xs[j]`, the element write `out[j] = v`, the increment `j + 1` and the
exit. `xs` and `out` are arrays of source values (`arrayF`): objects whose
array-store field holds a store under the tuple contract every position of
which, required or not, holds a source value (`storeF`); nothing relates
`xs` and `out`, so they may be one object. Every node is checked here from the
semantics alone, and `loop_safe` is `graph_safe` with no premise about the
graph: from every state where `0 ≤ from`, `to ≤ |xs|` and `xs`, `out` are
such arrays, the loop's run never gets stuck and returns `null`, raising
nothing. -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations ControlFlow PointClaims

/-! ## The world of the loop: arrays of source values -/

/-- The source values: every value but an array store. -/
def srcF : Fam := fun _ _ v => isSourceVal v = true

theorem srcF_adm : Adm srcF := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem srcF_valOnly : ValOnly srcF := fun _ _ v h => by
  cases v <;> simp_all [srcF, isSourceVal, isVal]

theorem srcF_not_arr {n : Nat} {W : WorldT n} {v : Val} (h : srcF n W v) : isArr v = false := by
  cases v <;> simp_all [srcF, isSourceVal, isArr]

/-- The tuple contract of a store of source values: no required or optional
position, every position under the rest, holes allowed. -/
def anyTuple : TupleF := { required := [], optional := [], rest := some srcF, presence := .sparse }

/-- A store every listed cell of which holds source values, its contract
exactly theirs. -/
def storeF : Fam := listT anyTuple

/-- An array of source values: an object whose array-store field's location
has the store contract `storeF`. -/
def arrayF : Fam := recT [(arrayStoreKey, storeF)]

/-- A listed cell of such a store has the contract of the source values. -/
theorem storeF_cell {k : Nat} {W : WorldT k} {ls : List (Option Nat)} {i l : Nat}
    (h : storeF k W (.arr ls)) (hl : ls[i]? = some (some l)) :
    ∃ c : Ctr k, lookup W l = some c ∧ ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val),
      c j hj W' u ↔ srcF j W' u := by
  obtain ⟨ls', he, -, -, -, -, -, -, hrest⟩ := h
  cases he
  obtain ⟨E, c, hE, hw, hag⟩ := hrest i l (by simp [anyTuple]) hl
  simp only [anyTuple, Option.some.injEq] at hE
  subst hE
  exact ⟨c, hw, fun j hj W' u => ⟨(hag j hj W' u).1, (hag j hj W' u).2 rfl⟩⟩

/-- **A store of source values grown at any index** below the most elements a
store holds, a fresh cell of the source values' contract listed there; holes
may open before it. -/
theorem storeF_grow {k : Nat} {W : WorldT k} {ls : List (Option Nat)} {i m : Nat}
    (h : storeF k W (.arr ls)) (hi : i < maxArrayLength) (hm : lookup W m = some (res srcF)) :
    storeF k W (.arr (placeAt ls i m)) := by
  obtain ⟨ls', he, -, -, hmax, -, -, -, hrest⟩ := h
  cases he
  refine ⟨_, rfl, fun _ _ => by simp [StorePresence, anyTuple], by simp [anyTuple],
    by rw [placeAt_length]; omega, fun hn => by simp [anyTuple] at hn, fun i A hA => by simp [anyTuple] at hA,
    fun i A l hA => by simp [anyTuple] at hA, ?_⟩
  intro i' l hi' hl
  rw [placeAt_getElem?] at hl
  split at hl
  · cases Option.some.inj (Option.some.inj hl)
    exact ⟨srcF, res srcF, rfl, hm, fun _ _ _ _ => SlotContract.refl _ _⟩
  · split at hl
    · exact hrest i' l hi' hl
    · split at hl <;> cases hl

/-- An array of source values exposes its store field's location and the
store contract it has. -/
theorem arrayF_at {k : Nat} {W : WorldT k} {v : Val} (h : arrayF k W v) :
    ∃ (flds : List (PropKey × Nat)) (fl : Nat) (c : Ctr k) (oid : Nat),
      v = .objAt flds .absent oid ∧ flds.lookup arrayStoreKey = some fl ∧ lookup W fl = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u ↔ storeF j W' u :=
  recT_at (List.mem_singleton_self _) h

/-! ## The assertions -/

/-- Slot `x` holds an array of source values, at the state's world. -/
def ArrAt (x : Nat) : Assertion := fun ρ _ s => arrayF s.n s.W (ρ x)

/-- Being such an array is a fact of the world: every admissible transition
keeps it. -/
theorem arrAt_invariant (x : Nat) : Invariant (ArrAt x) :=
  fun _ _ _ s' ⟨hle, hx⟩ h => (recT_adm _).transfer h s'.n hle s'.W hx

theorem arrAt_congr {x y : Nat} {ρ ρ' : Env} {m m' : Nat} {s : IndexedHeap} (he : ρ' x = ρ y)
    (h : ArrAt y ρ m s) : ArrAt x ρ' m' s := by
  unfold ArrAt at h ⊢
  rw [he]
  exact h

/-- The guard's fact: slot `j` holds an integer below the integer slot `t`
holds. It reads no heap. -/
def Below (j t : Nat) : Assertion := fun ρ _ _ =>
  ∃ a b, HeapKnowledge.intValue (ρ j) = some a ∧ HeapKnowledge.intValue (ρ t) = some b ∧ a < b

/-- Slot `x` holds a source value. It reads no heap. -/
def SrcAt (x : Nat) : Assertion := fun ρ _ _ => isSourceVal (ρ x) = true

/-- `y ≤ |x|` read at slots one higher, after a push. -/
theorem lowerBound_push {y x : Nat} {v : Tm} {ρ : Env} {m m' : Nat} {s : IndexedHeap}
    (h : LowerBound ε y x ρ m s) : LowerBound ε (y + 1) (x + 1) (push v ρ) m' s :=
  (HeapKnowledge.IndexFact.holdsAt_mapM (f := fun i => some (i + 1)) (F := lowerBoundFact y x) rfl
    (fun _ _ _ hg => by cases hg; rfl)).mpr h

/-- `y ≤ |x|` at another heap with the same contents. -/
theorem lowerBound_heap {y x : Nat} {ρ : Env} {m : Nat} {s s' : IndexedHeap} (hh : s'.h = s.h)
    (h : LowerBound ε y x ρ m s) : LowerBound ε y x ρ m s' := by
  unfold LowerBound at h ⊢
  rw [hh]
  exact h


/-! ## One step keeping the heap -/

/-- A step that keeps the heap, then the rest at the truncated world. -/
theorem pure_step {Ξ T : Fam} {Q : Post} {R : Heap → Prop} {n : Nat} {W : WorldT (n + 1)} {h : Heap} {t t' : Tm}
    (ha : WorldAdm W) (ho : HeapOk (n + 1) W h) (hst : Step h t h t')
    (hs : SafePostExc Ξ T Q R n (trunc n (Nat.le_succ n) W) h t') : SafePostExc Ξ T Q R (n + 1) W h t :=
  .inr ⟨_, h, t', WExt_refl _, WorldAdm_trunc _ ha, hst, HeapOk_trunc n W h ho, hs⟩

/-- The store an array of source values holds: at its store field's location,
a store under `storeF` at every level below the budget. -/
theorem arrayF_store {n : Nat} {W : WorldT (n + 1)} {h : Heap} {v : Val} (ho : HeapOk (n + 1) W h)
    (hv : arrayF (n + 1) W v) :
    ∃ (flds : List (PropKey × Nat)) (fl : Nat) (c : Ctr (n + 1)) (oid : Nat) (ls : List (Option Nat)),
      v = .objAt flds .absent oid ∧ flds.lookup arrayStoreKey = some fl ∧ lookup W fl = some c ∧
      (∀ (j : Nat) (hj : j < n + 1) (W' : WorldT j) (u : Val), c j hj W' u ↔ storeF j W' u) ∧
      h[fl]? = some (.arr ls) ∧
      ∀ (j : Nat) (hj : j < n + 1), storeF j (trunc j (Nat.le_of_lt hj) W) (.arr ls) := by
  obtain ⟨flds, fl, c, oid, rfl, hfd, hc, hag⟩ := arrayF_at hv
  obtain ⟨u, hu, hcu⟩ := ho.2 fl c hc
  obtain ⟨ls, rfl, -⟩ := (hag 0 (by omega) _ u).mp (hcu 0 (by omega))
  exact ⟨flds, fl, c, oid, ls, rfl, hfd, hc, hag, hu, fun j hj => (hag j hj _ _).mp (hcu j hj)⟩

/-- A listed cell of a store of source values, at a positive budget, holds a
source value, and its contract is theirs. -/
theorem cell_src {k : Nat} {W : WorldT (k + 1)} {h : Heap} {ls : List (Option Nat)} {i l : Nat}
    (ho : HeapOk (k + 1) W h) (hs : storeF (k + 1) W (.arr ls)) (hl : ls[i]? = some (some l)) :
    ∃ (c : Ctr (k + 1)) (w : Val), lookup W l = some c ∧
      (∀ (j : Nat) (hj : j < k + 1) (W' : WorldT j) (u : Val), c j hj W' u ↔ srcF j W' u) ∧
      h[l]? = some w ∧ isSourceVal w = true := by
  obtain ⟨c, hc, hag⟩ := storeF_cell hs hl
  obtain ⟨w, hw, hcw⟩ := ho.2 l c hc
  exact ⟨c, w, hc, hag, hw, (hag 0 (by omega) _ w).mp (hcw 0 (by omega))⟩

theorem elemLoc_some {ls : List (Option Nat)} {b : UInt64} {l : Nat} (h : elemLoc ls b = some l) :
    ∃ k, indexOfBits b = some k ∧ ls[k]? = some (some l) := by
  simp only [elemLoc, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, o, ho, he⟩ := h
  cases o with
  | none => cases he
  | some l' => cases he; exact ⟨k, hk, ho⟩


/-! ## The element write `out[j] = v`

`out` in slot 4, `j` in slot 1, `v` in slot 0, as the pass lowers an element
write at a run-time index (`ExpressionEffects.elemVarWriteSlots`). Three steps:
the store is read, the element written (a listed cell takes the value, or a
fresh cell is listed), the store put back. -/

/-- The write's term. -/
def writeTerm : Tm :=
  .writeAt arrayStoreKey (.var 4) (.setElem (.readAt arrayStoreKey (.var 4)) (.var 1) (.var 0))

theorem writeTerm_inst (ρ : Env) : instantiate 0 ρ writeTerm =
    .writeAt arrayStoreKey (ρ 4) (.setElem (.readAt arrayStoreKey (ρ 4)) (ρ 1) (ρ 0)) := by
  simp [writeTerm, instantiate]

/-- **The element write's local judgment, from the semantics**: where slot 4
holds an array of source values, slot 0 a source value and slot 1 a valid
array index, the write takes three steps to `null`, raising nothing, within
`{values: any, stores: grow}` from its first heap. Nothing is assumed of the
array read in slot 3: it may be `out`. -/
theorem write_safe {Ξ T : Fam} (hT : ∀ n W, T n W .nul) {ρ : Env} {b : UInt64} {k : Nat}
    (hv : isSourceVal (ρ 0) = true) (hb : ρ 1 = .num b) (hidx : indexOfBits b = some k) :
    ∀ (n : Nat) (W : WorldT n) (h : Heap), WorldAdm W → HeapOk n W h → arrayF n W (ρ 4) →
      SafePostExc Ξ T (fun h' _ => growEffect.Holds h h' ∧ True) (fun h' => growEffect.Holds h h' ∧ True)
        n W h (instantiate 0 ρ writeTerm) := by
  intro n W h ha ho hout
  rw [writeTerm_inst, hb]
  generalize hvv : ρ 0 = v at hv
  have hval : isVal v = true := srcF_valOnly 0 (trunc 0 (Nat.zero_le _) W) v hv
  cases n with
  | zero => trivial
  | succ n1 =>
  obtain ⟨flds, fl, cfl, oid, ls, ho4, hfd, hcfl, hagf, hfl, hst⟩ := arrayF_store ho hout
  rw [ho4]
  -- the store is read
  refine pure_step ha ho (.writeC2 rfl (.setC1 (.readField hfd hfl))) ?_
  cases n1 with
  | zero => trivial
  | succ n2 =>
  have ha1 := WorldAdm_trunc (Nat.le_succ (n2 + 1)) ha
  have ho1 := HeapOk_trunc (n2 + 1) W h ho
  have hst1 : storeF (n2 + 1) (trunc (n2 + 1) (Nat.le_succ _) W) (.arr ls) := hst (n2 + 1) (by omega)
  have hflt : fl < h.length := (List.getElem?_eq_some_iff.mp hfl).1
  cases hloc : elemLoc ls b with
  | some l =>
    -- a listed cell takes the value
    obtain ⟨i, -, hli⟩ := elemLoc_some hloc
    obtain ⟨c, w, hc, hagc, hw, hws⟩ := cell_src ho1 hst1 hli
    have hlt : l < h.length := (List.getElem?_eq_some_iff.mp hw).1
    have hnarr : isArr w = false := srcF_not_arr (n := 0) (W := trunc 0 (Nat.zero_le _) W) hws
    have ho2 : HeapOk n2 (trunc n2 (Nat.le_succ n2) (trunc (n2 + 1) (Nat.le_succ _) W)) (h.set l v) :=
      write_sound n2 _ h l _ v (HeapOk_trunc n2 _ h ho1) (lookup_trunc (Nat.le_succ n2) _ l c hc)
        (fun j hj => (hagc j (by omega) _ v).mpr hv)
    refine .inr ⟨_, h.set l v, _, WExt_refl _, WorldAdm_trunc _ ha1, .writeC2 rfl (.setPresent hval hloc hlt),
      ho2, ?_⟩
    cases n2 with
    | zero => trivial
    | succ n3 =>
    -- the store is put back, unchanged
    have hcfl2 := lookup_trunc (Nat.le_succ (n3 + 1)) _ fl _
      (lookup_trunc (Nat.le_succ (n3 + 2)) W fl cfl hcfl)
    have ho3 := write_sound n3 _ (h.set l v) fl _ (.arr ls) (HeapOk_trunc n3 _ _ ho2)
      (lookup_trunc (Nat.le_succ n3) _ fl _ hcfl2) (fun j hj => by
        show cfl j _ _ (.arr ls)
        simp only [trunc_trunc]
        exact (hagf j (by omega) _ _).mpr (hst j (by omega)))
    refine .inr ⟨_, _, .nul, WExt_refl _, WorldAdm_trunc _ (WorldAdm_trunc _ ha1),
      .writeField rfl hfd (by simpa using hflt), ho3, SafePostExc.value rfl (hT _ _) ⟨?_, trivial⟩⟩
    exact Footprints.Closed.Holds.mono (by decide) (ExpressionEffects.elem_present_holds hfl hw hnarr)
  | none =>
    -- a fresh cell is listed
    have hcadm : ∀ c ∈ [(res srcF : Ctr n2)], CtrAdm c := by
      intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      exact ⟨fun i _ U U' hx w hw => srcF_adm.mono i U U' hx w hw, fun i _ U w hw => srcF_valOnly i U w hw⟩
    have hlen : h.length = (toList (trunc n2 (Nat.le_succ n2) (trunc (n2 + 1) (Nat.le_succ _) W))).length := by
      have := ho.1; simp [trunc] at this ⊢; omega
    let W2 := appendWs (trunc n2 (Nat.le_succ n2) (trunc (n2 + 1) (Nat.le_succ _) W)) [res srcF]
    have ho2 : HeapOk n2 W2 (h ++ [v]) :=
      heap_allocs n2 _ _ h [v] (HeapOk_trunc n2 _ h ho1) (WorldAdm_trunc _ ha1) hcadm rfl (by
        intro q hq j hj
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq
        subst hq
        exact hv)
    have hx2 : WExt (trunc n2 (Nat.le_succ n2) (trunc (n2 + 1) (Nat.le_succ _) W)) W2 := WExt_appendWs _ _
    have ha2 : WorldAdm W2 := WorldAdm_appendWs (WorldAdm_trunc _ ha1) hcadm
    have hnew : lookup W2 h.length = some (res srcF) := by
      rw [hlen]
      simpa using lookup_appendWs (trunc n2 (Nat.le_succ n2) (trunc (n2 + 1) (Nat.le_succ _) W))
        [(res srcF : Ctr n2)] (i := 0) (by simp)
    refine .inr ⟨W2, h ++ [v], _, hx2, ha2, .writeC2 rfl (.setGrow hval hidx hloc), ho2, ?_⟩
    cases n2 with
    | zero => trivial
    | succ n3 =>
    have hcfl2 := WExt_lookup hx2 (lookup_trunc (Nat.le_succ (n3 + 1)) _ fl _
      (lookup_trunc (Nat.le_succ (n3 + 2)) W fl cfl hcfl))
    have ho3 := write_sound n3 _ (h ++ [v]) fl _ (.arr (placeAt ls k h.length)) (HeapOk_trunc n3 _ _ ho2)
      (lookup_trunc (Nat.le_succ n3) _ fl _ hcfl2) (fun j hj => by
        show cfl j _ _ _
        refine (hagf j (by omega) _ _).mpr (storeF_grow ?_ (indexOfBits_lt hidx) ?_)
        · refine (listT_adm anyTuple).mono j _ _ ?_ _ (hst j (by omega))
          rw [trunc_trunc]
          have := WExt_trunc (Nat.le_of_lt hj) (WExt_trunc (Nat.le_succ n3) hx2)
          simpa only [trunc_trunc] using this
        · have := lookup_trunc (Nat.le_of_lt hj) _ _ _ (lookup_trunc (Nat.le_succ n3) W2 _ _ hnew)
          simp only [trunc_trunc] at this ⊢
          exact this)
    refine .inr ⟨_, _, .nul, WExt_refl _, WorldAdm_trunc _ ha2,
      .writeField rfl hfd (by simp; omega), ho3, SafePostExc.value rfl (hT _ _) ⟨?_, trivial⟩⟩
    exact ExpressionEffects.elem_grow_holds hfl (indexOfBits_lt hidx)


/-! ## The guard `j < to` and the read `xs[j]` -/

/-- The guard's term: `j < to`, `j` in slot 0, `to` in slot 1. -/
def guardTerm : Tm := .arith .lt (.var 0) (.var 1)

/-- The read's term: `xs[j]`, `xs` in slot 2, `j` in slot 0. -/
def readTerm : Tm := .elemAt (.readAt arrayStoreKey (.var 2)) (.var 0)

theorem num_of_intValue {v : Val} {a : Int} (h : HeapKnowledge.intValue v = some a) :
    ∃ x, v = .num x ∧ SafeIntegers.SafeInt x a := by
  obtain ⟨x, rfl, hx⟩ := HeapKnowledge.intValue_safe h
  exact ⟨x, rfl, hx⟩

/-- `<` on two doubles of safe integers is the integers' order. -/
theorem lt_binop {x y : UInt64} {a b : Int} (hx : SafeIntegers.SafeInt x a) (hy : SafeIntegers.SafeInt y b) :
    binop .lt (.num x) (.num y) = some (if a < b then .tru else .fls) := by
  simp only [binop, reduceCtorEq, if_false, Arith.relational, if_true, relationalValue, relNumeric,
    Option.bind_some, numericRelation, SafeIntegers.doubleOrder_safe hx hy, Option.some.injEq]
  by_cases h : a < b
  · rw [Int.compare_eq_lt.mpr h, if_pos h]; rfl
  · rw [if_neg h]
    rcases Int.lt_or_eq_of_le (Int.not_lt.mp h) with h' | rfl
    · rw [Int.compare_eq_gt.mpr h']; rfl
    · rw [Int.compare_eq_eq.mpr rfl]; rfl

/-- **The guard's local judgment**: two safe integers compare in one step to
a Boolean, keeping the heap; `true` means the first is below the second. -/
theorem guard_safe {Ξ : Fam} {ce : Footprints.Closed} {Qe : Heap → Prop} {ρ : Env} {s : IndexedHeap} {a b : Int}
    (ha : HeapKnowledge.intValue (ρ 0) = some a) (hb : HeapKnowledge.intValue (ρ 1) = some b) :
    SafePostExc Ξ boolT
      (fun h' v => Footprints.Closed.empty.Holds s.h h' ∧ (v = .tru → ∃ a b, HeapKnowledge.intValue (ρ 0) = some a ∧
        HeapKnowledge.intValue (ρ 1) = some b ∧ a < b))
      (fun h' => ce.Holds s.h h' ∧ Qe h') s.n s.W s.h (instantiate 0 ρ guardTerm) := by
  obtain ⟨x, hx, hsx⟩ := num_of_intValue ha
  obtain ⟨y, hy, hsy⟩ := num_of_intValue hb
  obtain ⟨n, W, h, pos, adm, ok⟩ := s
  cases n with
  | zero => exact absurd pos (Nat.lt_irrefl 0)
  | succ n =>
    have hinst : instantiate 0 ρ guardTerm = .arith .lt (.num x) (.num y) := by
      simp [guardTerm, instantiate, hx, hy]
    rw [hinst]
    refine pure_step adm ok (.arithV (lt_binop hsx hsy)) (SafePostExc.value ?_ ?_
      ⟨Footprints.Closed.Holds.refl _ _, fun ht => ⟨a, b, ha, hb, ?_⟩⟩)
    · split <;> rfl
    · split
      · exact .inl rfl
      · exact .inr rfl
    · by_cases hab : a < b
      · exact hab
      · rw [if_neg hab] at ht; cases ht

/-- **The read's local judgment**: where slot 2 holds an array of source
values and slot 0 a number, `xs[j]` takes two steps to a source value, keeping
the heap: a listed cell's value, or `undefined` at a hole or past the end. -/
theorem read_safe {Ξ : Fam} {ce : Footprints.Closed} {Qe : Heap → Prop} {ρ : Env} {x : UInt64}
    (hj : ρ 0 = .num x) :
    ∀ (n : Nat) (W : WorldT n) (h : Heap), WorldAdm W → HeapOk n W h → arrayF n W (ρ 2) →
      SafePostExc Ξ srcF (fun h' _ => Footprints.Closed.empty.Holds h h' ∧ True) (fun h' => ce.Holds h h' ∧ Qe h')
        n W h (instantiate 0 ρ readTerm) := by
  intro n W h ha ho hxs
  have hinst : instantiate 0 ρ readTerm = .elemAt (.readAt arrayStoreKey (ρ 2)) (.num x) := by
    simp [readTerm, instantiate, hj]
  rw [hinst]
  cases n with
  | zero => trivial
  | succ n1 =>
  obtain ⟨flds, fl, cfl, oid, ls, ho2, hfd, -, -, hfl, hst⟩ := arrayF_store ho hxs
  rw [ho2]
  refine pure_step ha ho (.elemC1 (.readField hfd hfl)) ?_
  cases n1 with
  | zero => trivial
  | succ n2 =>
  have ho1 := HeapOk_trunc (n2 + 1) W h ho
  have ha1 := WorldAdm_trunc (Nat.le_succ (n2 + 1)) ha
  cases hloc : elemLoc ls x with
  | some l =>
    obtain ⟨i, -, hli⟩ := elemLoc_some hloc
    obtain ⟨-, w, -, -, hw, hws⟩ := cell_src ho1 (hst (n2 + 1) (by omega)) hli
    exact pure_step ha1 ho1 (.elemRead hloc hw)
      (SafePostExc.value (srcF_valOnly 0 (trunc 0 (Nat.zero_le _) W) w hws) hws ⟨Footprints.Closed.Holds.refl _ _, trivial⟩)
  | none =>
    exact pure_step ha1 ho1 (.elemAbsent hloc)
      (SafePostExc.value rfl rfl ⟨Footprints.Closed.Holds.refl _ _, trivial⟩)


/-! ## The graph, its assertions and its nodes checked -/

/-- `y ≤ |x|` as integers: the integer slot `y` holds is at most the length of
the store slot `x` holds. -/
theorem lowerBound_iff {y x : Nat} {ρ : Env} {m : Nat} {s : IndexedHeap} :
    LowerBound ε y x ρ m s ↔ ∃ a len, HeapKnowledge.intValue (ρ y) = some a ∧
      HeapKnowledge.lengthOf s.h (ρ x) = some len ∧ a ≤ len := by
  have e : LowerBound ε y x ρ m s ↔ PathLowerBound y x [] ρ m s := pathLowerBound_iff.symm
  rw [e]
  exact ⟨fun ⟨w, a, len, hw, ha, hl, hle⟩ => by cases hw; exact ⟨a, len, ha, hl, hle⟩,
    fun ⟨a, len, ha, hl, hle⟩ => ⟨ρ x, a, len, rfl, ha, hl, hle⟩⟩

/-- `y ≤ |x|` read at other slots holding the same values. -/
theorem lowerBound_env {y x y' x' : Nat} {ρ ρ' : Env} {m m' : Nat} {s : IndexedHeap}
    (hy : ρ' y' = ρ y) (hx : ρ' x' = ρ x) (h : LowerBound ε y x ρ m s) : LowerBound ε y' x' ρ' m' s := by
  rw [lowerBound_iff] at h ⊢
  rw [hy, hx]
  exact h

theorem nonNeg_congr {x y : Nat} {ρ ρ' : Env} {m m' : Nat} {s s' : IndexedHeap} (he : ρ' x = ρ y)
    (h : NonNeg y ρ m s) : NonNeg x ρ' m' s' := by
  unfold NonNeg at h ⊢
  rw [he]
  exact h

/-- The loop: the initialisation `j = from`, the guard `j < to`, the read
`v = xs[j]`, the write `out[j] = v`, the increment `j = j + 1` back to the
guard, and the exit returning `null`. The guard's environment is
`j, to, xs, out`; the body's `v, j, to, xs, out`. -/
def loopGraph : Program :=
  [⟨.var 0, .bind ⟨1, some [0, 2, 3, 4]⟩, none⟩,
   ⟨guardTerm, .branch ⟨2, none⟩ ⟨5, none⟩, none⟩,
   ⟨readTerm, .bind ⟨3, none⟩, none⟩,
   ⟨writeTerm, .effect ⟨4, none⟩, none⟩,
   ⟨incTerm, .bind ⟨1, some [0, 3, 4, 5]⟩, none⟩,
   ⟨.nul, .ret, none⟩]

/-- The head's facts at `j, to, xs, out`: `0 ≤ j`, `to ≤ |xs|`, and `xs`,
`out` arrays of source values. -/
def HeadAt (ε : HeapKnowledge.EntryState) : Assertion := fun ρ m s =>
  NonNeg 0 ρ m s ∧ LowerBound ε 1 2 ρ m s ∧ ArrAt 2 ρ m s ∧ ArrAt 3 ρ m s

/-- The body's facts at `v, j, to, xs, out`: the head's, one slot up, and the
guard's `j < to`. -/
def BodyAt (ε : HeapKnowledge.EntryState) : Assertion := fun ρ m s =>
  NonNeg 1 ρ m s ∧ LowerBound ε 2 3 ρ m s ∧ ArrAt 3 ρ m s ∧ ArrAt 4 ρ m s ∧ Below 1 2 ρ m s

/-- The node assertions. The entry's is the head's, at `from, to, xs, out`. -/
def loopPre (ε : HeapKnowledge.EntryState) : Nat → Assertion
  | 0 => HeadAt ε
  | 1 => HeadAt ε
  | 2 => fun ρ m s => HeadAt ε ρ m s ∧ Below 0 1 ρ m s
  | 3 => fun ρ m s => SrcAt 0 ρ m s ∧ BodyAt ε ρ m s
  | 4 => BodyAt ε
  | 5 => fun _ _ _ => True
  | _ => fun _ _ _ => False

/-- The head's facts survive every action of an effect within
`{values: any, stores: grow}`. -/
theorem headAt_action {c : Footprints.Closed} (hc : c.le growEffect = true) {ρ : Env} {m : Nat}
    {s₀ s : IndexedHeap} (ha : Action c.fp ρ s₀ s) (h : HeadAt ε ρ m s₀) : HeadAt ε ρ m s :=
  ⟨h.1, grow h.2.1 s (action_le_closed hc ha), arrAt_invariant 2 ρ m s₀ s ha.1 h.2.2.1,
    arrAt_invariant 3 ρ m s₀ s ha.1 h.2.2.2⟩

theorem bodyAt_action {c : Footprints.Closed} (hc : c.le growEffect = true) {ρ : Env} {m : Nat}
    {s₀ s : IndexedHeap} (ha : Action c.fp ρ s₀ s) (h : BodyAt ε ρ m s₀) : BodyAt ε ρ m s :=
  ⟨h.1, grow h.2.1 s (action_le_closed hc ha), arrAt_invariant 3 ρ m s₀ s ha.1 h.2.2.1,
    arrAt_invariant 4 ρ m s₀ s ha.1 h.2.2.2.1, h.2.2.2.2⟩

/-- The node assertions survive the administrative steps. -/
theorem loopPre_admin (m : Nat) : AdminClosed (loopPre ε) m := by
  have head : ∀ {ρ s s'}, Admissible s s' → s'.h = s.h → HeadAt ε ρ m s → HeadAt ε ρ m s' :=
    fun ha hh h => ⟨h.1, lowerBound_heap hh h.2.1, arrAt_invariant 2 _ m _ _ ha h.2.2.1,
      arrAt_invariant 3 _ m _ _ ha h.2.2.2⟩
  have body : ∀ {ρ s s'}, Admissible s s' → s'.h = s.h → BodyAt ε ρ m s → BodyAt ε ρ m s' :=
    fun ha hh h => ⟨h.1, lowerBound_heap hh h.2.1, arrAt_invariant 3 _ m _ _ ha h.2.2.1,
      arrAt_invariant 4 _ m _ _ ha h.2.2.2.1, h.2.2.2.2⟩
  intro l ρ s s' ha hh hp
  match l, hp with
  | 0, hp => exact head ha hh hp
  | 1, hp => exact head ha hh hp
  | 2, hp => exact ⟨head ha hh hp.1, hp.2⟩
  | 3, hp => exact ⟨hp.1, body ha hh hp.2⟩
  | 4, hp => exact body ha hh hp
  | 5, hp => exact hp

/-- The exception family of no value: no node raises. -/
theorem above_noFam {s : IndexedHeap} {e : Tm} (h : Above noFam s e) : False := by
  obtain ⟨_, _, h⟩ := h
  exact h

/-- **Every node of the loop is checked**, from the semantics: its local
judgment and its exit obligations, at every state its assertion holds. -/
theorem loop_checked (m : Nat) :
    NodesChecked loopGraph (loopPre ε) noFam nulT (fun _ => True) (fun _ => True) m := by
  intro l ρ s hp
  match l, hp with
  | 0, hp =>
    -- the initialisation `j = from`
    obtain ⟨a, ha, -⟩ := hp.1
    obtain ⟨x, hx, -⟩ := num_of_intValue ha
    refine ⟨_, rfl, noFam, numT, .empty, .empty, fun _ v => v = ρ 0, fun _ => True, ?_, ?_⟩
    · show SafePostExc _ _ _ _ s.n s.W s.h (instantiate 0 ρ (.var 0))
      simp only [instantiate, Nat.not_lt_zero, if_false, Nat.sub_zero]
      exact SafePostExc.value (by rw [hx]; rfl) ⟨x, hx⟩ ⟨Footprints.Closed.Holds.refl _ _, rfl⟩
    refine ⟨fun _ _ _ _ _ _ _ _ => trivial, fun s' v ha _ _ hv => ?_, fun _ _ _ _ hab _ => (above_noFam hab).elim⟩
    subst hv
    have hh := headAt_action (by decide) ha hp
    exact ⟨nonNeg_congr (ρ := ρ) rfl hh.1, lowerBound_env (mapEnv_push_slot rfl) (mapEnv_push_slot rfl) hh.2.1,
      arrAt_congr (mapEnv_push_slot rfl) hh.2.2.1, arrAt_congr (mapEnv_push_slot rfl) hh.2.2.2⟩
  | 1, hp =>
    -- the guard `j < to`
    obtain ⟨a, ha, -⟩ := hp.1
    obtain ⟨b, len, hb, -, -⟩ := lowerBound_iff.mp hp.2.1
    refine ⟨_, rfl, noFam, boolT, .empty, .empty, _, fun _ => True, guard_safe ha hb, ?_⟩
    refine ⟨fun _ _ _ _ _ hT _ _ => hT, fun s' v ha' _ ⟨_, _, hT⟩ hq => ?_,
      fun _ _ _ _ hab _ => (above_noFam hab).elim⟩
    rcases hT with rfl | rfl
    · exact .inl ⟨rfl, headAt_action (by decide) ha' hp, hq rfl⟩
    · exact .inr ⟨rfl, trivial⟩
  | 2, hp =>
    -- the read `v = xs[j]`
    obtain ⟨a, ha, -⟩ := hp.1.1
    obtain ⟨x, hx, -⟩ := num_of_intValue ha
    refine ⟨_, rfl, noFam, srcF, .empty, .empty, _, fun _ => True,
      read_safe hx s.n s.W s.h s.adm s.ok hp.1.2.2.1, ?_⟩
    refine ⟨fun _ _ _ _ _ _ _ _ => trivial, fun s' v ha' _ ⟨_, _, hT⟩ _ => ?_,
      fun _ _ _ _ hab _ => (above_noFam hab).elim⟩
    have hh := headAt_action (by decide) ha' hp.1
    show SrcAt 0 (push v ρ) m s' ∧ BodyAt ε (push v ρ) m s'
    exact ⟨hT, hh.1, lowerBound_push hh.2.1, arrAt_congr (ρ := ρ) rfl hh.2.2.1, arrAt_congr (ρ := ρ) rfl hh.2.2.2, hp.2⟩
  | 3, hp =>
    -- the write `out[j] = v`
    have hp3 : BodyAt ε ρ m s := hp.2
    obtain ⟨hv, ⟨a, ha, h0⟩, hlb, -, hout, ⟨a', b, ha', hb, hab⟩⟩ := hp
    rw [ha] at ha'; cases ha'
    obtain ⟨b', len, hb', hlen, hle⟩ := lowerBound_iff.mp hlb
    rw [hb] at hb'; cases hb'
    obtain ⟨st, ls, -, -, rfl, hmax⟩ := HeapKnowledge.lengthOf_store hlen
    obtain ⟨x, hx, hsx⟩ := num_of_intValue ha
    have hidx := HeapKnowledge.indexOfBits_safe hsx h0 (by omega)
    refine ⟨_, rfl, noFam, nulT, growEffect, growEffect, fun _ _ => True, fun _ => True,
      write_safe (Ξ := noFam) (T := nulT) (fun _ _ => rfl) hv hx hidx s.n s.W s.h s.adm s.ok hout, ?_⟩
    refine ⟨fun _ _ _ _ _ _ _ _ => trivial, fun s' v ha' _ _ _ => ?_,
      fun _ _ _ _ hab _ => (above_noFam hab).elim⟩
    exact bodyAt_action (by decide) ha' hp3
  | 4, hp =>
    -- the increment `j = j + 1`, back to the guard
    have hp4 : BodyAt ε ρ m s := hp
    obtain ⟨⟨a, ha, h0⟩, -, -, -, ⟨a', b, ha', hb, hab⟩⟩ := hp
    rw [ha] at ha'; cases ha'
    refine ⟨_, rfl, noFam, numT, .empty, .empty, _, fun _ => True,
      increment_judgment (fun _ _ b => ⟨b, rfl⟩) ha hb h0 hab, ?_⟩
    refine ⟨fun _ _ _ _ _ _ _ _ => trivial, fun s' v ha'' _ _ hq => ?_,
      fun _ _ _ _ hab _ => (above_noFam hab).elim⟩
    obtain ⟨a', ha', hv⟩ := hq
    rw [ha] at ha'; cases ha'
    have hb' := bodyAt_action (by decide) ha'' hp4
    show HeadAt ε (mapEnv (some [0, 3, 4, 5]) (push v ρ)) m s'
    refine ⟨⟨a + 1, by simpa [mapEnv, slot, push] using hv, by omega⟩,
      lowerBound_env (mapEnv_push_slot rfl) (mapEnv_push_slot rfl) hb'.2.1,
      arrAt_congr (mapEnv_push_slot rfl) hb'.2.2.1, arrAt_congr (mapEnv_push_slot rfl) hb'.2.2.2.1⟩
  | 5, _ =>
    -- the exit
    refine ⟨_, rfl, noFam, nulT, .empty, .empty, fun _ _ => True, fun _ => True,
      SafePostExc.value rfl rfl ⟨Footprints.Closed.Holds.refl _ _, trivial⟩, ?_⟩
    exact ⟨fun _ _ _ _ _ _ _ _ => trivial, fun _ v _ _ ⟨_, _, hT⟩ _ => ⟨hT, trivial⟩,
      fun _ _ _ _ hab _ => (above_noFam hab).elim⟩

/-- **The note's loop is safe**, one closed instance of `graph_safe`: from
every state where `0 ≤ from`, `to ≤ |xs|` and `xs`, `out` are arrays of source
values, aliased or not, the loop never gets stuck, returns `null` and raises
nothing. -/
theorem loop_safe (m : Nat) {ρ : Env} {s : IndexedHeap} (hpre : HeadAt ε ρ m s) :
    SafeGraph noFam loopGraph nulT s.n s.W s.h (.at 0 ρ) :=
  graph_safe_at (pre := loopPre ε) (Qres := fun _ => True) (Rres := fun _ => True) (l := 0)
    (loop_checked (ε := ε) m) (loopPre_admin m) hpre

/-- A run of the loop to its end, with budget left, returns `null`. -/
theorem loop_done (m : Nat) {ρ : Env} {s : IndexedHeap} (hpre : HeadAt ε ρ m s) {k : Nat} {h' : Heap} {v : Tm}
    (hrun : Transitions loopGraph k s.h (.at 0 ρ) h' (.done v)) (hk : k < s.n) : v = .nul := by
  obtain ⟨_, -, -, -, -, hT, -⟩ := invocation_done (pre := loopPre ε) (Qres := fun _ => True)
    (Rres := fun _ => True) (l := 0) (loop_checked (ε := ε) m) (loopPre_admin m) hpre hrun hk
  exact hT

/-- No run of the loop with budget left raises. -/
theorem loop_no_raise (m : Nat) {ρ : Env} {s : IndexedHeap} (hpre : HeadAt ε ρ m s) {k : Nat} {h' : Heap}
    {e : Tm} (hrun : Transitions loopGraph k s.h (.at 0 ρ) h' (.raised e)) (hk : k < s.n) : False := by
  obtain ⟨_, -, -, -, -, hΞ, -⟩ := invocation_raised (pre := loopPre ε) (Qres := fun _ => True)
    (Rres := fun _ => True) (l := 0) (loop_checked (ε := ε) m) (loopPre_admin m) hpre hrun hk
  exact hΞ


/-! ## An aliased entry state

The entry assertion is met where `xs` and `out` are one array: a world of two
locations, a store listing one cell and that cell, at every positive budget.
So `loop_safe` covers an aliased run, not only a vacuous one. -/

/-- The world: location 0 a store of source values, location 1 its cell. -/
def aliasWorld (n : Nat) : WorldT n := ofList [res storeF, res srcF]

/-- The heap: the store listing location 1, which holds `0`. -/
def aliasHeap : Heap := [.arr [some 1], .num (bitsOfNat 0)]

/-- The one array, its store field at location 0. -/
def aliasArray : Val := .objAt [(arrayStoreKey, 0)] .absent 2

/-- `from = 0`, `to = 1`, `xs` and `out` the same array. -/
def aliasEnv : Env
  | 0 => .num (bitsOfNat 0)
  | 1 => .num oneBits
  | 2 => aliasArray
  | 3 => aliasArray
  | _ => .undef

theorem storeF_valOnly : ValOnly storeF := fun _ _ _ h => by
  obtain ⟨ls, rfl, -⟩ := h
  rfl

theorem res_ctrAdm {k : Nat} {A : Fam} (hA : Adm A) (hV : ValOnly A) : CtrAdm (res A : Ctr k) :=
  ⟨fun i _ U U' hx w hw => hA.mono i U U' hx w hw, fun i _ U w hw => hV i U w hw⟩

theorem aliasWorld_lookup {n l : Nat} {c : Ctr n} (hl : lookup (aliasWorld n) l = some c) :
    (l = 0 ∧ c = res storeF) ∨ (l = 1 ∧ c = res srcF) := by
  simp only [lookup, aliasWorld, toList_ofList] at hl
  rcases l with _ | _ | l <;> simp at hl
  · exact .inl ⟨rfl, hl.symm⟩
  · exact .inr ⟨rfl, hl.symm⟩

theorem aliasWorld_adm (n : Nat) : WorldAdm (aliasWorld n) := by
  intro l c hl
  rcases aliasWorld_lookup hl with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact res_ctrAdm (listT_adm _) storeF_valOnly
  · exact res_ctrAdm srcF_adm srcF_valOnly

theorem aliasStore (n : Nat) : storeF n (aliasWorld n) (.arr [some 1]) := by
  refine ⟨_, rfl, fun _ _ => by simp [StorePresence, anyTuple], by simp [anyTuple], by decide,
    fun hn => by simp [anyTuple] at hn, fun i A hA => by simp [anyTuple] at hA,
    fun i A l hA => by simp [anyTuple] at hA, ?_⟩
  intro i l _ hl
  rcases i with _ | i <;> simp at hl
  subst hl
  exact ⟨srcF, res srcF, rfl, by simp [lookup, aliasWorld], fun _ _ _ _ => SlotContract.refl _ _⟩

theorem aliasHeap_ok (n : Nat) : HeapOk n (aliasWorld n) aliasHeap := by
  refine ⟨by simp [aliasHeap, aliasWorld], fun l c hl => ?_⟩
  rcases aliasWorld_lookup hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨_, rfl, fun j hj => ?_⟩
    have h := aliasStore j
    have e : trunc j (Nat.le_of_lt hj) (aliasWorld n) = aliasWorld j := by
      simp only [trunc, aliasWorld, toList_ofList, List.map_cons, List.map_nil]
      rfl
    show storeF j _ _
    rw [e]
    exact h
  · exact ⟨_, rfl, fun _ _ => rfl⟩

/-- The aliased entry state at budget `n + 1`. -/
def aliasState (n : Nat) : IndexedHeap :=
  ⟨n + 1, aliasWorld (n + 1), aliasHeap, Nat.zero_lt_succ n, aliasWorld_adm _, aliasHeap_ok _⟩

theorem aliasArray_arrayF (n : Nat) : arrayF n (aliasWorld n) aliasArray := by
  refine ⟨[(arrayStoreKey, 0)], 2, rfl, fun f T hm l hl g hg => ?_, fun f T hm => ?_⟩
  · simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, -⟩ := hm
    simp only [List.lookup] at hg
    split at hg
    · rename_i hb
      exact beq_iff_eq.mp hb
    · cases hg
  · simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨0, res storeF, by simp [List.lookup], by simp [lookup, aliasWorld], fun _ _ _ _ => Iff.rfl⟩

/-- **The entry assertion holds with `xs` and `out` aliased.** -/
theorem alias_entry (m n : Nat) : HeadAt ε aliasEnv m (aliasState n) ∧ aliasEnv 2 = aliasEnv 3 := by
  have zero : SafeIntegers.SafeInt (bitsOfNat 0) 0 := ⟨by decide, .inl ⟨by decide, rfl⟩⟩
  refine ⟨⟨⟨0, HeapKnowledge.intValue_num zero, Int.le_refl _⟩, ?_, aliasArray_arrayF _, aliasArray_arrayF _⟩, rfl⟩
  refine lowerBound_iff.mpr ⟨1, 1, HeapKnowledge.intValue_num oneBits_safe, ?_, Int.le_refl _⟩
  exact HeapKnowledge.lengthOf_of_store (s := 0) (ls := [some 1]) (by show List.lookup arrayStoreKey [(arrayStoreKey, 0)] = some 0; simp [List.lookup])
    rfl (by decide)

/-- The loop is safe from the aliased entry state. -/
theorem alias_loop_safe (m n : Nat) :
    SafeGraph noFam loopGraph nulT (n + 1) (aliasWorld (n + 1)) aliasHeap (.at 0 aliasEnv) :=
  loop_safe (ε := ⟨aliasEnv, aliasHeap⟩) (s := aliasState n) m (alias_entry m n).1

end Verification.TolerantFrames
