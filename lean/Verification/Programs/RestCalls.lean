import Verification.Semantics.Rules

/-!
# Variadic calls

A variadic signature (`restsT`) says only which actual lists a caller may
write, so one value may also meet fixed signatures (`Safety`, call
contracts). What code collecting a rest promises is proved where graph code is
created (`ProgramTyping.restsT_of_graphRest`). Here: eliminating a variadic
signature, allocating a rest store, and spreading actuals.
-/
namespace Verification.RestCalls

/-- A ready variadic call consumes one step, then meets the result contract. -/
theorem call_elim_rest {S : List (Fam × List Fam × ArgFam × Fam)} {s : Fam × List Fam × ArgFam × Fam}
    (hs : s ∈ S) (hR : Adm s.1) (hA : ∀ A ∈ s.2.1, Adm A) (hAv : ∀ A ∈ s.2.1, ValOnly A)
    (hE : Adm s.2.2.1)
    {n : Nat} {W : WorldT n} {f r : Tm} {args extra : List Tm} {heap : Heap}
    (hrv : isVal r = true) (hr : s.1 n W r)
    (hf : restsT Ξ S n W f) (ha : ArgsT s.2.1 n W args) (he : s.2.2.1 n W extra)
    (hev : CallArguments.Values extra)
    (hw : WorldAdm W) (hh : HeapOk n W heap) :
    Safe Ξ s.2.2.2 n W heap (.invoke f r (args ++ extra)) := by
  apply ArgumentContracts.call_safe
    (P := ArgsRest s.2.1 s.2.2.1)
    (Adm.of_transfer (fun ha j hj U hx => ArgsRest_transfer hA hE ha j hj U hx)) hR
    ⟨hf.1, hf.2 s hs⟩ hr hrv ?_ (ArgsRest_of_exact_extra ha he) hw hh
  intro a hm
  rcases List.mem_append.mp hm with hm | hm
  · exact ArgsT_values hAv ha a hm
  · exact hev a hm

/-- Run a subterm in an evaluation context, then continue with its value. -/
theorem ctx_bind {A B : Fam} (C : Tm → Tm)
    (lift : ∀ {h t h' t'}, Step h t h' t' → Step h (C t) h' (C t'))
    (raise : ∀ {t v}, Raises t v → Raises (C t) v) :
    ∀ n W h t, WorldAdm W → HeapOk n W h → Safe Ξ A n W h t →
    (∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
      ∀ h' v, HeapOk j U h' → isVal v = true → A j U v → Safe Ξ B j U h' (C v)) →
    Safe Ξ B n W h (C t) := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hw hh hs hk
    rcases hs with (⟨hv, ht⟩ | hr) | ⟨U, h', t', hx, hu, step, hh', ht'⟩
    · exact hk (n+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw h t hh hv ht
    · exact Or.inl (Or.inr (hr.lift raise))
    · refine Or.inr ⟨U, h', C t', hx, hu, lift step, hh', ih U h' t' hu hh' ht' ?_⟩
      intro j hj V hx' hv h'' v hh'' hval ha
      apply hk j (by omega) V _ hv h'' v hh'' hval ha
      apply WExt_trans _ hx'
      simpa only [trunc_trunc] using WExt_trunc hj hx

/-- **Allocating a rest store.** Actuals meeting a tuple contract at the
current level, as a fresh store, meet it as a writable store. The allocation
step, rather than tuple membership, consumes an approximation level. -/
theorem argument_alloc_safe {T : TupleF} (hT : ∀ i A, positionFam T i = some A → Adm A)
    (hTv : ∀ i A, positionFam T i = some A → ValOnly A)
    {n : Nat} {W : WorldT n} {h : Heap} {vs : List Tm}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hp : ArgumentContracts.Fits T n W vs)
    (hvals : CallArguments.Values vs) :
    Safe Ξ (listT { T with readonly := false }) n W h (.arrLit vs) := by
  obtain ⟨hreq, hbound, hel⟩ := hp
  have hsome : ∀ i, i < vs.length → ∃ A, positionFam T i = some A := by
    intro i hi
    apply Option.isSome_iff_exists.mp
    apply ArgumentContracts.positionFam_isSome
    cases hr : T.rest with
    | none => have := hbound hr; left; omega
    | some _ => right; rfl
  let As := (List.range vs.length).map fun i => (positionFam T i).getD (fun _ _ _ => False)
  have hlen : As.length = vs.length := by simp [As]
  have hAi : ∀ i (hi : i < As.length), positionFam T i = some (As[i]'hi) := by
    intro i hi
    obtain ⟨A, hA⟩ := hsome i (by simpa [hlen] using hi)
    simp [As, hA]
  have hres := arr_alloc_rule_below (Ξ := Ξ) (Q := listT { T with readonly := false }) (As := As)
    (by
      intro A hA
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
      exact hT i _ (hAi i hi))
    (by
      intro A hA
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
      exact hTv i _ (hAi i hi))
    n W h vs hlen hvals hw hh
    (by
      intro p hp j hj
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
      rw [List.getElem_zip] at hpi
      subst hpi
      have hiv : i < vs.length := by simp at hi; omega
      exact (hT i _ (hAi i _)).down_le n j (Nat.le_of_lt hj) W _
        (hel i _ _ (List.getElem?_eq_getElem hiv) (hAi i _)))
    (by
      intro j hj U hx hl
      have := listT_alloc (T := { T with readonly := false }) (As := As) (base := h.length)
        (by simp only [hlen]; exact hreq) (by simp only [hlen]; exact hbound)
        (fun i A hA => by
          obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hA
          exact hAi i hi)
        hl
      rwa [hlen] at this)
  exact hres


/-! ## Spread actuals

A spread actual evaluates to a store, and the call then reads the store's
elements in its place, before any later actual runs. A store family spreads
into `E` when every element it may hold reads at `E`: through its location's
contract one budget down, or as `undefined` at a hole. -/

/-- Reading the elements of a store the heap satisfies yields members of `E`. -/
def Spreads (S E : Fam) : Prop :=
  ∀ n W (h : Heap) v, HeapOk n W h → S n W v →
    ∃ ls vs, v = .arr ls ∧ readElems h ls = some vs ∧
      ∀ e ∈ vs, ∀ (j : Nat) (hj : j < n), E j (trunc j (Nat.le_of_lt hj) W) e

/-- Every location a store names has a contract implying `E`, and a hole is
allowed only where `E` admits `undefined`: then the elements read at `E`. -/
theorem readElems_ok {E : Fam} {n : Nat} {W : WorldT n} {h : Heap} (hh : HeapOk n W h) :
    ∀ ls : List (Option Nat),
      (∀ l, some l ∈ ls → ∃ c : Ctr n, lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → E j U u) →
      (none ∈ ls → ∀ j, j < n → ∀ (U : WorldT j), E j U .undef) →
      ∃ vs, readElems h ls = some vs ∧
        ∀ e ∈ vs, ∀ (j : Nat) (hj : j < n), E j (trunc j (Nat.le_of_lt hj) W) e
  | [], _, _ => ⟨[], rfl, by simp⟩
  | none :: ls, hl, hn => by
    obtain ⟨vs, hr, he⟩ := readElems_ok hh ls (fun l hm => hl l (by simp [hm]))
      (fun hm => hn (by simp [hm]))
    refine ⟨.undef :: vs, by simp [readElems, hr], ?_⟩
    intro e hm j hj
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hn (by simp) j hj _
    · exact he e hm j hj
  | some l :: ls, hl, hn => by
    obtain ⟨vs, hr, he⟩ := readElems_ok hh ls (fun l hm => hl l (by simp [hm]))
      (fun hm => hn (by simp [hm]))
    obtain ⟨c, hc, hag⟩ := hl l (by simp)
    obtain ⟨v, hv, hmem⟩ := hh.2 l c hc
    refine ⟨v :: vs, by simp [readElems, hv, hr], ?_⟩
    intro e hm j hj
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hag j hj _ e (hmem j hj)
    · exact he e hm j hj

/-- A tuple contract spreads into `E` when every position's family implies
`E`, and `E` admits `undefined` if the store may have a hole: at an optional
position or among the rest. -/
theorem listT_spreads {T : TupleF} {E : Fam}
    (hpos : ∀ i A, positionFam T i = some A → FamLe A E)
    (hhole : T.presence = .sparse → ∀ j (U : WorldT j), E j U .undef) :
    Spreads (listT T) E := by
  rintro n W h v hh ⟨ls, rfl, hd, hlen, hbound, hreq, hopt, hrest⟩
  have hsome : ∀ l, some l ∈ ls → ∃ c : Ctr n, lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → E j U u := by
    intro l hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    by_cases h1 : i < T.required.length
    · obtain ⟨A, hA⟩ : ∃ A, T.required[i]? = some A := ⟨_, List.getElem?_eq_getElem h1⟩
      obtain ⟨l', c, hl', hc, hag⟩ := hreq i A hA
      rw [hi] at hl'; cases hl'
      refine ⟨c, hc, fun j hj U u hu => hpos i A (by simp [positionFam, hA]) j U u ((hag j hj U u).1 hu)⟩
    · by_cases h2 : i < T.required.length + T.optional.length
      · obtain ⟨A, hA⟩ : ∃ A, T.optional[i - T.required.length]? = some A :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨c, hc, hag⟩ := hopt (i - T.required.length) A l hA
          (by rw [show T.required.length + (i - T.required.length) = i by omega]; exact hi)
        refine ⟨c, hc, fun j hj U u hu => hpos i A ?_ j U u ((hag j hj U u).1 hu)⟩
        simp [positionFam, List.getElem?_eq_none (show T.required.length ≤ i by omega), hA]
      · obtain ⟨A, c, hA, hc, hag⟩ := hrest i l (by omega) hi
        refine ⟨c, hc, fun j hj U u hu => hpos i A ?_ j U u ((hag j hj U u).1 hu)⟩
        simp [positionFam, List.getElem?_eq_none (show T.required.length ≤ i by omega),
          List.getElem?_eq_none (show T.optional.length ≤ i - T.required.length by omega),
          show T.required.length + T.optional.length ≤ i by omega, hA]
  have hnone : none ∈ ls → ∀ j, j < n → ∀ (U : WorldT j), E j U .undef := by
    intro hm j hj U
    cases hT : T.presence with
    | dense => exact False.elim ((show none ∉ ls by simpa [StorePresence, hT] using hd j hj) hm)
    | sparse => exact hhole hT j U
    | readable =>
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
      have hs : (positionFam T i).isSome = true := by
        apply ArgumentContracts.positionFam_isSome
        cases hr : T.rest with
        | none => have := hbound hr; have := (List.getElem?_eq_some_iff.mp hi).1; left; omega
        | some _ => right; rfl
      obtain ⟨A, hA⟩ := Option.isSome_iff_exists.mp hs
      have ha := hd j hj
      simp only [StorePresence, hT] at ha
      exact hpos i A hA j U .undef (ha i hi A hA U)
  obtain ⟨vs, hr, he⟩ := readElems_ok hh ls hsome hnone
  exact ⟨ls, vs, rfl, hr, he⟩

/-- A step of the actual after a completed prefix is a step of the call. -/
theorem call_lift {h h' : Heap} {f r t t' : Tm} {pre rest : List Tm}
    (hf : isVal f = true) (hr : isVal r = true) (hp : CallArguments.Values pre)
    (s : Step h t h' t') :
    Step h (.invoke f r (pre ++ t :: rest)) h' (.invoke f r (pre ++ t' :: rest)) :=
  (CallArguments.Prepare.args (r := r) (args := pre ++ t :: rest) hf hr
    (CallArguments.keep_prefix hp (.head s))).step

theorem call_raise {f r t v : Tm} {pre rest : List Tm}
    (hf : isVal f = true) (hr : isVal r = true) (hp : CallArguments.Values pre)
    (s : Raises t v) : Raises (.invoke f r (pre ++ t :: rest)) v :=
  .callArg hf hr (prefix_position hp).1 (prefix_position hp).2 s

/-- The term a part is written as: itself, or a spread of it. -/
def partTerm (p : Option Fam × Tm) : Tm :=
  match p.1 with
  | none => p.2
  | some _ => .spread p.2

/-- **Parts in a list context.** In a context `C` over a list of terms that
evaluates its entries left to right (`lift`, `raise`) and replaces a spread
of a ready store by the store's elements once every earlier entry is a value
(`spread`), as an argument list (`Step.callSpread`) and a store literal
(`Step.arrSpread`) do: each part is a plain entry at `E` or a spread of a
store in a family that spreads into `E`; they run left to right, each spread
read as soon as its store is ready, and the continuation receives every
element and entry at `E`. -/
theorem parts_safe {E R : Fam} (hE : Adm E) (hEv : ValOnly E) (C : List Tm → Tm)
    (lift : ∀ {h h' : Heap} {t t' : Tm} {pre rest : List Tm}, CallArguments.Values pre →
      Step h t h' t' → Step h (C (pre ++ t :: rest)) h' (C (pre ++ t' :: rest)))
    (raise : ∀ {t v : Tm} {pre rest : List Tm}, CallArguments.Values pre →
      Raises t v → Raises (C (pre ++ t :: rest)) v)
    (spread : ∀ {h : Heap} {pre rest : List Tm} {ls : List (Option Nat)} {vs : List Tm},
      CallArguments.Values pre → readElems h ls = some vs →
      Step h (C (pre ++ .spread (.arr ls) :: rest)) h (C (pre ++ vs ++ rest))) :
    ∀ (parts : List (Option Fam × Tm)) (n : Nat) (W : WorldT n) (heap : Heap) (pre : List Tm),
      (∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ Spreads S E) →
      WorldAdm W → HeapOk n W heap → CallArguments.Values pre →
      (∀ p ∈ parts, ∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
        ∀ heap, HeapOk j U heap → Safe Ξ (p.1.getD E) j U heap p.2) →
      (∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
        ∀ heap extra, HeapOk j U heap → (∀ e ∈ extra, E j U e) →
          Safe Ξ R j U heap (C (pre ++ extra))) →
      Safe Ξ R n W heap (C (pre ++ parts.map partTerm))
  | [], n, W, heap, pre, _, hw, hh, _, _, hk => by
    simpa using hk n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap [] hh (by simp)
  | (none, a) :: parts, n, W, heap, pre, hS, hw, hh, hp, ht, hk => by
    have ha := ht (none, a) (by simp) n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap hh
    apply ctx_bind (A := E) (fun t => C (pre ++ t :: parts.map partTerm))
      (fun s => lift hp s) (fun s => raise hp s) n W heap a hw hh ha
    intro j hj U hx hu heap' v hh' hv hEv'
    have hrest := parts_safe hE hEv C lift raise spread parts j U heap' (pre ++ [v])
      (fun p hm => hS p (by simp [hm])) hu hh'
      (by intro x hx'; rcases List.mem_append.mp hx' with hx' | hx'
          · exact hp x hx'
          · simp at hx'; subst hx'; exact hv)
      (by
        intro p hm i hi V hy hV heap'' hh''
        apply ht p (by simp [hm]) i (by omega) V _ hV heap'' hh''
        apply WExt_trans _ hy
        simpa only [trunc_trunc] using WExt_trunc hi hx)
      (by
        intro i hi V hy hV heap'' extra hh'' he
        have hw' : WExt (trunc i (by omega) W) V := by
          apply WExt_trans _ hy
          simpa only [trunc_trunc] using WExt_trunc hi hx
        have := hk i (by omega) V hw' hV heap'' (v :: extra) hh'' (by
          intro e hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact hE.mono i _ V hy e (hE.down_le j i hi U e hEv')
          · exact he e hm)
        simpa using this)
    simpa [partTerm] using hrest
  | (some S, s) :: parts, n, W, heap, pre, hS, hw, hh, hp, ht, hk => by
    obtain ⟨hSa, hSs⟩ := hS (some S, s) (by simp) S rfl
    have hs := ht (some S, s) (by simp) n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap hh
    show Safe Ξ R n W heap (C (pre ++ .spread s :: parts.map partTerm))
    apply ctx_bind (A := S) (fun t => C (pre ++ .spread t :: parts.map partTerm))
      (fun s => lift hp (.spreadC s)) (fun s => raise hp (.spreadC s))
      n W heap s hw hh hs
    intro j hj U hx hu heap' v hh' _ hv
    obtain ⟨ls, vs, rfl, hr, he⟩ := hSs j U heap' _ hh' hv
    cases j with
    | zero => trivial
    | succ p =>
      have hvs : CallArguments.Values vs := fun e hm => hEv p _ e (he e hm p (by omega))
      refine Or.inr ⟨trunc p (Nat.le_succ p) U, heap', C (pre ++ vs ++ parts.map partTerm), WExt_refl _,
        WorldAdm_trunc _ hu, spread hp hr, HeapOk_trunc p U heap' hh', ?_⟩
      have hUV : ∀ i (hi : i ≤ p) (X : WorldT i),
          WExt (trunc i hi (trunc p (Nat.le_succ p) U)) X → WExt (trunc i (by omega) W) X := by
        intro i hi X hy
        apply WExt_trans _ hy
        have := WExt_trunc (show i ≤ p + 1 by omega) hx
        simpa only [trunc_trunc] using this
      have hrest := parts_safe hE hEv C lift raise spread parts p _ heap' (pre ++ vs)
        (fun q hm => hS q (by simp [hm])) (WorldAdm_trunc _ hu) (HeapOk_trunc p U heap' hh')
        (by intro x hx'; rcases List.mem_append.mp hx' with hx' | hx'
            · exact hp x hx'
            · exact hvs x hx')
        (by
          intro q hm i hi X hy hX heap'' hh''
          exact ht q (by simp [hm]) i (by omega) X (hUV i hi X hy) hX heap'' hh'')
        (by
          intro i hi X hy hX heap'' extra hh'' hex
          have := hk i (by omega) X (hUV i hi X hy) hX heap'' (vs ++ extra) hh'' (by
            intro e hm
            rcases List.mem_append.mp hm with hm | hm
            · have h0 := he e hm p (by omega)
              exact hE.mono i _ X hy e (hE.down_le p i hi _ e h0)
            · exact hex e hm)
          simpa using this)
      simpa using hrest

/-- **Actuals after the fixed ones**: the parts in an argument list. -/
theorem spread_parts_safe {E R : Fam} (hE : Adm E) (hEv : ValOnly E) {f r : Tm}
    (hf : isVal f = true) (hrv : isVal r = true) :
    ∀ (parts : List (Option Fam × Tm)) (n : Nat) (W : WorldT n) (heap : Heap) (pre : List Tm),
      (∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ Spreads S E) →
      WorldAdm W → HeapOk n W heap → CallArguments.Values pre →
      (∀ p ∈ parts, ∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
        ∀ heap, HeapOk j U heap → Safe Ξ (p.1.getD E) j U heap p.2) →
      (∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
        ∀ heap extra, HeapOk j U heap → (∀ e ∈ extra, E j U e) →
          Safe Ξ R j U heap (.invoke f r (pre ++ extra))) →
      Safe Ξ R n W heap (.invoke f r (pre ++ parts.map partTerm)) :=
  parts_safe hE hEv (fun args => .invoke f r args) (fun hp s => call_lift hf hrv hp s)
    (fun hp s => call_raise hf hrv hp s) (fun hp hr => .callSpread hf hrv rfl hp hr)

/-- **The parts of a store literal**, evaluated as actuals are. -/
theorem store_parts_safe {E R : Fam} (hE : Adm E) (hEv : ValOnly E) :
    ∀ (parts : List (Option Fam × Tm)) (n : Nat) (W : WorldT n) (heap : Heap),
      (∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ Spreads S E) →
      WorldAdm W → HeapOk n W heap →
      (∀ p ∈ parts, ∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
        ∀ heap, HeapOk j U heap → Safe Ξ (p.1.getD E) j U heap p.2) →
      (∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
        ∀ heap extra, HeapOk j U heap → (∀ e ∈ extra, E j U e) →
          Safe Ξ R j U heap (.arrLit extra)) →
      Safe Ξ R n W heap (.arrLit (parts.map partTerm)) := by
  intro parts n W heap hS hw hh ht hk
  have := parts_safe (R := R) hE hEv Tm.arrLit
    (fun hp s => CallArguments.Step.arrArgs (CallArguments.keep_prefix hp (.head s)))
    (fun hp s => .arrArg (prefix_position hp).1 (prefix_position hp).2 s)
    (fun hp hr => .arrSpread rfl hp hr) parts n W heap [] hS hw hh (by simp [CallArguments.Values]) ht
    (by simpa using hk)
  simpa using this

#print axioms argument_alloc_safe
#print axioms call_elim_rest
#print axioms listT_spreads
#print axioms parts_safe
#print axioms spread_parts_safe
#print axioms store_parts_safe

end Verification.RestCalls
