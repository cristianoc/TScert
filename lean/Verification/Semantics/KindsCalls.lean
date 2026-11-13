import Verification.Semantics.KindsContracts
/-!
# Call preservation over kinded worlds

The general interface every native contract and every call is used through,
over the safety predicate with world-indexed postconditions (`SafeW`):

- **execution prefixes** end in well-formed configurations (`SafeW.run`,
  `NativeContract.run` in `KindsContracts`);
- **exits** (`SafeW.exit`): a run of a safe term that ends in a value or a
  throw at positive budget ends under one extension `U` of the truncated
  entry world, where the heap meets `U` in both parts (contracts and roles'
  shapes), the term's references are valid, and the result type and the
  normal postcondition, or the exception family, the thrown value's valid
  references and the exceptional postcondition, hold at that same `U`;
- **sequencing** (`SafeW.bind`): a term safe in an evaluation context
  continues from each normal exit of the hole at the world that exit reached,
  so a callback's allocations, with the roles its own typing chose, are the
  world the native's continuation extends;
- **exception propagation** (`SafeW.bind`, whose context lets the throw out;
  `SafeW.handle`, whose context steps to a handler): a handler is entered at
  the throwing configuration's world and heap, which is well-formed whatever
  the exceptional postcondition states, `True` included (an effect without
  `onThrow`);
- **invocation** (`NativeContract.safe`): a callee meeting the native-contract
  condition makes its invocation safe at its result type and both
  postconditions;
- **erasure** (`SafeW.erase`): world-indexed postconditions implying heap-only
  ones give safety at the heap-only ones lifted, the postconditions the
  active `SafePostExc` states.

The early evidence of the design (location-kinds draft, §9) is proved here:
a callback that allocates and throws into a handler leaves a well-formed
handler entry with no exceptional postcondition (`callback_throw_handled`),
and a callback's allocation followed by a native's write-back is well-formed
under one world extending the callback's (`callback_writeback`).
-/
namespace Verification.Kinds
open Verification

/-! ## Evaluation contexts -/

/-- **A context's references** are those of its hole's contents and those of
the context around the hole. -/
def CtxRefs (C : Tm → Tm) : Prop := ∀ t r, r ∈ refs (C t) ↔ r ∈ refs t ∨ r ∈ refs (C .undef)

theorem CtxRefs.ok {C : Tm → Tm} (hc : CtxRefs C) {k : Nat} {W : WorldT k} {t : Tm}
    (ht : RefsOk W t) (hC : RefsOk W (C .undef)) : RefsOk W (C t) :=
  fun r hr => ((hc t r).mp hr).elim (ht r) (hC r)

/-- A throw leaves every context that lets it out. -/
theorem Thrown.lift {Ξ : Fam} {k : Nat} {W : WorldT k} {t : Tm} {C : Tm → Tm}
    (raise : ∀ {v}, Raises t v → Raises (C t) v) (h : Thrown Ξ k W t) : Thrown Ξ k W (C t) :=
  let ⟨v, hv, hs, hΞ⟩ := h; ⟨v, raise hv, hs, hΞ⟩

/-! ## Sequencing and exception propagation -/

/-- **Sequencing in an evaluation context.** A term safe in the hole of a
context that lets throws out is safe in the context when the context
continues safely from each normal exit of the hole, at the world and heap
that exit reached. A throw out of the hole is a throw of the whole at the
same world and heap, so the exceptional postcondition is the hole's. -/
theorem SafeW.bind {Ξ A B : Fam} {Q Q' : WPost} {R : WExc} (C : Tm → Tm)
    (lift : ∀ {h t h' t'}, Step h t h' t' → Step h (C t) h' (C t'))
    (raise : ∀ {t v}, Raises t v → Raises (C t) v) (hc : CtxRefs C) :
    ∀ (n : Nat) (W : WorldT n) (h : Heap) (t : Tm), WorldAdm W → HeapOk n W h → RefsOk W (C .undef) →
    SafeW Ξ A Q R n W h t →
    (∀ j (hj : j ≤ n) (U : WorldT j), WExt (trunc j hj W) U → WorldAdm U →
      ∀ h' v, HeapOk j U h' → isVal v = true → A j U v → Q j U h' v → SafeW Ξ B Q' R j U h' (C v)) →
    SafeW Ξ B Q' R n W h (C t) := by
  intro n
  induction n with
  | zero => intro W h t _ _ hC hs _; exact hc.ok hs hC
  | succ p ih =>
    intro W h t hw hh hC hs hk
    obtain ⟨hr, hs⟩ := hs
    rcases hs with (⟨hv, ha, hq⟩ | ⟨ht, hR⟩) | ⟨U, h', t', hx, hu, st, hh', hs'⟩
    · exact hk (p + 1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw h t hh hv ha hq
    · exact ⟨hc.ok hr hC, .inl (.inr ⟨ht.lift raise, hR⟩)⟩
    · refine ⟨hc.ok hr hC, .inr ⟨U, h', C t', hx, hu, lift st, hh',
        ih U h' t' hu hh' (RefsOk_mono hx (RefsOk_trunc _ hC)) hs' ?_⟩⟩
      intro j hj V hx' hv h'' v hh'' hval ha hq
      apply hk j (by omega) V _ hv h'' v hh'' hval ha hq
      simpa only [trunc_trunc] using WExt_trans (WExt_trunc hj hx) hx'

/-- **Exception propagation into a handler.** A term safe in the hole of a
context that steps a throw of the hole to its handler `H` is safe in the
context when the context continues from each normal exit of the hole, and
the handler from each exceptional one. The handler is entered at the
throwing configuration's world and heap: the heap meets that world in both
parts and the thrown value's references are valid there, whatever the
hole's exceptional postcondition `R` states, `True` included. -/
theorem SafeW.handle {Ξ Ξ' A B : Fam} {Q Q' : WPost} {R R' : WExc} (C H : Tm → Tm)
    (lift : ∀ {h t h' t'}, Step h t h' t' → Step h (C t) h' (C t'))
    (hcatch : ∀ {h t v}, Raises t v → Step h (C t) h (H v)) (hc : CtxRefs C) :
    ∀ (n : Nat) (W : WorldT n) (h : Heap) (t : Tm), WorldAdm W → HeapOk n W h → RefsOk W (C .undef) →
    SafeW Ξ A Q R n W h t →
    (∀ j (hj : j ≤ n) (U : WorldT j), WExt (trunc j hj W) U → WorldAdm U →
      ∀ h' v, HeapOk j U h' → isVal v = true → A j U v → Q j U h' v → SafeW Ξ' B Q' R' j U h' (C v)) →
    (∀ m (hm : m + 1 ≤ n) (U : WorldT (m + 1)), WExt (trunc (m + 1) hm W) U → WorldAdm U →
      ∀ h' v, HeapOk (m + 1) U h' → Ξ (m + 1) U v → RefsOk U v → R (m + 1) U h' →
        SafeW Ξ' B Q' R' m (trunc m (Nat.le_succ m) U) h' (H v)) →
    SafeW Ξ' B Q' R' n W h (C t) := by
  intro n
  induction n with
  | zero => intro W h t _ _ hC hs _ _; exact hc.ok hs hC
  | succ p ih =>
    intro W h t hw hh hC hs hk hz
    obtain ⟨hr, hs⟩ := hs
    rcases hs with (⟨hv, ha, hq⟩ | ⟨ht, hR⟩) | ⟨U, h', t', hx, hu, st, hh', hs'⟩
    · exact hk (p + 1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw h t hh hv ha hq
    · obtain ⟨v, hrv, hΞ, hvr⟩ := Thrown.refs ht hr
      exact ⟨hc.ok hr hC, .inr ⟨_, h, H v, WExt_refl _, WorldAdm_trunc _ hw, hcatch hrv,
        HeapOk_trunc p W h hh,
        hz p (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw h v hh hΞ hvr hR⟩⟩
    · refine ⟨hc.ok hr hC, .inr ⟨U, h', C t', hx, hu, lift st, hh',
        ih U h' t' hu hh' (RefsOk_mono hx (RefsOk_trunc _ hC)) hs' ?_ ?_⟩⟩
      · intro j hj V hx' hv h'' v hh'' hval ha hq
        apply hk j (by omega) V _ hv h'' v hh'' hval ha hq
        simpa only [trunc_trunc] using WExt_trans (WExt_trunc hj hx) hx'
      · intro m hm V hx' hv h'' v hh'' hΞ hvr hR
        apply hz m (by omega) V _ hv h'' v hh'' hΞ hvr hR
        simpa only [trunc_trunc] using WExt_trans (WExt_trunc hm hx) hx'

/-! ## Exits -/

/-- **Normal and exceptional exits at one world.** A run of a safe term that
ends in a value or a throw with budget left ends under one extension `U` of
the truncated entry world: the heap meets `U` in both parts, the term's
references are valid in `U`, and either the value has the result type and
meets the normal postcondition at `U`, or the thrown value is of the
exception family with valid references and the exceptional postcondition
holds at `U`. Typing, shapes and postconditions read the same world. -/
theorem SafeW.exit {Ξ T : Fam} {Q : WPost} {R : WExc} {k : Nat} {h : Heap} {t : Tm} {h' : Heap}
    {t' : Tm} (hst : HeapObservations.Steps k h t h' t') {n : Nat} {W : WorldT n} (hk : k < n)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hs : SafeW Ξ T Q R n W h t)
    (hend : isVal t' = true ∨ ∃ v, Raises t' v) :
    ∃ (j : Nat) (hj : j + 1 ≤ n) (U : WorldT (j + 1)), j + 1 + k = n ∧ WExt (trunc (j + 1) hj W) U ∧
      WorldAdm U ∧ HeapOk (j + 1) U h' ∧ RefsOk U t' ∧
      ((isVal t' = true ∧ T (j + 1) U t' ∧ Q (j + 1) U h' t') ∨
        (∃ v, Raises t' v ∧ Ξ (j + 1) U v ∧ RefsOk U v ∧ R (j + 1) U h')) := by
  obtain ⟨j, hj, U, hjk, hx, hu, hh, hr, hs'⟩ := hs.run hst (Nat.le_of_lt hk) hadm hok
  cases j with
  | zero => omega
  | succ m =>
    refine ⟨m, hj, U, hjk, hx, hu, hh, hr, ?_⟩
    rcases hs'.2 with (⟨hv, hT, hq⟩ | ⟨ht, hR⟩) | ⟨_, _, _, -, -, st, -, -⟩
    · exact .inl ⟨hv, hT, hq⟩
    · obtain ⟨v, hrv, hΞ, hvr⟩ := Thrown.refs ht hr
      exact .inr ⟨v, hrv, hΞ, hvr, hR⟩
    · rcases hend with hv | ⟨v, hrv⟩
      · exact absurd st (value_no_step hv)
      · exact absurd st (raises_no_step hrv)

/-- **Erasure to heap-only postconditions.** World-indexed postconditions
implying heap-only ones give safety at the heap-only ones lifted, which are
the postconditions `SafePostExc` states of the active worlds. -/
theorem SafeW.erase {Ξ T : Fam} {Q : WPost} {R : WExc} {Q' : Heap → Val → Prop} {R' : Heap → Prop}
    (hQ : ∀ k (W : WorldT k) h v, Q k W h v → Q' h v) (hR : ∀ k (W : WorldT k) h, R k W h → R' h)
    {n : Nat} {W : WorldT n} {h : Heap} {t : Tm} (hs : SafeW Ξ T Q R n W h t) :
    SafeW Ξ T (WPost.lift Q') (WExc.lift R') n W h t :=
  SafeW.mono (Q' := WPost.lift Q') (R' := WExc.lift R') hQ hR hs

/-! ## Invocation -/

theorem refs_invoke {f r : Tm} {args : List Tm} {k : Nat} {W : WorldT k} (hf : RefsOk W f)
    (hr : RefsOk W r) (ha : ∀ a ∈ args, RefsOk W a) : RefsOk W (.invoke f r args) := by
  intro x hx
  simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap] at hx
  rcases hx with (hx | hx) | ⟨a, ha', hx⟩
  · exact hf x hx
  · exact hr x hx
  · exact ha a ha' x hx

/-- **Invocation of a callee meeting the native-contract condition.** From a
well-formed configuration whose callee, receiver and actuals are valid and
meet the input contract at the world one step below, the invocation is safe
at the contract's result type and both its postconditions. -/
theorem NativeContract.safe {Ξ : Fam} {Acc : (j : Nat) → WorldT j → List Tm → Prop} {Rc : Fam}
    {requires : Tm → List Tm → Heap → Prop} {R : Tm → List Tm → Fam}
    {post : Tm → List Tm → Heap → WPost} {excPost : Tm → List Tm → Heap → WExc}
    {n : Nat} {W : WorldT (n + 1)} {v : Val}
    (hc : NativeContract Ξ Acc Rc requires R post excPost (n + 1) W v) (hadm : WorldAdm W)
    {heap : Heap} (hh : HeapOk (n + 1) W heap) (hv : RefsOk W v) {r : Tm} (hrv : isVal r = true)
    (hrc : Rc n (trunc n (Nat.le_succ n) W) r) (hrr : RefsOk W r) {args : List Tm}
    (ha : CallArguments.Values args) (hacc : Acc n (trunc n (Nat.le_succ n) W) args)
    (har : ∀ a ∈ args, RefsOk W a) (hreq : requires r args heap) :
    SafeW Ξ (R r args) (post r args heap) (excPost r args heap) (n + 1) W heap (.invoke v r args) := by
  obtain ⟨result, hi, hs⟩ := hc n (Nat.lt_succ_self n) _ (WExt_refl _) (WorldAdm_trunc _ hadm) heap
    (HeapOk_trunc n W heap hh) (RefsOk_trunc _ hv) r hrv hrc (RefsOk_trunc _ hrr) args ha hacc
    (fun a h => RefsOk_trunc _ (har a h)) hreq
  exact ⟨refs_invoke hv hrr har, .inr ⟨_, heap, result, WExt_refl _, WorldAdm_trunc _ hadm,
    hi.step heap, HeapOk_trunc n W heap hh, hs⟩⟩

/-! ## Forwarding descriptors -/

/-- **The native-contract condition is closed downward**: at a lower budget
and an extension of the world truncated there. -/
theorem NativeContract.down {Ξ : Fam} {Acc : (j : Nat) → WorldT j → List Tm → Prop} {Rc : Fam}
    {requires : Tm → List Tm → Heap → Prop} {R : Tm → List Tm → Fam}
    {post : Tm → List Tm → Heap → WPost} {excPost : Tm → List Tm → Heap → WExc}
    {k : Nat} {W : WorldT k} {v : Val} (hc : NativeContract Ξ Acc Rc requires R post excPost k W v)
    {j : Nat} (hj : j ≤ k) {U : WorldT j} (hx : WExt (trunc j hj W) U) :
    NativeContract Ξ Acc Rc requires R post excPost j U v := by
  intro i hi V hy hu heap hh hv r hrv hrc hrr args ha hacc har hreq
  refine hc i (by omega) V ?_ hu heap hh hv r hrv hrc hrr args ha hacc har hreq
  simpa only [trunc_trunc] using WExt_trans (WExt_trunc (Nat.le_of_lt hi) hx) hy

/-- **A forwarding descriptor meets the native-contract condition when its
target does**, at the saved receiver and the saved prefix before the
actuals, when the target's actuals' contract survives truncation, as an
admissible family's does. Its invocation changes no heap: it calls the target, so every
configuration of the call is one of the target's. The descriptor's call
ignores its own receiver. -/
theorem NativeContract.bound {Ξ : Fam} {Acc : (j : Nat) → WorldT j → List Tm → Prop} {Rc : Fam}
    {requires : Tm → List Tm → Heap → Prop} {R : Tm → List Tm → Fam}
    {post : Tm → List Tm → Heap → WPost} {excPost : Tm → List Tm → Heap → WExc}
    {k : Nat} {W : WorldT k} {target r₀ : Tm} {pre : List Tm} {fs : List (PropKey × Nat)} {oid : Nat}
    (ht : NativeContract Ξ Acc Rc requires R post excPost k W target)
    (hr₀ : isVal r₀ = true) (hrc : ∀ j (U : WorldT j), j < k → Rc j U r₀)
    (hpre : CallArguments.Values pre)
    (hdown : ∀ j (U : WorldT (j + 1)) args, Acc (j + 1) U args → Acc j (trunc j (Nat.le_succ j) U) args) :
    NativeContract Ξ (fun j U args => Acc j U (pre ++ args)) (fun _ _ _ => True)
      (fun _ args heap => requires r₀ (pre ++ args) heap) (fun _ args => R r₀ (pre ++ args))
      (fun _ args heap => post r₀ (pre ++ args) heap) (fun _ args heap => excPost r₀ (pre ++ args) heap)
      k W (.objAt fs (.bound target r₀ pre) oid) := by
  intro j hj U hx hu heap hh hv r hrv _ _ args ha hacc har hreq
  have hrefs : RefsOk U target ∧ RefsOk U r₀ ∧ ∀ a ∈ pre, RefsOk U a := by
    refine ⟨fun x hm => hv x ?_, fun x hm => hv x ?_, fun a hap x hm => hv x ?_⟩ <;>
      simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap]
    · exact .inr (.inl (.inl hm))
    · exact .inr (.inl (.inr hm))
    · exact .inr (.inr ⟨a, hap, hm⟩)
  refine ⟨_, .bound hrv ha, ?_⟩
  have hvals : CallArguments.Values (pre ++ args) := fun a hm =>
    (List.mem_append.mp hm).elim (hpre a) (ha a)
  have hall : ∀ a ∈ pre ++ args, RefsOk U a := fun a hm =>
    (List.mem_append.mp hm).elim (hrefs.2.2 a) (har a)
  cases j with
  | zero => exact refs_invoke hrefs.1 hrefs.2.1 hall
  | succ m =>
    exact NativeContract.safe (ht.down (Nat.le_of_lt hj) hx) hu hh hrefs.1 hr₀
      (hrc m _ (by omega)) hrefs.2.1 hvals (hdown m U _ hacc) hall hreq

/-! ## Early evidence: a callback that allocates and throws into a handler -/

/-- A contract admitting every machine value. -/
def valCtr {k : Nat} : Ctr k := fun _ _ _ v => isVal v = true

theorem valCtr_adm {k : Nat} : CtrAdm (valCtr (k := k)) :=
  ⟨fun _ _ _ _ _ _ h => h, fun _ _ _ _ h => h⟩

/-- The callback `throw { f: v }`: it allocates an object and throws it. -/
def allocThrow (f : PropKey) (v : Tm) : Tm := .throw (.makeAt .absent [f] [v])

/-- The world the callback's allocation extends: the property `f` in F and
the object's identity in I, each with a contract admitting every value. -/
def allocEntries {k : Nat} : List (Role × Ctr k) := objectEntries [.field] [valCtr] valCtr

/-- **The callback is safe with no exceptional postcondition** (an effect
without `onThrow`): from every well-formed configuration with the initializer
a source value valid in the world and `f` an ordinary key, it allocates under
an extension giving `f` the role F, then throws the object, of every
exception family that admits it, at that world. -/
theorem allocThrow_safe {Ξ T : Fam} {Q : WPost} {f : PropKey} {v : Tm} {n : Nat} {W : WorldT (n + 2)}
    {h : Heap} (hadm : WorldAdm W) (hok : HeapOk (n + 2) W h) (hsrc : isSourceVal v = true)
    (hvr : RefsOk W v)
    (hf : f ≠ arrayStoreKey ∧ f ≠ viewElementsKey ∧ f ≠ viewLengthKey)
    (hΞ : ∀ (U : WorldT (n + 1)) u, Ξ (n + 1) U u) :
    SafeW Ξ T Q (fun _ _ _ => True) (n + 2) W h (allocThrow f v) := by
  have hv : isVal v = true := sourceVal_isVal hsrc
  let W₁ := trunc (n + 1) (Nat.le_succ _) W
  let U := appendWs W₁ (allocEntries (k := n + 1))
  have hok₁ : HeapOk (n + 1) W₁ h := HeapOk_trunc (n + 1) W h hok
  have hmake : RefsOk W₁ (.makeAt .absent [f] [v]) := by
    intro r hr; simp only [refs, refsArgs_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hr
    exact RefsOk_trunc _ hvr r hr
  obtain ⟨hsh, hobj⟩ := objectLiteral_shaped (c := .absent) (ns := [f]) (vs := [v]) [valCtr] valCtr
    (by simpa using hok₁.1.1) hok₁.2 rfl rfl hmake (by simpa using hf) (by simpa using hsrc)
  have hokU : HeapOk (n + 1) U (h ++ [v] ++ [.nul]) := by
    have := HeapOk_appendWs (es := allocEntries (k := n + 1)) (vs := [v, .nul]) hok₁
      (WorldAdm_trunc _ hadm) (fun e he => by
        simp only [allocEntries, objectEntries, List.cons_append, List.nil_append, List.zip_cons_cons,
          List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> exact valCtr_adm)
      rfl
      (fun i c u hc hu j hj => by
        match i with
        | 0 => simp [allocEntries, objectEntries] at hc hu; subst hc hu; exact hv
        | 1 => simp [allocEntries, objectEntries] at hc hu; subst hc hu; rfl
        | i + 2 => simp [allocEntries, objectEntries] at hc)
      (fun i r u hr hu => by
        have hl₁ : h.length = (entries W₁).length := by simpa using hok₁.1.1
        have hu' := hsh (h.length + i) r (by rw [hl₁, roleAt_appendWs']; simpa [allocEntries] using hr)
        obtain ⟨u', hu'', hs⟩ := hu'
        rw [List.append_assoc] at hu''
        rw [List.getElem?_append_right (Nat.le_add_right _ _)] at hu''
        simp only [Nat.add_sub_cancel_left] at hu''
        simp only [List.cons_append, List.nil_append] at hu''
        rw [hu''] at hu; cases hu; exact hs)
    simpa [List.append_assoc] using this
  let o : Tm := .objAt (slots h.length [f]) .absent (h.length + 1)
  have hoRefs : RefsOk U o := by simpa [U, allocEntries] using hobj
  refine ⟨fun r hr => hvr r (by simpa [allocThrow, refs, refsArgs_eq] using hr), .inr ⟨U, h ++ [v] ++ [.nul],
    .throw o, WExt_appendWs _ _, WorldAdm_appendWs (WorldAdm_trunc _ hadm) ?_, ?_, hokU, ?_⟩⟩
  · intro e he
    simp only [allocEntries, objectEntries, List.cons_append, List.nil_append, List.zip_cons_cons,
      List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> exact valCtr_adm
  · exact .throwC (.makeFields (by simpa using hv) rfl)
  · exact ⟨hoRefs, .inl (.inr ⟨⟨o, Raises.throwV (v := o) rfl rfl, trivial, hΞ U o⟩, trivial⟩)⟩

/-- **A callback that allocates and throws into a handler leaves a
well-formed handler entry, with no exceptional postcondition.** Run in a
graph node with a handler, the callback of `allocThrow_safe` takes two steps
to the handler's entry with the thrown object bound; that configuration
meets one extension of the truncated entry world in both parts (contracts
and roles' shapes, the allocated property in F and the identity in I), and
its references, the thrown object's among them, are valid there. -/
theorem callback_throw_handled {f : PropKey} {v : Tm} {n : Nat} {W : WorldT (n + 2)} {h : Heap}
    {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {L : List Tm}
    {d : Tm} {k : ControlFlow.Continuation} {l : ControlFlow.Target}
    (hadm : WorldAdm W) (hok : HeapOk (n + 2) W h) (hsrc : isSourceVal v = true)
    (hf : f ≠ arrayStoreKey ∧ f ≠ viewElementsKey ∧ f ≠ viewLengthKey)
    (hr : RefsOk W (.frame E K (allocThrow f v) L d k (some l))) :
    ∃ (h' : Heap) (t' : Tm) (U : WorldT n),
      HeapObservations.Steps 2 h (.frame E K (allocThrow f v) L d k (some l)) h' t' ∧
      WExt (trunc n (by omega) W) U ∧ WorldAdm U ∧ HeapOk n U h' ∧ RefsOk U t' := by
  have hvr : RefsOk W v := fun r hm => hr r (by
    simp only [refs, refsArgs_eq, allocThrow, List.mem_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact .inl (.inl (.inr hm)))
  have hs := allocThrow_safe (Ξ := fun _ _ _ => True) (T := fun _ _ _ => True) (Q := fun _ _ _ _ => True)
    hadm hok hsrc hvr hf (fun _ _ => trivial)
  have hv : isVal v = true := sourceVal_isVal hsrc
  let o : Tm := .objAt (slots h.length [f]) .absent (h.length + 1)
  have st₀ : Step h (allocThrow f v) (h ++ [v] ++ [.nul]) (.throw o) :=
    .throwC (.makeFields (by simpa using hv) rfl)
  have hro : Raises (.throw o) o := Raises.throwV (v := o) rfl rfl
  obtain ⟨-, (⟨hv', -⟩ | ⟨⟨_, hrv, -⟩, -⟩) | ⟨U, h₁, t₁, hx, hu, st, hh₁, hs₁⟩⟩ := hs
  · simp [allocThrow, isVal] at hv'
  · exact absurd st₀ (raises_no_step hrv)
  obtain ⟨rfl, rfl⟩ := Step_det st st₀
  have ht₁ : RefsOk U (.throw o) := hs₁.refs
  have hrefC : RefsOk U (.frame E K .undef L d k (some l)) := by
    refine RefsOk_mono hx (RefsOk_trunc _ fun r hm => hr r ?_)
    simp only [refs, refsArgs_eq, List.mem_append] at hm ⊢
    rcases hm with ((hm | hm) | hm) | hm
    · exact .inl (.inl (.inl hm))
    · simp at hm
    · exact .inl (.inr hm)
    · exact .inr hm
  have hCt : RefsOk U (.frame E K (.throw o) L d k (some l)) := by
    intro r hm
    simp only [refs, refsArgs_eq, List.mem_append] at hm
    rcases hm with ((hm | hm) | hm) | hm
    · exact hrefC r (by simp only [refs, refsArgs_eq, List.mem_append]; exact .inl (.inl (.inl hm)))
    · exact ht₁ r (by simpa [refs] using hm)
    · exact hrefC r (by simp only [refs, refsArgs_eq, List.mem_append]; exact .inl (.inr hm))
    · exact hrefC r (by simp only [refs, refsArgs_eq, List.mem_append]; exact .inr hm)
  have hcatch := Step.frameHandle (h := h ++ [v] ++ [.nul]) (E := E) (K := K) (L := L) (d := d) (k := k)
    (l := l) hro
  refine ⟨h ++ [v] ++ [.nul], _, trunc n (Nat.le_succ n) U, .next (.frameC st₀) (.next hcatch .refl), ?_,
    WorldAdm_trunc _ hu, HeapOk_trunc n U _ hh₁, ?_⟩
  · simpa only [trunc_trunc] using WExt_trunc (Nat.le_succ n) hx
  · exact RefsOk_trunc _ (step_refs hcatch (by simpa using hh₁.1.1) hh₁.2 hCt)

/-! ## Early evidence: a callback's allocation, then a native's write-back -/

/-- **A callback's allocation followed by a native's write-back is
well-formed under one world extending the callback's.** The callback ran to
a value at the world `U` its own typing chose (`SafeW.exit`), its
allocations with whatever roles that typing gave. The native then appends
fresh element cells holding source values valid in `U`, each meeting its
contract, and writes an ordinary array's store `s` to a store listing cells
of the old store or fresh ones, a store `s`'s contract admits. The result
meets the one world `U'` that extends `U` by the fresh cells as E, in both
parts of satisfaction; the callback's result keeps every property its type
gives at `U` that extension keeps. -/
theorem callback_writeback {n : Nat} {U : WorldT n} {h : Heap} (hok : HeapOk n U h) (hadm : WorldAdm U)
    {cs : List (Ctr n)} {vs : List Val} (hlen : cs.length = vs.length)
    (hcadm : ∀ c ∈ cs, CtrAdm c)
    (hvs : ∀ (i : Nat) (c : Ctr n) (u : Val), cs[i]? = some c → vs[i]? = some u →
      isSourceVal u = true ∧ RefsOk U u ∧ ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) U) u)
    {s : Nat} {orig ls' : List (Option Nat)} (hs : roleAt U s = some (.store .array))
    (horig : h[s]? = some (.arr orig))
    (hcells : ∀ c, some c ∈ ls' → some c ∈ orig ∨ (h.length ≤ c ∧ c < h.length + vs.length))
    (hctr : ∀ c, lookup (appendWs U (cs.map fun c => (Role.elem, c))) s = some c →
      ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) (appendWs U (cs.map fun c => (Role.elem, c))))
        (.arr ls')) :
    WExt U (appendWs U (cs.map fun c => (Role.elem, c))) ∧ WorldAdm (appendWs U (cs.map fun c => (Role.elem, c))) ∧
      HeapOk n (appendWs U (cs.map fun c => (Role.elem, c))) ((h ++ vs).set s (.arr ls')) := by
  let es := cs.map fun c => (Role.elem, c)
  let U' := appendWs U es
  have hx : WExt U U' := WExt_appendWs U es
  have hlenU : h.length = (entries U).length := by simpa using hok.1.1
  have hadm' : WorldAdm U' := WorldAdm_appendWs hadm (fun e he => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he; exact hcadm c hc)
  have hok' : HeapOk n U' (h ++ vs) := HeapOk_appendWs hok hadm (fun e he => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he; exact hcadm c hc) (by simp [es, hlen])
    (fun i c u hc hu j hj => by
      simp only [es, List.map_map, Function.comp_def, List.map_id'] at hc
      exact (hvs i c u hc hu).2.2 j hj)
    (fun i r u hr hu => by
      simp only [es, List.map_map, Function.comp_def, List.getElem?_map] at hr
      have hlt : i < cs.length := by
        rcases hci : cs[i]? with _ | c <;> simp [hci] at hr; exact (List.getElem?_eq_some_iff.mp hci).1
      obtain ⟨c, hc⟩ : ∃ c, cs[i]? = some c := ⟨cs[i], List.getElem?_eq_getElem hlt⟩
      rw [hc] at hr; cases hr
      obtain ⟨hsrc, hur, -⟩ := hvs i c u hc hu
      exact ⟨by simpa [Cat] using hsrc, RefsOk_mono hx hur⟩)
  have hsU' : roleAt U' s = some (.store .array) := WExt_roleAt hx hs
  obtain ⟨c, hc⟩ : ∃ c, lookup U' s = some c := by
    obtain ⟨u, hu, -⟩ := hok'.2 s _ hsU'
    have hlt : s < (h ++ vs).length := (List.getElem?_eq_some_iff.mp hu).1
    have hl : (h ++ vs).length = (toList U').length := hok'.1.1
    exact ⟨(toList U')[s]'(by omega), List.getElem?_eq_getElem _⟩
  refine ⟨hx, hadm', write_sound n U' (h ++ vs) s c _ _ hok' hc hsU' (hctr c hc) ⟨⟨ls', rfl⟩, ?_⟩⟩
  refine RefsOk_arr_iff.mpr fun l hl => ?_
  rcases hcells l hl with ho | ⟨h1, h2⟩
  · have := hok.store_cells horig ho
    exact WExt_roleAt hx this.1
  · obtain ⟨i, rfl⟩ : ∃ i, l = h.length + i := ⟨l - h.length, by omega⟩
    rw [hlenU, roleAt_appendWs']
    simp [es, hlen ▸ (show i < vs.length by omega)]

/-! ## Footprint relations alone

A footprint bounds where a call may change the heap. The relations below
admit a transition from a well-formed heap to a heap no extension of its
world satisfies, so none of them is evidence of the native-contract
condition; a contract meeting the condition states its structural part
through safety (`SafeW`). -/

/-- **A relation that lets an old location's contents leave its role's
category does not respect kinds.** -/
theorem not_respects_of_breaks {Rel : Heap → Heap → Prop} {k : Nat} {W : WorldT k} {h h' : Heap}
    (hlen : h.length = (entries W).length) (hsh : Shaped W h) (hr : Rel h h') {l : Nat} {r : Role}
    (hl : roleAt W l = some r) (hbad : ∀ u, h'[l]? = some u → ¬ Cat r u) : ¬ RespectsKinds Rel := by
  intro H
  obtain ⟨W', hx, -, hsh'⟩ := H k W h h' hlen hsh hr
  obtain ⟨u, hu, hc, -⟩ := hsh' l r (WExt_roleAt hx hl)
  exact hbad u hu hc

/-- The world of one property location. -/
def fieldWorld : WorldT 0 := ofEntries [(.field, fun _ hj _ _ => absurd hj (Nat.not_lt_zero _))]

theorem fieldWorld_shaped : Shaped fieldWorld [.str "a"] := by
  intro l r hr
  have hl : l = 0 := by have := roleAt_lt hr; simp [fieldWorld] at this; omega
  subst hl
  have hW : roleAt fieldWorld 0 = some .field := by simp [fieldWorld, roleAt, roles]
  rw [hW] at hr; cases hr
  exact ⟨_, rfl, rfl, fun _ h => by simp [refs] at h⟩

/-- **A change confined to one location, arbitrary there, does not respect
kinds**: the relation a receiver's store (`receiverStore`), a receiver's own
locations (`receiverOwn`) or an argument store region bounds a call by at
the location it names. -/
theorem confined_not_respects :
    ¬ RespectsKinds (fun h h' => h'.length = h.length ∧ ∀ l, l ≠ 0 → h'[l]? = h[l]?) :=
  not_respects_of_breaks (W := fieldWorld) (h := [.str "a"]) (h' := [.arr []]) (by simp [fieldWorld])
    fieldWorld_shaped ⟨rfl, fun l hl => by rcases l with _ | l <;> simp_all⟩
    (l := 0) (r := .field) (by simp [fieldWorld, roleAt, roles])
    (fun u hu => by simp at hu; subst hu; simp [Cat, isSourceVal])

/-- **An unrestricted exceptional postcondition does not respect kinds**:
an effect without `onThrow` states nothing of the heap a throw leaves. -/
theorem unrestricted_not_respects : ¬ RespectsKinds (fun _ _ => True) := fun H =>
  confined_not_respects fun k W h h' hlen hsh _ => H k W h h' hlen hsh trivial

/-- **Allocation alone does not respect kinds**: a relation admitting any
heap the old one is a prefix of, whatever the fresh locations hold
(`fresh`, `freshObject`), admits a fresh store listing a location of no
heap. -/
theorem allocation_not_respects : ¬ RespectsKinds (fun h h' => h.IsPrefix h') := by
  intro H
  let W : WorldT 0 := ofEntries []
  obtain ⟨W', -, hlen, hsh⟩ := H 0 W [] [.arr [some 5]] (by simp [W]) (fun l r hr => by
    have := roleAt_lt hr; simp [W] at this) (List.nil_prefix)
  have hlen' : (entries W').length = 1 := by simpa using hlen.symm
  obtain ⟨r, hr⟩ := roleAt_some (W := W') (l := 0) (by omega)
  obtain ⟨u, hu, hc, href⟩ := hsh 0 r hr
  simp at hu; subst hu
  cases r with
  | store f =>
    have := roleAt_lt (RefsOk_arr_iff.mp href 5 (by simp))
    omega
  | field | cell | elem => simp [Cat, isSourceVal] at hc
  | identity => simp [Cat] at hc

end Verification.Kinds
