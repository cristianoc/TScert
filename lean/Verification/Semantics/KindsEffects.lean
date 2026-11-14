import Verification.Semantics.KindsCalls
/-!
# The gate: a callback's allocation, then a write meeting two signatures

The active call contracts (`CallEffects.PromiseWith`,
`CallEffects.ConstructPromise`) state a signature's postconditions over
kinded worlds: the heap postcondition and the view write from the call's
entry world and heap, both at the exit world (`CallEffects.Effect.postW`).
Here they compose with a callback's allocation at one successor world.

- **The gate** (`gate_write`, `gate_handled`): a callback allocates an
  object, then a value meeting two effectful signatures performs a view
  write. Its every normal exit, and its every throw entering a handler, is
  at one world where the allocated object's property capability holds, the
  heap meets the world in both parts (contracts and roles' shapes), and the
  call's postconditions of both signatures hold (`PromiseWith.combine`,
  `Effect.postW_meet`).
-/
namespace Verification.Kinds
open Verification HeapObservations

/-! ## The gate: a callback's allocation, then a write meeting two signatures -/

/-- The callback of the gate, `{ f: x }`. -/
def literal (f : PropKey) (x : Tm) : Tm := .makeAt .absent [f] [x]

/-- **The callback allocates under a property capability.** From a
well-formed configuration, `{ f: x }` (an ordinary key `f`, a source value
`x` of the admissible contents type `A`) steps once, to the object, at the
world extended by the property in F with the contract of `A` and the identity
in I; there the field capability of `f` at `A` holds of the object. -/
theorem literal_safe {Ξ T : Fam} {R : WExc} {f : PropKey} {x : Tm} {A : Fam} {n : Nat}
    {W : WorldT (n + 2)} {h : Heap} (hadm : WorldAdm W) (hok : HeapOk (n + 2) W h)
    (hsrc : isSourceVal x = true) (hxr : RefsOk W x)
    (hf : f ≠ arrayStoreKey ∧ f ≠ viewElementsKey ∧ f ≠ viewLengthKey)
    (hA : CtrAdm (res A : Ctr (n + 1))) 
    (hxA : ∀ j (hj : j < n + 1), A j (trunc j (Nat.le_of_lt hj) (trunc (n + 1) (Nat.le_succ _) W)) x)
    (hT : ∀ (U : WorldT (n + 1)) u, T (n + 1) U u) :
    SafePostExcW Ξ T (fun _ U h' v => v = .objAt (slots h.length [f]) .absent (h.length + 1) ∧ RefsOk U v ∧
      h.IsPrefix h' ∧ (Capability.field f A).Holds U (slots h.length [f])) R (n + 2) W h (literal f x) := by
  have hv : isVal x = true := sourceVal_isVal hsrc
  let W₁ := trunc (n + 1) (Nat.le_succ _) W
  let es : List (Role × Ctr (n + 1)) := objectEntries [.field] [res A]
  let U := appendWs W₁ es
  have hok₁ : HeapOk (n + 1) W₁ h := HeapOk_trunc (n + 1) W h hok
  have hmake : RefsOk W₁ (.makeAt .absent [f] [x]) := by
    intro r hr; simp only [refs, refsArgs_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hr
    exact RefsOk_trunc _ hxr r hr
  obtain ⟨hsh, hobj⟩ := objectLiteral_shaped (c := .absent) (ns := [f]) (vs := [x]) [res A]
    (by simpa using hok₁.1.1) hok₁.2 rfl rfl hmake (by simpa using hf) (by simpa using hsrc)
  have hadmE : ∀ e ∈ es, CtrAdm e.2 := by
    intro e he
    simp only [es, objectEntries, List.cons_append, List.nil_append, List.zip_cons_cons,
      List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hA
    · exact idCtr_adm
  have hokU : HeapOk (n + 1) U (h ++ [x] ++ [.nul]) := by
    have := HeapOk_appendWs (es := es) (vs := [x, .nul]) hok₁ (WorldAdm_trunc _ hadm) hadmE rfl
      (fun i c u hc hu j hj => by
        match i with
        | 0 => simp [es, objectEntries] at hc hu; subst hc hu; exact hxA j hj
        | 1 => simp [es, objectEntries] at hc hu; subst hc hu; rfl
        | i + 2 => simp [es, objectEntries] at hc)
      (fun i r u hr hu => by
        have hl₁ : h.length = (entries W₁).length := by simpa using hok₁.1.1
        have hu' := hsh (h.length + i) r (by rw [hl₁, roleAt_appendWs']; simpa [es] using hr)
        obtain ⟨u', hu'', hs⟩ := hu'
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _)] at hu''
        simp only [Nat.add_sub_cancel_left, List.cons_append, List.nil_append] at hu''
        rw [hu''] at hu; cases hu; exact hs)
    simpa [List.append_assoc] using this
  let o : Tm := .objAt (slots h.length [f]) .absent (h.length + 1)
  have hoRefs : RefsOk U o := by simpa [U, es] using hobj
  have hcap : (Capability.field f A).Holds U (slots h.length [f]) := by
    have hl₁ : h.length = (entries W₁).length := by simpa using hok₁.1.1
    rw [hl₁]
    exact Capability.holds_alloc W₁ (ns := [f]) (rs := [.field]) (As := [A])  (by simp) rfl rfl
      (i := 0) (by simp) rfl ⟨rfl, rfl⟩
  refine ⟨fun r hr => hxr r (by simpa [literal, refs, refsArgs_eq] using hr), .inr ⟨U, h ++ [x] ++ [.nul],
    o, WExt_appendWs _ _, WorldAdm_appendWs (WorldAdm_trunc _ hadm) hadmE,
    .makeFields (by simpa using hv) rfl, hokU, ?_⟩⟩
  exact ⟨hoRefs, .inl (.inl ⟨rfl, hT U o, rfl, hoRefs, ⟨[x, .nul], by simp⟩, hcap⟩)⟩

/-- The postcondition of the gate's normal exits: at the exit world, the
callback's object has its property capability, and the call's
postconditions of both signatures hold from the call's entry. -/
def gatePost (a b : CallEffects.Effect) (r : Tm) (args : List Tm) (cap : Capability)
    (fs : List (PropKey × Nat)) : WPost :=
  fun k W' h' v => (∃ (j : Nat) (U : WorldT j) (h₁ : Heap), a.postW r args U h₁ k W' h' v ∧
    b.post r args h₁ h' v) ∧ cap.Holds W' fs

/-- The postcondition of the gate's exceptional exits: at the throwing
world, the callback's object has its property capability, and the meet's
exceptional postcondition holds of the call (`Effect.excPost_meet`: the
footprint of both signatures where both state `onThrow`). -/
def gateExc (a b : CallEffects.Effect) (r : Tm) (args : List Tm) (cap : Capability)
    (fs : List (PropKey × Nat)) : WExc :=
  fun _ W' h' => (∃ (h₁ : Heap), (a.meet b).excPost r args h₁ h') ∧ cap.Holds W' fs

/-- **The gate.** A callback allocates `{ f: x }`; then a value `g` meeting
two signatures `a` and `b` with the same result meaning
(`Effect.sameResult`), each a promise over kinded worlds, is called with a
view write among its effects. The whole, `let o = { f: x } in g(r, args)`,
is safe at one world per exit: on a normal return, the exit world gives the
callback's object its field capability, the heap meets that world in both
parts (`SafePostExcW.exit`), and both signatures' postconditions hold of the call,
the first's view write from the call's entry world; on a throw, the same
with both exceptional postconditions. -/
theorem gate_write {Ξ : Fam} {a b : CallEffects.Effect} {Acc : (j : Nat) → WorldT j → List Tm → Prop}
    {Rc : Fam} {B C D : Fam} {f : PropKey} {x g r : Tm} {args : List Tm} {A : Fam}
    {n : Nat} {W : WorldT (n + 2)} {h : Heap}
    (hs : a.sameResult b = true) (ha : CallEffects.PromiseWith Ξ a Acc Rc B (n + 2) W g)
    (hb : CallEffects.PromiseWith Ξ b Acc Rc C (n + 2) W g)
    (hcross : ∀ j, j < n + 2 → CrossCompatUpTo j B C D)
    (hadm : WorldAdm W) (hok : HeapOk (n + 2) W h) (hsrc : isSourceVal x = true)
    (hf : f ≠ arrayStoreKey ∧ f ≠ viewElementsKey ∧ f ≠ viewLengthKey)
    (hA : CtrAdm (res A : Ctr (n + 1))) 
    (hxA : ∀ j (hj : j < n + 1), A j (trunc j (Nat.le_of_lt hj) (trunc (n + 1) (Nat.le_succ _) W)) x)
    (hrefs : RefsOk W (.letE (literal f x) (.invoke g r args)))
    (hscope : Scoped 0 (.invoke g r args)) (hrv : isVal r = true) (hargs : CallArguments.Values args)
    (hrc : ∀ j (U : WorldT j), Rc j U r) (hacc : ∀ j (U : WorldT j), Acc j U args)
    (hreq : ∀ h', h.IsPrefix h' → a.Requires r args h') :
    SafePostExcW Ξ (fun _ _ _ => True) (gatePost a b r args (Capability.field f A) (slots h.length [f]))
      (gateExc a b r args (Capability.field f A) (slots h.length [f])) (n + 2) W h
      (.letE (literal f x) (.invoke g r args)) := by
  let fs := slots h.length [f]
  let cap := Capability.field f A
  let body : Tm := .invoke g r args
  have hcomb := CallEffects.PromiseWith.combine (D := D) hs ha hb hcross
  have hbodyRefs : RefsOk W body := fun y hy => hrefs y
    (show y ∈ refs (literal f x) ++ refs body from List.mem_append.mpr (.inr hy))
  have hxr : RefsOk W x := fun y hy => hrefs y (by
    simp only [refs, literal, refsArgs_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append]
    exact .inl hy)
  have hctx : CtxRefs (fun t => Tm.letE t body) := fun t y => by simp [refs]
  have hlit := literal_safe (Ξ := Ξ) (T := fun _ _ _ => True)
    (R := gateExc a b r args cap fs) hadm hok hsrc hxr hf hA hxA (fun _ _ => trivial)
  refine SafePostExcW.bind (fun t => Tm.letE t body) (fun st => .letC st) (fun hr => .letC hr) hctx
    (n + 2) W h (literal f x) hadm hok
    (fun y hy => (List.mem_append.mp (show y ∈ refs .undef ++ refs body from hy)).elim
      (fun h => by simp [refs] at h) (hbodyRefs y)) hlit ?_
  rintro j hj U hx hu h' v hh' hval - ⟨-, hvU, hpre, hcap⟩
  have hsub : subst 0 v body = body := subst_above hscope (Nat.le_refl 0) v
  have hbodyU : RefsOk U body := RefsOk_mono hx (RefsOk_trunc _ hbodyRefs)
  have hletU : RefsOk U (.letE v body) := fun y hy => by
    simp only [refs, List.mem_append] at hy
    exact hy.elim (hvU y) (hbodyU y)
  cases j with
  | zero => exact hletU
  | succ m =>
    refine ⟨hletU, .inr ⟨trunc m (Nat.le_succ m) U, h', body, WExt_refl _, WorldAdm_trunc _ hu,
      by simpa [hsub] using (Step.letV (h := h') (b := body) hval), HeapOk_trunc m U h' hh', ?_⟩⟩
    cases m with
    | zero => exact RefsOk_trunc _ hbodyU
    | succ p =>
      let V := trunc (p + 1) (Nat.le_succ (p + 1)) U
      have hxV : WExt (trunc (p + 1) (by omega) W) V := by
        have := WExt_trunc (Nat.le_succ (p + 1)) hx
        rwa [trunc_trunc] at this
      have hVb : RefsOk V body := RefsOk_trunc _ hbodyU
      have hg : RefsOk V g := fun y hy => hVb y (by simp [body, refs, hy])
      have hr : RefsOk V r := fun y hy => hVb y (by simp [body, refs, hy])
      have hargsr : ∀ a ∈ args, RefsOk V a := fun a ha y hy =>
        hVb y (by simp only [body, refs, refsArgs_eq, List.mem_append, List.mem_flatMap]; exact .inr ⟨a, ha, hy⟩)
      have hcall := CallEffects.NativeContract.safe (CallEffects.NativeContract.down hcomb (by omega) hxV)
        (WorldAdm_trunc _ hu) (HeapOk_trunc (p + 1) U h' hh') hrv (hrc _ _) hargs (hacc _ _) (hreq h' hpre)
        (RefsOk_invoke.mpr ⟨hg, hr, hargsr⟩)
      have hw := SafePostExcW.world (P := fun k W' => cap.Holds W' fs) (fun _ _ _ hx' hp => hp.mono hx')
        (fun _ _ hj' _ hp => hp.trunc hj') (hcap.trunc _) hcall
      refine SafePostExcW.consequence_below' (fun _ _ _ _ hξ => hξ) (fun _ _ _ _ _ => trivial) ?_ ?_ hw
      · intro _ _ W' h'' val ⟨hp, hc⟩
        obtain ⟨hpa, hpb⟩ := (CallEffects.Effect.postW_meet hs r args _ h' _ W' h'' val).mp hp
        exact ⟨⟨p, _, h', hpa, hpb⟩, hc⟩
      · intro _ _ W' h'' ⟨hp, hc⟩
        exact ⟨⟨h', hp⟩, hc⟩

/-- **The gate's throw-to-handler variant.** Run in a graph node with a
handler, the gate's term is safe when the node continues from each normal
exit and the handler from each throw: the handler is entered at the throwing
configuration's world and heap, where the heap meets the world in both
parts, the thrown value is of the exception family with valid references,
the callback's object has its field capability, and the call's exceptional
postcondition holds (`SafePostExcW.handle`). -/
theorem gate_handled {Ξ Ξ' B' : Fam} {Q' : WPost} {R' : WExc} {a b : CallEffects.Effect}
    {Acc : (j : Nat) → WorldT j → List Tm → Prop}
    {Rc : Fam} {B C D : Fam} {f : PropKey} {x g r : Tm} {args : List Tm} {A : Fam}
    {n : Nat} {W : WorldT (n + 2)} {h : Heap}
    {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {L : List Tm}
    {d : Tm} {k : ControlFlow.Continuation} {l : ControlFlow.Target}
    (hs : a.sameResult b = true) (ha : CallEffects.PromiseWith Ξ a Acc Rc B (n + 2) W g)
    (hb : CallEffects.PromiseWith Ξ b Acc Rc C (n + 2) W g)
    (hcross : ∀ j, j < n + 2 → CrossCompatUpTo j B C D)
    (hadm : WorldAdm W) (hok : HeapOk (n + 2) W h) (hsrc : isSourceVal x = true)
    (hf : f ≠ arrayStoreKey ∧ f ≠ viewElementsKey ∧ f ≠ viewLengthKey)
    (hA : CtrAdm (res A : Ctr (n + 1))) 
    (hxA : ∀ j (hj : j < n + 1), A j (trunc j (Nat.le_of_lt hj) (trunc (n + 1) (Nat.le_succ _) W)) x)
    (hrefs : RefsOk W (.frame E K (.letE (literal f x) (.invoke g r args)) L d k (some l)))
    (hscope : Scoped 0 (.invoke g r args)) (hrv : isVal r = true) (hargs : CallArguments.Values args)
    (hrc : ∀ j (U : WorldT j), Rc j U r) (hacc : ∀ j (U : WorldT j), Acc j U args)
    (hreq : ∀ h', h.IsPrefix h' → a.Requires r args h')
    (hnext : ∀ j (hj : j ≤ n + 2) (U : WorldT j), WExt (trunc j hj W) U → WorldAdm U →
      ∀ h' v, HeapOk j U h' → isVal v = true →
        gatePost a b r args (Capability.field f A) (slots h.length [f]) j U h' v →
        SafePostExcW Ξ' B' Q' R' j U h' (.frame E K v L d k (some l)))
    (hhandler : ∀ m (hm : m + 1 ≤ n + 2) (U : WorldT (m + 1)), WExt (trunc (m + 1) hm W) U → WorldAdm U →
      ∀ h' v, HeapOk (m + 1) U h' → Ξ (m + 1) U v → RefsOk U v →
        gateExc a b r args (Capability.field f A) (slots h.length [f]) (m + 1) U h' →
        SafePostExcW Ξ' B' Q' R' m (trunc m (Nat.le_succ m) U) h'
          (.goto E K l.label (envMap l.mapping (v :: L) d).1 (envMap l.mapping (v :: L) d).2)) :
    SafePostExcW Ξ' B' Q' R' (n + 2) W h (.frame E K (.letE (literal f x) (.invoke g r args)) L d k (some l)) := by
  have hctx : CtxRefs (fun t => Tm.frame E K t L d k (some l)) := fun t y => by
    show y ∈ refsArgs E ++ refs t ++ refsArgs L ++ refs d ↔
      y ∈ refs t ∨ y ∈ refsArgs E ++ refs .undef ++ refsArgs L ++ refs d
    simp only [List.mem_append, refs, List.not_mem_nil, or_false]
    constructor
    · rintro (((h | h) | h) | h)
      · exact .inr (.inl (.inl h))
      · exact .inl h
      · exact .inr (.inl (.inr h))
      · exact .inr (.inr h)
    · rintro (h | ((h | h) | h))
      · exact .inl (.inl (.inr h))
      · exact .inl (.inl (.inl h))
      · exact .inl (.inr h)
      · exact .inr h
  have hinner : RefsOk W (.letE (literal f x) (.invoke g r args)) := fun y hy =>
    hrefs y ((hctx _ y).mpr (.inl hy))
  have hC : RefsOk W (.frame E K .undef L d k (some l)) := fun y hy => by
    rcases (hctx .undef y).mp hy with h | h
    · simp [refs] at h
    · exact hrefs y ((hctx _ y).mpr (.inr h))
  have hgate := gate_write (D := D) hs ha hb hcross hadm hok hsrc hf hA hxA hinner hscope hrv hargs
    hrc hacc hreq
  exact SafePostExcW.handle (fun t => Tm.frame E K t L d k (some l))
    (fun t => .goto E K l.label (envMap l.mapping (t :: L) d).1
      (envMap l.mapping (t :: L) d).2)
    (fun st => .frameC st) (fun hr => .frameHandle hr) hctx (n + 2) W h _ hadm hok hC
    hgate (fun j hj U hx hu h' v hh' hv _ hq => hnext j hj U hx hu h' v hh' hv hq) hhandler

end Verification.Kinds
