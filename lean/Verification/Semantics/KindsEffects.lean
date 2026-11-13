import Verification.Semantics.KindsCalls
/-!
# Call effects over kinded worlds

A signature's effect (`CallEffects.Effect`) as a contract over kinded worlds,
and the composition of such contracts at one successor world.

- **The effect's postconditions read the entry and the exit world**
  (`Effect.postK`): the heap postcondition of the signature (`Effect.post`)
  and, where it states an element write, the view write from the call's
  entry world and heap to its exit world and heap (`ViewWriteOf`). The
  exceptional one is the signature's heap postcondition (`Effect.excPostK`).
- **A promise** (`PromiseK`) is the native-contract condition
  (`NativeContract`) at those postconditions; a construct promise
  (`ConstructK`) its counterpart for `new` (`NativeConstruct`).
- **Meeting** (`PromiseK.combine`): two promises of one value with the same
  result meaning (`Effect.sameResult`) give the promise of their meet. The
  first execution's world is kept with its view write; the second
  execution's heap postconditions are carried to it by determinism
  (`SafeW.cross`); the view writes agree because the two effects state the
  same element write.
- **Weakening** (`PromiseK.weaken`), **prefix transport**
  (`Effect.postK_prefix`), **invocation** (`NativeContract.safe`,
  `NativeConstruct.safe`) and **world facts** (`SafeW.world`: a fact of the
  world that extension and truncation keep holds at every exit).
- **The gate** (`gate_write`, `gate_handled`): a callback allocates an
  object, then a value meeting two effectful signatures performs a view
  write. Its every normal exit, and its every throw entering a handler, is
  at one world where the allocated object's property capability holds, the
  heap meets the world in both parts (contracts and roles' shapes), and the
  call's postconditions of both signatures hold.

The general relations these read (`ViewWrite`, `WPost`) are below the call
effects, in `Semantics/ElementWrites.lean`.
-/
namespace Verification.Kinds
open Verification

/-! ## Consequence, world facts and two runs of one term -/

/-- **Consequence** at the budgets an execution reaches, on the exception
family, the result type and both postconditions. -/
theorem SafeW.consequence {Ξ Ξ' T T' : Fam} {Q Q' : WPost} {R R' : WExc} :
    ∀ {n : Nat},
    (∀ j, j ≤ n → ∀ (W : WorldT j) v, Ξ j W v → Ξ' j W v) →
    (∀ j, j ≤ n → ∀ (W : WorldT j) v, T j W v → T' j W v) →
    (∀ j, j ≤ n → ∀ (W : WorldT j) h v, Q j W h v → Q' j W h v) →
    (∀ j, j ≤ n → ∀ (W : WorldT j) h, R j W h → R' j W h) →
    ∀ {W : WorldT n} {h : Heap} {t : Tm}, SafeW Ξ T Q R n W h t → SafeW Ξ' T' Q' R' n W h t
  | 0, _, _, _, _, _, _, _, hs => hs
  | n + 1, hΞ, hT, hQ, hR, _, _, _, ⟨hr, hs⟩ => by
    refine ⟨hr, ?_⟩
    rcases hs with (⟨hv, hT', hq⟩ | ⟨⟨v, hrv, hsc, hx⟩, hR'⟩) | ⟨U, h', t', hx, hu, st, hh, hs'⟩
    · exact .inl (.inl ⟨hv, hT _ (Nat.le_refl _) _ _ hT', hQ _ (Nat.le_refl _) _ _ _ hq⟩)
    · exact .inl (.inr ⟨⟨v, hrv, hsc, hΞ _ (Nat.le_refl _) _ _ hx⟩, hR _ (Nat.le_refl _) _ _ hR'⟩)
    · exact .inr ⟨U, h', t', hx, hu, st, hh, SafeW.consequence (fun j hj => hΞ j (by omega))
        (fun j hj => hT j (by omega)) (fun j hj => hQ j (by omega)) (fun j hj => hR j (by omega)) hs'⟩

/-- **A world fact holds at every exit**: a fact of the world that every
extension and every truncation keep, true of the entry world, holds at the
world of each normal and exceptional exit, beside its postcondition. -/
theorem SafeW.world {Ξ T : Fam} {Q : WPost} {R : WExc} {P : (k : Nat) → WorldT k → Prop}
    (hmono : ∀ k (W W' : WorldT k), WExt W W' → P k W → P k W')
    (htrunc : ∀ k j (hj : j ≤ k) (W : WorldT k), P k W → P j (trunc j hj W)) :
    ∀ {n : Nat} {W : WorldT n} {h : Heap} {t : Tm}, P n W → SafeW Ξ T Q R n W h t →
      SafeW Ξ T (fun k W h v => Q k W h v ∧ P k W) (fun k W h => R k W h ∧ P k W) n W h t
  | 0, _, _, _, _, hs => hs
  | _ + 1, _, _, _, hp, ⟨hr, hs⟩ => by
    refine ⟨hr, ?_⟩
    rcases hs with (⟨hv, hT, hq⟩ | ⟨ht, hR⟩) | ⟨U, h', t', hx, hu, st, hh, hs'⟩
    · exact .inl (.inl ⟨hv, hT, hq, hp⟩)
    · exact .inl (.inr ⟨ht, hR, hp⟩)
    · exact .inr ⟨U, h', t', hx, hu, st, hh,
        SafeW.world hmono htrunc (hmono _ _ _ hx (htrunc _ _ _ _ hp)) hs'⟩

/-- Two result types combine into a third across the two worlds two runs of
one term reach over one heap. -/
def CrossK (n : Nat) (B C D : Fam) : Prop :=
  ∀ (j : Nat), j ≤ n → ∀ (W W' : WorldT j) (h : Heap), HeapOk j W h → HeapOk j W' h →
    ∀ (u : Val), B j W u → C j W' u → D j W u

/-- **Two runs of one term at one world.** The first run's world is kept,
with its world-indexed postconditions; the second run takes the same steps
(`Step_det`), so its heap postconditions hold at the same exits, and its
result type combines with the first's (`CrossK`). -/
theorem SafeW.cross {Ξ Ξ' B C D : Fam} {Q : WPost} {R : WExc} {Q' : Heap → Val → Prop}
    {R' : Heap → Prop} :
    ∀ (n : Nat), CrossK n B C D → ∀ (W W' : WorldT n) (h : Heap) (t : Tm), HeapOk n W h → HeapOk n W' h →
      SafeW Ξ B Q R n W h t → SafeW Ξ' C (WPost.lift Q') (WExc.lift R') n W' h t →
        SafeW Ξ D (fun k W h v => Q k W h v ∧ Q' h v) (fun k W h => R k W h ∧ R' h) n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ hs _; exact hs
  | succ p ih =>
    intro hc W W' h t hok hok' hs1 hs2
    obtain ⟨hr, hs1⟩ := hs1
    obtain ⟨-, hs2⟩ := hs2
    refine ⟨hr, ?_⟩
    rcases hs1 with (⟨hv1, hB, hQ⟩ | ⟨ht1, hR1⟩) | ⟨Z, h1, t1, hz, huz, hst1, hok1, hcont1⟩ <;>
      rcases hs2 with (⟨hv2, hC, hQ2⟩ | ⟨ht2, hR2⟩) | ⟨Z', h2, t2, -, -, hst2, hok2, hcont2⟩
    · exact .inl (.inl ⟨hv1, hc (p + 1) (Nat.le_refl _) W W' h hok hok' t hB hC, hQ, hQ2⟩)
    · obtain ⟨_, hr2, -⟩ := ht2; rw [raises_not_val hr2] at hv1; contradiction
    · exact absurd hst2 (value_no_step hv1)
    · obtain ⟨_, hr1, -⟩ := ht1; rw [raises_not_val hr1] at hv2; contradiction
    · exact .inl (.inr ⟨ht1, hR1, hR2⟩)
    · obtain ⟨_, hr1, -⟩ := ht1; exact absurd hst2 (raises_no_step hr1)
    · exact absurd hst1 (value_no_step hv2)
    · obtain ⟨_, hr2, -⟩ := ht2; exact absurd hst1 (raises_no_step hr2)
    · obtain ⟨rfl, rfl⟩ := Step_det hst1 hst2
      exact .inr ⟨Z, h1, t1, hz, huz, hst1, hok1,
        ih (fun j hj => hc j (by omega)) Z Z' h1 t1 hok1 hok2 hcont1 hcont2⟩

/-! ## A signature's postconditions over kinded worlds -/

/-- The view write a signature states, from the call's entry world and heap
to its exit world and heap: where it states an element write, `ViewWriteOf`
of it at the actuals. -/
def _root_.Verification.CallEffects.Effect.viewPost (e : CallEffects.Effect) (args : List Tm) {j : Nat}
    (W : WorldT j) (h : Heap) : WPost :=
  fun _ W' h' _ => ∀ w, e.elementWrite = some w → ViewWriteOf w args W h W' h'

/-- **A signature's normal postcondition over kinded worlds**, given the
call's entry world and heap: its heap postcondition (`Effect.post`) and its
view write (`Effect.viewPost`). -/
def _root_.Verification.CallEffects.Effect.postK (e : CallEffects.Effect) : CPost :=
  fun r args _ W h k W' h' v => e.post r args h h' v ∧ e.viewPost args W h k W' h' v

/-- A signature's exceptional postcondition over kinded worlds: its heap
postcondition on a throw (`Effect.excPost`). -/
def _root_.Verification.CallEffects.Effect.excPostK (e : CallEffects.Effect) : CExc :=
  fun r args _ _ h _ _ h' => e.excPost r args h h'

/-- **The meet's postcondition** is the first signature's, view write
included, and the second's heap postcondition: the two state the same
element write (`Effect.sameResult`). -/
theorem _root_.Verification.CallEffects.Effect.postK_meet {a b : CallEffects.Effect}
    (hs : a.sameResult b = true) (r : Tm) (args : List Tm) (j : Nat) (W : WorldT j) (h : Heap)
    (k : Nat) (W' : WorldT k) (h' : Heap) (v : Val) :
    (a.meet b).postK r args j W h k W' h' v ↔ a.postK r args j W h k W' h' v ∧ b.post r args h h' v := by
  simp only [CallEffects.Effect.postK, CallEffects.Effect.viewPost]
  rw [CallEffects.Effect.post_meet hs]
  exact ⟨fun ⟨⟨ha, hb⟩, hw⟩ => ⟨⟨ha, hw⟩, hb⟩, fun ⟨⟨ha, hw⟩, hb⟩ => ⟨⟨ha, hb⟩, hw⟩⟩

/-- A signature covers another over kinded worlds: it covers it
(`Effect.Covers`), and it states every element write the other states. -/
def _root_.Verification.CallEffects.Effect.CoversK (a b : CallEffects.Effect) : Prop :=
  a.Covers b ∧ ∀ w, b.elementWrite = some w → a.elementWrite = some w

/-- The checker's covering decides covering over kinded worlds. -/
theorem _root_.Verification.CallEffects.Effect.coversK_sound {a b : CallEffects.Effect}
    (h : a.covers b = true) : a.CoversK b := by
  refine ⟨CallEffects.Effect.covers_sound h, fun w hw => ?_⟩
  simp only [CallEffects.Effect.covers, Bool.and_eq_true] at h
  have hwr := h.2
  simp only [hw, Option.isNone_some, Bool.false_or, beq_iff_eq] at hwr
  exact hwr

/-! ## The view write from a prefix -/

/-- **The view write from a prefix of the entry**: a view write from a
world and heap extending an entry world and heap is one from the entry. -/
theorem ViewWrite.prefix_left {n m n' : Nat} {W : WorldT n} {M : WorldT m} {h hm : Heap}
    {W' : WorldT n'} {h' : Heap} (hle : m ≤ n) (hx : WExt (trunc m hle W) M) (hok : HeapOk n W h)
    (hp : h.IsPrefix hm) (hw : ViewWrite M hm W' h') : ViewWrite W h W' h' := by
  have hlen : h.length = (entries W).length := by simpa using hok.1.1
  have hrole : ∀ {l r}, Kinds.roleAt W l = some r → Kinds.roleAt M l = some r := fun hr =>
    WExt_roleAt hx (by simpa using hr)
  have hget : ∀ {l r}, Kinds.roleAt W l = some r → hm[l]? = h[l]? := by
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

/-- **Prefix transport of a signature's postcondition**: allocation between
the call's entry and the start of its body composes with the postcondition,
where the frame's paths and the entry terms agree across it
(`Effect.post_prefix`), and the view write holds from the entry
(`ViewWrite.prefix_left`). -/
theorem _root_.Verification.CallEffects.Effect.postK_prefix (e : CallEffects.Effect) {r : Tm}
    {args : List Tm} {n m : Nat} {W : WorldT n} {M : WorldT m} {h hm : Heap} (hle : m ≤ n)
    (hx : WExt (trunc m hle W) M) (hok : HeapOk n W h) (hp : h.IsPrefix hm)
    (hagree : e.PrefixAgrees (CallEffects.callEnv r args) h hm)
    (hens : e.EntryAgrees (CallEffects.callEnv r args) h hm) {k : Nat} {W' : WorldT k} {h' : Heap}
    {v : Val} (hpost : e.postK r args m M hm k W' h' v) : e.postK r args n W h k W' h' v :=
  ⟨e.post_prefix hp hagree hens hpost.1, fun w hw =>
    ⟨(hpost.2 w hw).1.prefix_left hle hx hok hp, fun k hk => ((hpost.2 w hw).2 k hk).prefix_left hp⟩⟩

/-! ## Promises over kinded worlds -/

/-- **A promise over kinded worlds**: the native-contract condition at the
signature's precondition and postconditions over kinded worlds, its result
type `R` given the receiver and the actuals. -/
def PromiseK (Ξ : Fam) (e : CallEffects.Effect) (Acc : (j : Nat) → WorldT j → List Tm → Prop) (Rc : Fam)
    (R : Tm → List Tm → Fam) (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  NativeContract Ξ Acc Rc e.Requires R e.postK e.excPostK k W v

/-- **Meeting two promises.** Two promises of one value whose signatures mean
the same result give the promise of the signatures' meet, at a result type
combining theirs. The first execution's world and its view write are kept;
the second's heap postconditions hold at that world by determinism. -/
theorem PromiseK.combine {Ξ : Fam} {a b : CallEffects.Effect} {Acc : (j : Nat) → WorldT j → List Tm → Prop}
    {Rc : Fam} {B C D : Tm → List Tm → Fam} {k : Nat} {W : WorldT k} {v : Val}
    (hs : a.sameResult b = true) (ha : PromiseK Ξ a Acc Rc B k W v) (hb : PromiseK Ξ b Acc Rc C k W v)
    (hcross : ∀ r args n, n < k → CrossK n (B r args) (C r args) (D r args)) :
    PromiseK Ξ (a.meet b) Acc Rc D k W v := by
  intro j hj U hx hu heap hh hvr r hrv hrc hrr args hv hacc har hq
  have hq' : b.Requires r args heap := by
    simp only [CallEffects.Effect.sameResult, Bool.and_eq_true, beq_iff_eq] at hs
    exact ⟨fun R hR => hq.1 R (by simp only [CallEffects.Effect.meet]; rw [hs.1.1.1.1.2]; exact hR),
      fun F hF => hq.2 F (by simp only [CallEffects.Effect.meet]; rw [hs.1.1.2]; exact hF)⟩
  obtain ⟨u, hiu, hsu⟩ := ha j hj U hx hu heap hh hvr r hrv hrc hrr args hv hacc har hq
  obtain ⟨c, hic, hsc⟩ := hb j hj U hx hu heap hh hvr r hrv hrc hrr args hv hacc har hq'
  cases CallArguments.invoke_deterministic hiu hic
  have hboth := SafeW.cross j (hcross r args j hj) U U heap u hh hh hsu
    (SafeW.erase (Q' := b.post r args heap) (R' := b.excPost r args heap)
      (fun _ _ _ _ hp => hp.1) (fun _ _ _ hp => hp) hsc)
  refine ⟨u, hiu, SafeW.mono ?_ ?_ hboth⟩
  · intro k' W' h' val hp
    exact (CallEffects.Effect.postK_meet hs r args j U heap k' W' h' val).mpr hp
  · intro k' W' h' hp
    exact CallEffects.Effect.excPost_meet hs r args heap h' hp.1 hp.2

/-- **Weakening a promise**: to a signature it covers, a wider exception
family, narrower receivers and actuals, and a wider result type. -/
theorem PromiseK.weaken {Ξ Ξ' : Fam} {a b : CallEffects.Effect}
    {Acc Acc' : (j : Nat) → WorldT j → List Tm → Prop} {Rc Rc' : Fam} {R T : Tm → List Tm → Fam}
    {k : Nat} {W : WorldT k} {v : Val} (he : a.CoversK b)
    (hexc : ∀ j, j < k → ∀ (U : WorldT j) u, Ξ j U u → Ξ' j U u)
    (hrecv : ∀ j, j < k → ∀ (U : WorldT j) r, Rc' j U r → Rc j U r)
    (hacc : ∀ j, j < k → ∀ (U : WorldT j) args, Acc' j U args → Acc j U args)
    (hres : ∀ r args j, j < k → ∀ (U : WorldT j) u, R r args j U u → T r args j U u)
    (h : PromiseK Ξ a Acc Rc R k W v) : PromiseK Ξ' b Acc' Rc' T k W v := by
  intro j hj U hx hu heap hh hvr r hrv hrc hrr args hv ha har hq
  obtain ⟨u, hiu, hsu⟩ := h j hj U hx hu heap hh hvr r hrv (hrecv j hj U r hrc) hrr args hv
    (hacc j hj U args ha) har (he.1.2.2.2 r args heap hq)
  refine ⟨u, hiu, SafeW.consequence (fun i hi => hexc i (by omega)) (fun i hi => hres r args i (by omega))
    ?_ ?_ hsu⟩
  · intro _ _ W' h' val hp
    have hp' : a.post r args heap h' val ∧ a.viewPost args U heap _ W' h' val := hp
    exact show b.post r args heap h' val ∧ b.viewPost args U heap _ W' h' val from
      ⟨he.1.1 _ _ _ _ _ hp'.1, fun w hw => hp'.2 w (he.2 w hw)⟩
  · intro _ _ W' h' hp
    exact show b.excPost r args heap h' from he.1.2.2.1 _ _ _ _ hp

/-! ## Construction -/

/-- `new` on a value whose construction runs `result` steps there. -/
theorem ConstructsTo.step {v : Val} {args : List Tm} {result : Tm} (hc : ConstructsTo v args result)
    (hv : CallArguments.Values args) (h : Heap) : Step h (.construct v args) h result := by
  obtain ⟨fs, c, enter, oid, rfl, hcon, rfl⟩ := hc
  unfold CallArguments.construction at hcon
  split at hcon
  · cases hcon; exact .constructGraph hv
  · cases hcon

/-- **The native-contract condition of construction**: from every
well-formed entry configuration meeting the input contract, `new` runs a
construction safe at the result type and both postconditions, the receiver
`undefined`. -/
def NativeConstruct (Ξ : Fam) (Acc : (j : Nat) → WorldT j → List Tm → Prop)
    (requires : List Tm → Heap → Prop) (R : List Tm → Fam) (post : CPost) (excPost : CExc)
    (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U →
    ∀ (heap : Heap), HeapOk j U heap → RefsOk U v →
      ∀ args, CallArguments.Values args → Acc j U args → (∀ a ∈ args, RefsOk U a) → requires args heap →
        ∃ result, ConstructsTo v args result ∧
          SafeW Ξ (R args) (post .undef args j U heap) (excPost .undef args j U heap) j U heap result

/-- **Construction of a value meeting the condition is safe.** -/
theorem NativeConstruct.safe {Ξ : Fam} {Acc : (j : Nat) → WorldT j → List Tm → Prop}
    {requires : List Tm → Heap → Prop} {R : List Tm → Fam} {post : CPost} {excPost : CExc}
    {n : Nat} {W : WorldT (n + 1)} {v : Val} (hc : NativeConstruct Ξ Acc requires R post excPost (n + 1) W v)
    (hadm : WorldAdm W) {heap : Heap} (hh : HeapOk (n + 1) W heap) (hv : RefsOk W v) {args : List Tm}
    (ha : CallArguments.Values args) (hacc : Acc n (trunc n (Nat.le_succ n) W) args)
    (har : ∀ a ∈ args, RefsOk W a) (hreq : requires args heap) :
    SafeW Ξ (R args) (post .undef args n (trunc n (Nat.le_succ n) W) heap)
      (excPost .undef args n (trunc n (Nat.le_succ n) W) heap) (n + 1) W heap (.construct v args) := by
  obtain ⟨result, hi, hs⟩ := hc n (Nat.lt_succ_self n) _ (WExt_refl _) (WorldAdm_trunc _ hadm) heap
    (HeapOk_trunc n W heap hh) (RefsOk_trunc _ hv) args ha hacc (fun a h => RefsOk_trunc _ (har a h)) hreq
  refine ⟨fun x hx => ?_, .inr ⟨_, heap, result, WExt_refl _, WorldAdm_trunc _ hadm,
    ConstructsTo.step hi ha heap, HeapOk_trunc n W heap hh, hs⟩⟩
  simp only [refs, refsArgs_eq, List.mem_append, List.mem_flatMap] at hx
  rcases hx with hx | ⟨a, ha', hx⟩
  · exact hv x hx
  · exact har a ha' x hx

/-- A construct signature over kinded worlds: the construction condition at
the signature's precondition and postconditions, the receiver `undefined`. -/
def ConstructK (Ξ : Fam) (e : CallEffects.Effect) (P : (j : Nat) → WorldT j → List Tm → Prop)
    (R : List Tm → Fam) (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  NativeConstruct Ξ P (e.Requires .undef) R e.postK e.excPostK k W v

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
    SafeW Ξ T (fun _ U h' v => v = .objAt (slots h.length [f]) .absent (h.length + 1) ∧ RefsOk U v ∧
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
  fun k W' h' v => (∃ (j : Nat) (U : WorldT j) (h₁ : Heap), a.postK r args j U h₁ k W' h' v ∧
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
parts (`SafeW.exit`), and both signatures' postconditions hold of the call,
the first's view write from the call's entry world; on a throw, the same
with both exceptional postconditions. -/
theorem gate_write {Ξ : Fam} {a b : CallEffects.Effect} {Acc : (j : Nat) → WorldT j → List Tm → Prop}
    {Rc : Fam} {B C D : Tm → List Tm → Fam} {f : PropKey} {x g r : Tm} {args : List Tm} {A : Fam}
    {n : Nat} {W : WorldT (n + 2)} {h : Heap}
    (hs : a.sameResult b = true) (ha : PromiseK Ξ a Acc Rc B (n + 2) W g)
    (hb : PromiseK Ξ b Acc Rc C (n + 2) W g)
    (hcross : ∀ r args j, j < n + 2 → CrossK j (B r args) (C r args) (D r args))
    (hadm : WorldAdm W) (hok : HeapOk (n + 2) W h) (hsrc : isSourceVal x = true)
    (hf : f ≠ arrayStoreKey ∧ f ≠ viewElementsKey ∧ f ≠ viewLengthKey)
    (hA : CtrAdm (res A : Ctr (n + 1))) 
    (hxA : ∀ j (hj : j < n + 1), A j (trunc j (Nat.le_of_lt hj) (trunc (n + 1) (Nat.le_succ _) W)) x)
    (hrefs : RefsOk W (.letE (literal f x) (.invoke g r args)))
    (hscope : Scoped 0 (.invoke g r args)) (hrv : isVal r = true) (hargs : CallArguments.Values args)
    (hrc : ∀ j (U : WorldT j), Rc j U r) (hacc : ∀ j (U : WorldT j), Acc j U args)
    (hreq : ∀ h', h.IsPrefix h' → a.Requires r args h') :
    SafeW Ξ (fun _ _ _ => True) (gatePost a b r args (Capability.field f A) (slots h.length [f]))
      (gateExc a b r args (Capability.field f A) (slots h.length [f])) (n + 2) W h
      (.letE (literal f x) (.invoke g r args)) := by
  let fs := slots h.length [f]
  let cap := Capability.field f A
  let body : Tm := .invoke g r args
  have hcomb := PromiseK.combine (D := D) hs ha hb hcross
  have hbodyRefs : RefsOk W body := fun y hy => hrefs y
    (show y ∈ refs (literal f x) ++ refs body from List.mem_append.mpr (.inr hy))
  have hxr : RefsOk W x := fun y hy => hrefs y (by
    simp only [refs, literal, refsArgs_eq, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append]
    exact .inl hy)
  have hctx : CtxRefs (fun t => Tm.letE t body) := fun t y => by simp [refs]
  have hlit := literal_safe (Ξ := Ξ) (T := fun _ _ _ => True)
    (R := gateExc a b r args cap fs) hadm hok hsrc hxr hf hA hxA (fun _ _ => trivial)
  refine SafeW.bind (fun t => Tm.letE t body) (fun st => .letC st) (fun hr => .letC hr) hctx
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
      have hcall := NativeContract.safe (hcomb.down (by omega) hxV) (WorldAdm_trunc _ hu)
        (HeapOk_trunc (p + 1) U h' hh') hg hrv (hrc _ _) hr hargs (hacc _ _) hargsr (hreq h' hpre)
      have hw := SafeW.world (P := fun k W' => cap.Holds W' fs) (fun _ _ _ hx' hp => hp.mono hx')
        (fun _ _ hj' _ hp => hp.trunc hj') (hcap.trunc _) hcall
      refine SafeW.consequence (fun _ _ _ _ hξ => hξ) (fun _ _ _ _ _ => trivial) ?_ ?_ hw
      · intro _ _ W' h'' val ⟨hp, hc⟩
        obtain ⟨hpa, hpb⟩ := (CallEffects.Effect.postK_meet hs r args p _ h' _ W' h'' val).mp hp
        exact ⟨⟨p, _, h', hpa, hpb⟩, hc⟩
      · intro _ _ W' h'' ⟨hp, hc⟩
        exact ⟨⟨h', hp⟩, hc⟩

/-- **The gate's throw-to-handler variant.** Run in a graph node with a
handler, the gate's term is safe when the node continues from each normal
exit and the handler from each throw: the handler is entered at the throwing
configuration's world and heap, where the heap meets the world in both
parts, the thrown value is of the exception family with valid references,
the callback's object has its field capability, and the call's exceptional
postcondition holds (`SafeW.handle`). -/
theorem gate_handled {Ξ Ξ' B' : Fam} {Q' : WPost} {R' : WExc} {a b : CallEffects.Effect}
    {Acc : (j : Nat) → WorldT j → List Tm → Prop}
    {Rc : Fam} {B C D : Tm → List Tm → Fam} {f : PropKey} {x g r : Tm} {args : List Tm} {A : Fam}
    {n : Nat} {W : WorldT (n + 2)} {h : Heap}
    {E : List Tm} {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {L : List Tm}
    {d : Tm} {k : ControlFlow.Continuation} {l : ControlFlow.Target}
    (hs : a.sameResult b = true) (ha : PromiseK Ξ a Acc Rc B (n + 2) W g)
    (hb : PromiseK Ξ b Acc Rc C (n + 2) W g)
    (hcross : ∀ r args j, j < n + 2 → CrossK j (B r args) (C r args) (D r args))
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
        SafeW Ξ' B' Q' R' j U h' (.frame E K v L d k (some l)))
    (hhandler : ∀ m (hm : m + 1 ≤ n + 2) (U : WorldT (m + 1)), WExt (trunc (m + 1) hm W) U → WorldAdm U →
      ∀ h' v, HeapOk (m + 1) U h' → Ξ (m + 1) U v → RefsOk U v →
        gateExc a b r args (Capability.field f A) (slots h.length [f]) (m + 1) U h' →
        SafeW Ξ' B' Q' R' m (trunc m (Nat.le_succ m) U) h'
          (.goto E K l.label (envMap l.mapping (v :: L) d).1 (envMap l.mapping (v :: L) d).2)) :
    SafeW Ξ' B' Q' R' (n + 2) W h (.frame E K (.letE (literal f x) (.invoke g r args)) L d k (some l)) := by
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
  exact SafeW.handle (fun t => Tm.frame E K t L d k (some l))
    (fun t => .goto E K l.label (envMap l.mapping (t :: L) d).1
      (envMap l.mapping (t :: L) d).2)
    (fun st => .frameC st) (fun hr => .frameHandle hr) hctx (n + 2) W h _ hadm hok hC
    hgate (fun j hj U hx hu h' v hh' hv _ hq => hnext j hj U hx hu h' v hh' hv hq) hhandler

end Verification.Kinds
