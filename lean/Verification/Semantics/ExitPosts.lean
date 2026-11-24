import Verification.Semantics.ExitSchemas

/-! # The postcondition of a call per completion

What a callable's type guarantees of each completion of a call (the note
*Tolerant frames*, §6, Call on both exits, and "The action of an effect"):
from the call's entry state, the state the completion reaches is admissible,
its heaps meet the completion's frame, and every postcondition of the
completion holds, the specification instantiated at the call's actuals
(`Exits.exitPost`). Admissibility is part of the guarantee, never a premise:
the action of an effect includes the base relation. At a world and heap
rather than an indexed state the guarantee holds at every well-formed
endpoint with a positive budget (`Exits.exitPostW`); a safe run supplies the
states (`SafePostExcW.weaken_admissible`, `SafePostExcW.complete_normal`,
`SafePostExcW.complete_exceptional`), at the world the run reaches. -/
namespace Verification.CallEffects
open Verification Footprints Parity TolerantFrames HeapObservations

/-- **A completion's guarantee at a call** with receiver `r` and actuals
`args`, from the indexed state `s` to `s'`, completing with `v` (the
returned or thrown value): the completion's exit specification at the call's
arity holds, at the empty arena (a contract states no assertion-arena
formula) and the mark of the entry heap's length. -/
def Exits.exitPost (x : Exits ExitSchema) (c : Completion) (r : Tm) (args : List Tm) (s s' : IndexedHeap)
    (v : Tm) : Prop :=
  ((x.atArity args.length).get c).Holds AssertionArena.empty (callState r args v s.h.length s s')

/-- A completion's guarantee read at a budget, a world and a heap, with the
returned or thrown value. -/
abbrev ExitPostW := (k : Nat) → WorldT k → Heap → Tm → Prop

/-- **A completion's guarantee at worlds and heaps**: from the entry world
`U` and heap `before`, at every exit world and heap, both endpoints well
formed and of positive budget, the guarantee at the indexed states they
form. -/
def Exits.exitPostW (x : Exits ExitSchema) (c : Completion) (r : Tm) (args : List Tm) {j : Nat} (U : WorldT j)
    (before : Heap) : ExitPostW :=
  fun k V after v => ∀ (hj : 0 < j) (hu : WorldAdm U) (hh : HeapOk j U before) (hk : 0 < k) (hv : WorldAdm V)
    (hh' : HeapOk k V after), x.exitPost c r args ⟨j, U, before, hj, hu, hh⟩ ⟨k, V, after, hk, hv, hh'⟩ v

section
variable {x : Exits ExitSchema} {c : Completion} {r : Tm} {args : List Tm} {s s' : IndexedHeap} {v : Tm}

/-- **At indexed endpoints the two readings agree.** -/
theorem Exits.exitPostW_iff (x : Exits ExitSchema) (c : Completion) (r : Tm) (args : List Tm)
    (s s' : IndexedHeap) (v : Tm) :
    x.exitPostW c r args s.W s.h s'.n s'.W s'.h v ↔ x.exitPost c r args s s' v :=
  ⟨fun h => h s.pos s.adm s.ok s'.pos s'.adm s'.ok, fun h _ _ _ _ _ _ => h⟩

/-- The completion reaches an admissible state. -/
theorem Exits.exitPost_admissible (h : x.exitPost c r args s s' v) : Admissible s s' := h.1.1

theorem Exits.atArity_frame (x : Exits ExitSchema) (n : Nat) (c : Completion) :
    ((x.atArity n).get c).frame = (x.get c).frame := by
  cases c <;> rfl

/-- **The completion's heaps meet its frame**, read at the call's
positions. -/
theorem Exits.exitPost_frame (h : x.exitPost c r args s s' v) :
    Post (x.get c).frame (callEnv r args) s.h s'.h := by
  have h2 := h.1.2
  rwa [Exits.atArity_frame] at h2

/-- **Each postcondition of the completion holds**, instantiated at the
call. -/
theorem Exits.exitPost_ensures (h : x.exitPost c r args s s' v) :
    ∀ F ∈ (x.get c).ensures, Holds AssertionArena.empty (callState r args v s.h.length s s')
      (instantiateFormula (x.callInstantiation args.length) F) := by
  intro F hF
  apply h.2
  cases c <;> exact List.mem_map_of_mem hF

end

/-! ## Safety supplies the states -/

/-- **Consequence at admissible endpoints**: a postcondition implication
required only at the admissible, well-formed, positive states a run from the
entry reaches transports safety with postconditions. One induction on safety,
carrying the extension of the entry world. -/
theorem SafePostExcW.weaken_admissible {Ξ T : Fam} {Q Q' : WPost} {R R' : WExc} (s : IndexedHeap)
    (hq : ∀ (s' : IndexedHeap) (v : Tm), Admissible s s' → Q s'.n s'.W s'.h v → Q' s'.n s'.W s'.h v)
    (hr : ∀ s' : IndexedHeap, Admissible s s' → R s'.n s'.W s'.h → R' s'.n s'.W s'.h) {t : Tm}
    (hs : SafePostExcW Ξ T Q R s.n s.W s.h t) : SafePostExcW Ξ T Q' R' s.n s.W s.h t := by
  suffices H : ∀ (n : Nat) (hle : n ≤ s.n) (W : WorldT n) (h : Heap) (t : Tm), WExt (trunc n hle s.W) W →
      WorldAdm W → HeapOk n W h → SafePostExcW Ξ T Q R n W h t → SafePostExcW Ξ T Q' R' n W h t from
    H s.n (Nat.le_refl _) s.W s.h t (by rw [trunc_id]; exact WExt_refl _) s.adm s.ok hs
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ hs; exact hs
  | succ p ih =>
    intro hle W h t hx hw hok hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, hT, hQ⟩ | ⟨hth, hR⟩) | ⟨U, h', t', hx', hu, st, hh', hs'⟩
    · exact .inl (.inl ⟨hv, hT, hq ⟨p + 1, W, h, Nat.succ_pos _, hw, hok⟩ t ⟨hle, hx⟩ hQ⟩)
    · exact .inl (.inr ⟨hth, hr ⟨p + 1, W, h, Nat.succ_pos _, hw, hok⟩ ⟨hle, hx⟩ hR⟩)
    · refine .inr ⟨U, h', t', hx', hu, st, hh', ih (by omega) U h' t' ?_ hu hh' hs'⟩
      simpa only [trunc_trunc] using WExt_trans (WExt_trunc (Nat.le_succ p) hx) hx'

/-- **Consequence at admissible endpoints, the throw's postcondition reading
the thrown value**: as `SafePostExcW.weaken_admissible`. -/
theorem SafePostExcV.weaken_admissible {Ξ T : Fam} {Q Q' : WPost} {R R' : WExcV} (s : IndexedHeap)
    (hq : ∀ (s' : IndexedHeap) (v : Tm), Admissible s s' → Q s'.n s'.W s'.h v → Q' s'.n s'.W s'.h v)
    (hr : ∀ (s' : IndexedHeap) (v : Tm), Admissible s s' → R s'.n s'.W s'.h v → R' s'.n s'.W s'.h v) {t : Tm}
    (hs : SafePostExcV Ξ T Q R s.n s.W s.h t) : SafePostExcV Ξ T Q' R' s.n s.W s.h t := by
  suffices H : ∀ (n : Nat) (hle : n ≤ s.n) (W : WorldT n) (h : Heap) (t : Tm), WExt (trunc n hle s.W) W →
      WorldAdm W → HeapOk n W h → SafePostExcV Ξ T Q R n W h t → SafePostExcV Ξ T Q' R' n W h t from
    H s.n (Nat.le_refl _) s.W s.h t (by rw [trunc_id]; exact WExt_refl _) s.adm s.ok hs
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ hs; exact hs
  | succ p ih =>
    intro hle W h t hx hw hok hs
    obtain ⟨hrf, hs⟩ := hs
    refine ⟨hrf, ?_⟩
    rcases hs with (⟨hv, hT, hQ⟩ | ⟨u, hra, hsc, hξ, hR⟩) | ⟨U, h', t', hx', hu, st, hh', hs'⟩
    · exact .inl (.inl ⟨hv, hT, hq ⟨p + 1, W, h, Nat.succ_pos _, hw, hok⟩ t ⟨hle, hx⟩ hQ⟩)
    · exact .inl (.inr ⟨u, hra, hsc, hξ, hr ⟨p + 1, W, h, Nat.succ_pos _, hw, hok⟩ u ⟨hle, hx⟩ hR⟩)
    · refine .inr ⟨U, h', t', hx', hu, st, hh', ih (by omega) U h' t' ?_ hu hh' hs'⟩
      simpa only [trunc_trunc] using WExt_trans (WExt_trunc (Nat.le_succ p) hx) hx'

/-- **A normal completion within the budget reaches one admissible indexed
state**, the world the run reaches, its result of the type and the
postcondition holding there. -/
theorem SafePostExcW.complete_normal {Ξ T : Fam} {Q : WPost} {R : WExc} (s : IndexedHeap) {k : Nat}
    {t : Tm} {h' : Heap} {v : Tm} (hst : Steps k s.h t h' v) (hv : isVal v = true) (hk : k < s.n)
    (hs : SafePostExcW Ξ T Q R s.n s.W s.h t) :
    ∃ s' : IndexedHeap, s'.h = h' ∧ Admissible s s' ∧ T s'.n s'.W v ∧ Q s'.n s'.W h' v := by
  obtain ⟨j, hj, U, hjk, hx, hu, hh, -, hs'⟩ := SafePostExcW.run hst (Nat.le_of_lt hk) s.adm s.ok hs
  cases j with
  | zero => omega
  | succ p =>
    rcases hs'.2 with (⟨-, hT, hQ⟩ | ⟨hth, -⟩) | ⟨_, _, _, _, _, st, -⟩
    · exact ⟨⟨p + 1, U, h', Nat.succ_pos _, hu, hh⟩, rfl, ⟨hj, hx⟩, hT, hQ⟩
    · rw [hth.not_val] at hv; cases hv
    · exact absurd st (value_no_step hv)

/-- **An exceptional completion within the budget reaches one admissible
indexed state**, the world the run reaches, the thrown value of the
exception family and the postcondition holding there. -/
theorem SafePostExcW.complete_exceptional {Ξ T : Fam} {Q : WPost} {R : WExc} (s : IndexedHeap) {k : Nat}
    {t : Tm} {h' : Heap} {t' u : Tm} (hst : Steps k s.h t h' t') (hraise : Raises t' u) (hk : k < s.n)
    (hs : SafePostExcW Ξ T Q R s.n s.W s.h t) :
    ∃ s' : IndexedHeap, s'.h = h' ∧ Admissible s s' ∧ Thrown Ξ s'.n s'.W t' ∧ R s'.n s'.W h' := by
  obtain ⟨j, hj, U, hjk, hx, hu, hh, -, hs'⟩ := SafePostExcW.run hst (Nat.le_of_lt hk) s.adm s.ok hs
  cases j with
  | zero => omega
  | succ p =>
    rcases hs'.2 with (⟨hv, -, -⟩ | ⟨hth, hR⟩) | ⟨_, _, _, _, _, st, -⟩
    · cases hraise <;> simp [isVal] at hv
    · exact ⟨⟨p + 1, U, h', Nat.succ_pos _, hu, hh⟩, rfl, ⟨hj, hx⟩, hth, hR⟩
    · exact absurd st (raises_no_step hraise)

/-! ## A call: evaluation, then invocation -/

/-- **Evaluation reaching an invocation** (the note's Call: evaluation of
the callee, the receiver and the arguments, spread expansion included,
precedes invocation): from budget `n`, world `W` and heap `h`, the term is an
invocation meeting `E` there, or raises a value of `Ξ` meeting `R`, or steps,
to an admissible extension of the world and a well-formed heap, to a term
with the same property. -/
def EvalCallSafe (Ξ : Fam) (E : (n : Nat) → WorldT n → Heap → Tm → Tm → List Tm → Prop) (R : WExcV) :
    (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, W, _, t => RefsOk W t
  | n + 1, W, h, t => RefsOk W t ∧
      (((∃ f r vs, t = .invoke f r vs ∧ E (n + 1) W h f r vs) ∨
        (∃ v, Raises t v ∧ Scoped 0 v ∧ Ξ (n + 1) W v ∧ R (n + 1) W h v)) ∨
      (∃ (U : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧ Step h t h' t' ∧
          HeapOk n U h' ∧ EvalCallSafe Ξ E R n U h' t'))

/-- An invocation meeting `E` is an evaluation reaching it. -/
theorem EvalCallSafe.invoke {Ξ : Fam} {E : (n : Nat) → WorldT n → Heap → Tm → Tm → List Tm → Prop} {R : WExcV}
    {n : Nat} {W : WorldT n} {h : Heap} {f r : Tm} {vs : List Tm} (href : RefsOk W (.invoke f r vs))
    (hE : E n W h f r vs) : EvalCallSafe Ξ E R n W h (.invoke f r vs) := by
  cases n with
  | zero => exact href
  | succ n => exact ⟨href, .inl (.inl ⟨f, r, vs, rfl, hE⟩)⟩

/-- **A term that neither is a value nor raises has its guarantee read past
its step**: safety at postconditions implying others at every completion,
where the budget left after the term's step is positive, is safety at the
others. -/
theorem SafePostExcV.weaken_inert {Ξ T : Fam} {Q Q' : WPost} {R R' : WExcV} {n : Nat} {W : WorldT (n + 1)}
    {h : Heap} {t : Tm} (hnv : isVal t = false) (hnr : ∀ u, ¬ Raises t u)
    (hq : 0 < n → ∀ k V a v, Q k V a v → Q' k V a v) (hr : 0 < n → ∀ k V a v, R k V a v → R' k V a v)
    (hs : SafePostExcV Ξ T Q R (n + 1) W h t) : SafePostExcV Ξ T Q' R' (n + 1) W h t := by
  obtain ⟨hrf, (⟨hv, -⟩ | ⟨u, hra, -⟩) | ⟨U, h', t', hx, hu, st, hh', hs'⟩⟩ := hs
  · rw [hnv] at hv; cases hv
  · exact absurd hra (hnr u)
  · refine ⟨hrf, .inr ⟨U, h', t', hx, hu, st, hh', ?_⟩⟩
    cases n with
    | zero => exact hs'
    | succ m => exact SafePostExcV.weaken (hq (Nat.succ_pos _)) (hr (Nat.succ_pos _)) hs'

/-- A term that steps neither is a value nor raises. -/
theorem Step.inert {h h' : Heap} {t t' : Tm} (st : Step h t h' t') : isVal t = false ∧ ∀ u, ¬ Raises t u :=
  ⟨Bool.eq_false_iff.mpr fun hv => value_no_step hv st, fun _ hu => raises_no_step hu st⟩

/-- An invocation at values neither is a value nor raises. -/
theorem invoke_values_inert {f r : Tm} {vs : List Tm} (hf : isVal f = true) (hr : isVal r = true)
    (hv : CallArguments.Values vs) : isVal (.invoke f r vs) = false ∧ ∀ u, ¬ Raises (.invoke f r vs) u := by
  refine ⟨rfl, fun u hu => ?_⟩
  cases hu with
  | callL h => rw [raises_not_val h] at hf; cases hf
  | callRecv _ h => rw [raises_not_val h] at hr; cases hr
  | callArg _ _ hi _ h =>
    have := hv _ (List.mem_of_getElem? hi)
    rw [raises_not_val h] at this; cases this

/-- **An invocation an evaluation reached** from a call's entry: its world
reached from the call's (`WorldReach`), and the call's term evaluating to it
from the call's heap (the evaluation prefix). -/
def EvalReached {n m : Nat} (W : WorldT n) (h : Heap) (t : Tm) (U : WorldT m) (h' : Heap) (t' : Tm) : Prop :=
  WorldReach W U ∧ ∃ k, Steps k h t h' t'

/-- **A call's guarantee at a completion** (the note's Call, before any
consequence): an invocation `f r vs` the evaluation reached from the call's
entry (`EvalReached`), at a well-formed state of budget `m + 1`, meeting `E`,
and the completion's guarantee at its receiver and evaluated actuals from
its entry: the invocation's world truncated by the invocation's step, its
heap, the budget there positive. -/
def Exits.callExit (x : Exits ExitSchema) (c : Completion)
    (E : (n : Nat) → WorldT n → Heap → Tm → Tm → List Tm → Prop) {n : Nat} (W : WorldT n) (h : Heap)
    (t : Tm) : ExitPostW :=
  fun k V after v => ∃ (m : Nat) (U : WorldT (m + 1)) (h' : Heap) (f r : Tm) (vs : List Tm),
    EvalReached W h t U h' (.invoke f r vs) ∧ WorldAdm U ∧ HeapOk (m + 1) U h' ∧ 0 < m ∧
      E (m + 1) U h' f r vs ∧ x.exitPostW c r vs (trunc m (Nat.le_succ m) U) h' k V after v

/-- **A call at its callee's exits** (the note's Call): where evaluation of
the callee, the receiver and the arguments is safe and reaches invocations
at values meeting `E`, each safe at the specification's exits from its
entry, the call is safe; each completion is a throw of the evaluation,
meeting `R`, or a completion of a reached invocation with its guarantee
(`Exits.callExit`). -/
theorem call_site_exits {Ξ T : Fam} {x : Exits ExitSchema} {R : WExcV}
    {E : (n : Nat) → WorldT n → Heap → Tm → Tm → List Tm → Prop}
    (hval : ∀ m U h f r vs, E m U h f r vs → isVal f = true ∧ isVal r = true ∧ CallArguments.Values vs)
    (hinvoke : ∀ m (U : WorldT (m + 1)) h f r vs, E (m + 1) U h f r vs →
      SafePostExcV Ξ T (x.exitPostW .normal r vs (trunc m (Nat.le_succ m) U) h)
        (x.exitPostW .exceptional r vs (trunc m (Nat.le_succ m) U) h) (m + 1) U h (.invoke f r vs)) :
    ∀ {n W h t}, WorldAdm W → HeapOk n W h → EvalCallSafe Ξ E R n W h t →
      SafePostExcV Ξ T (x.callExit .normal E W h t)
        (fun k V a v => R k V a v ∨ x.callExit .exceptional E W h t k V a v) n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ he; exact he
  | succ n ih =>
    intro W h t hw hh he
    obtain ⟨hrf, he⟩ := he
    rcases he with (hinv | hraise) | hstep
    · obtain ⟨f, r, vs, rfl, hE⟩ := hinv
      obtain ⟨hf, hr, hv⟩ := hval _ _ _ _ _ _ hE
      obtain ⟨hnv, hnr⟩ := invoke_values_inert hf hr hv
      have hreach : EvalReached W h (.invoke f r vs) W h (.invoke f r vs) := ⟨WorldReach.refl W, 0, .refl⟩
      exact SafePostExcV.weaken_inert hnv hnr
        (fun hn _ _ _ _ hp => ⟨n, W, h, f, r, vs, hreach, hw, hh, hn, hE, hp⟩)
        (fun hn _ _ _ _ hp => .inr ⟨n, W, h, f, r, vs, hreach, hw, hh, hn, hE, hp⟩) (hinvoke n W h f r vs hE)
    · obtain ⟨v, hra, hsc, hξ, hR⟩ := hraise
      exact ⟨hrf, .inl (.inr ⟨v, hra, hsc, hξ, .inl hR⟩)⟩
    · obtain ⟨U, h', t', hx, hu, st, hh', he⟩ := hstep
      have hxU : WorldReach W U := ⟨Nat.le_succ n, hx⟩
      have back : ∀ c k V a v, x.callExit c E U h' t' k V a v → x.callExit c E W h t k V a v := by
        rintro c k V a v ⟨m, U', h'', f, r, vs, ⟨hreach, j, hsteps⟩, hrest⟩
        exact ⟨m, U', h'', f, r, vs, ⟨hxU.trans hreach, j + 1, .next st hsteps⟩, hrest⟩
      exact ⟨hrf, .inr ⟨U, h', t', hx, hu, st, hh', SafePostExcV.weaken (back .normal)
        (fun k V a v hp => hp.imp_right (back .exceptional k V a v)) (ih hu hh' he)⟩⟩

/-- **The entry of a call's guarantee**: the reached invocation's entry is a
well-formed indexed state whose world is reached from the call's, and the
completion's guarantee holds from it at every well-formed exit. -/
theorem Exits.callExit_entry {x : Exits ExitSchema} {c : Completion}
    {E : (n : Nat) → WorldT n → Heap → Tm → Tm → List Tm → Prop} {n : Nat} {W : WorldT n} {h : Heap} {t : Tm}
    {k : Nat} {V : WorldT k} {after : Heap} {v : Tm} (hp : x.callExit c E W h t k V after v) :
    ∃ (s : IndexedHeap) (m : Nat) (U : WorldT (m + 1)) (f r : Tm) (vs : List Tm),
      EvalReached W h t U s.h (.invoke f r vs) ∧ E (m + 1) U s.h f r vs ∧ WorldReach W s.W ∧
        x.exitPostW c r vs s.W s.h k V after v := by
  obtain ⟨m, U, h', f, r, vs, hreach, hu, hh, hm, hE, hx⟩ := hp
  refine ⟨⟨m, trunc m (Nat.le_succ m) U, h', hm, WorldAdm_trunc _ hu, HeapOk_trunc m U h' hh⟩, m, U, f, r, vs,
    hreach, hE, hreach.1.trans ⟨Nat.le_succ m, WExt_refl _⟩, hx⟩

/-- **Erasure at the states a run reaches**: safety with world-indexed
postconditions gives safety at heap postconditions each implies at every
admissible state the run reaches from the entry (`SafePostExcV.weaken_admissible`). -/
theorem SafePostExcV.erase_reached {Ξ T : Fam} {Q : WPost} {R : WExcV} {H : Post} {J : Heap → Prop}
    (s : IndexedHeap)
    (hn : ∀ (s' : IndexedHeap) (v : Tm), Admissible s s' → Q s'.n s'.W s'.h v → H s'.h v)
    (he : ∀ (s' : IndexedHeap) (v : Tm), Admissible s s' → R s'.n s'.W s'.h v → J s'.h) {t : Tm}
    (hs : SafePostExcV Ξ T Q R s.n s.W s.h t) : SafePostExc Ξ T H J s.n s.W s.h t :=
  SafePostExcV.iff_lift.mp
    (SafePostExcV.weaken_admissible s (Q' := WPost.lift H) (R' := (WExc.lift J).liftV) hn he hs)

/-- Valid references on a call's receiver and actuals give valid roots on
its call environment. -/
theorem callEnv_rootsOk {k : Nat} {W : WorldT k} {r : Tm} {args : List Tm}
    (hr : RefsOk W r) (ha : ∀ a ∈ args, RefsOk W a) : RootsOk W (callEnv r args) := by
  intro i
  cases i with
  | zero => exact hr
  | succ j =>
    simp only [callEnv, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, List.getD]
    cases h : args[j]? with
    | none => simp [RefsOk, refs]
    | some a => simpa using ha a (List.mem_of_getElem? h)

/-- **One exit specification entails another** at every call with valid
references and every pair of states: the rule of consequence on both
completions. -/
def Exits.Entails (x y : Exits ExitSchema) : Prop :=
  ∀ c r args s s' v, RootsOk s.W (callEnv r args) → x.exitPost c r args s s' v → y.exitPost c r args s s' v

/-- Entailment at worlds and heaps. -/
theorem Exits.Entails.exitPostW {x y : Exits ExitSchema} (h : x.Entails y) {c : Completion} {r : Tm}
    {args : List Tm} {j : Nat} {U : WorldT j} {before : Heap} {k : Nat} {V : WorldT k} {after : Heap} {v : Tm}
    (hr : RootsOk U (callEnv r args))
    (hp : x.exitPostW c r args U before k V after v) : y.exitPostW c r args U before k V after v :=
  fun h1 h2 h3 h4 h5 h6 => h _ _ _ _ _ _ hr (hp h1 h2 h3 h4 h5 h6)

/-- **A completion's guarantee read at heaps**: some indexed states with
these heaps at which the guarantee holds; what a consequence reading no
world concludes (`Exits.heapPost_frame`). -/
def Exits.heapPost (x : Exits ExitSchema) (c : Completion) (r : Tm) (args : List Tm) (before after : Heap)
    (v : Tm) : Prop :=
  ∃ s s' : IndexedHeap, s.h = before ∧ s'.h = after ∧ x.exitPost c r args s s' v

theorem Exits.heapPost_frame {x : Exits ExitSchema} {c : Completion} {r : Tm} {args : List Tm}
    {before after : Heap} {v : Tm} (h : x.heapPost c r args before after v) :
    Post (x.get c).frame (callEnv r args) before after := by
  obtain ⟨s, s', rfl, rfl, hp⟩ := h
  exact Exits.exitPost_frame hp

/-- **Safety at a callable's exits from an entry is safety at their heap
readings** (`SafePostExcV.erase_reached`). -/
theorem SafePostExcV.heapPosts {Ξ T : Fam} {x : Exits ExitSchema} {r : Tm} {args : List Tm} (s : IndexedHeap)
    {t : Tm}
    (hs : SafePostExcV Ξ T (x.exitPostW .normal r args s.W s.h) (x.exitPostW .exceptional r args s.W s.h)
      s.n s.W s.h t) :
    SafePostExc Ξ T (x.heapPost .normal r args s.h) (fun h' => ∃ v, x.heapPost .exceptional r args s.h h' v)
      s.n s.W s.h t :=
  SafePostExcV.erase_reached s
    (fun s' _ _ hp => ⟨s, s', rfl, rfl, hp s.pos s.adm s.ok s'.pos s'.adm s'.ok⟩)
    (fun s' v _ hp => ⟨v, s, s', rfl, rfl, hp s.pos s.adm s.ok s'.pos s'.adm s'.ok⟩) hs

/-! ## A call's guarantee from its invocation entry -/

/-- **An invocation entry held from a call's entry**: the call's heap `h`,
at a budget at most the call's `n` and a world extending the call's world
`W` truncated there; the entry an evaluation reaching the invocation in the
heap the call starts in leaves (the note's Call: evaluation precedes
invocation, and the specification is relative to the invocation's entry). -/
def HeldEntry {n : Nat} (W : WorldT n) (h : Heap) (s : IndexedHeap) : Prop :=
  s.h = h ∧ WorldReach W s.W

/-- An entry held from a world reached from another is held from that
other. -/
theorem HeldEntry.trans {n j : Nat} {W : WorldT n} {U : WorldT j} (hx : WorldReach W U)
    {h : Heap} {s : IndexedHeap} (hs : HeldEntry U h s) : HeldEntry W h s :=
  ⟨hs.1, hx.trans hs.2⟩

/-- **A completion's guarantee from an invocation entry**: at the exit, the
completion's guarantee from some entry meeting `P`. -/
def Exits.fromEntry (x : Exits ExitSchema) (c : Completion) (r : Tm) (args : List Tm)
    (P : IndexedHeap → Prop) : ExitPostW :=
  fun k V after v => ∃ s, P s ∧ x.exitPostW c r args s.W s.h k V after v

/-- **A call's guarantee on a normal return**, its evaluation keeping the
heap: the normal exit from an entry held from the call's. -/
abbrev Exits.heldPost (x : Exits ExitSchema) (r : Tm) (args : List Tm) {n : Nat} (W : WorldT n) (h : Heap) :
    WPost :=
  x.fromEntry .normal r args (HeldEntry W h)

/-- **A call's guarantee on a throw**, its evaluation keeping the heap: the
exceptional exit from an entry held from the call's, or a throw of the
evaluation, in the heap the call starts in. -/
abbrev Exits.heldExc (x : Exits ExitSchema) (r : Tm) (args : List Tm) {n : Nat} (W : WorldT n) (h : Heap) :
    WExcV :=
  fun k V after v => x.fromEntry .exceptional r args (HeldEntry W h) k V after v ∨ after = h

/-- **The exact entry of an invocation is held from the invocation's**:
safety, past a step, at a specification's exits from the invocation's world
truncated by its step and its heap gives safety at them from an entry held
from the invocation's (`HeldEntry`). -/
theorem SafePostExcV.fromEntry_of_exact {Ξ T : Fam} {x : Exits ExitSchema} {r : Tm} {vs : List Tm} {n : Nat}
    {W : WorldT (n + 1)} {h : Heap} {t : Tm} (hw : WorldAdm W) (hh : HeapOk (n + 1) W h)
    (hnv : isVal t = false) (hnr : ∀ u, ¬ Raises t u)
    (hs : SafePostExcV Ξ T (x.exitPostW .normal r vs (trunc n (Nat.le_succ n) W) h)
      (x.exitPostW .exceptional r vs (trunc n (Nat.le_succ n) W) h) (n + 1) W h t) :
    SafePostExcV Ξ T (x.fromEntry .normal r vs (HeldEntry W h)) (x.fromEntry .exceptional r vs (HeldEntry W h))
      (n + 1) W h t :=
  let s (hn : 0 < n) : IndexedHeap := ⟨n, trunc n (Nat.le_succ n) W, h, hn, WorldAdm_trunc _ hw, HeapOk_trunc n W h hh⟩
  have hs0 (hn : 0 < n) : HeldEntry W h (s hn) := ⟨rfl, Nat.le_succ _, WExt_refl _⟩
  SafePostExcV.weaken_inert hnv hnr (fun hn _ _ _ _ hp => ⟨s hn, hs0 hn, hp⟩) (fun hn _ _ _ _ hp => ⟨s hn, hs0 hn, hp⟩) hs

/-- **Consequence from held entries**: where one specification's exit
entails another's at other actuals, the guarantee from an entry held from
an invocation's entry gives the other's from an entry held from the entry of
a call the invocation's is an extension of. -/
theorem Exits.fromEntry_weaken {x y : Exits ExitSchema} {c : Completion} {r r' : Tm} {args other : List Tm}
    (hxy : ∀ s s' v, x.exitPost c r args s s' v → y.exitPost c r' other s s' v)
    {n j : Nat} {W : WorldT n} {U : WorldT j} (hx : WorldReach W U) {h : Heap}
    {k : Nat} {V : WorldT k} {after : Heap} {v : Tm}
    (hp : x.fromEntry c r args (HeldEntry U h) k V after v) : y.fromEntry c r' other (HeldEntry W h) k V after v := by
  obtain ⟨s, hs, hp⟩ := hp
  exact ⟨s, hs.trans hx, fun h1 h2 h3 h4 h5 h6 => hxy _ _ _ (hp h1 h2 h3 h4 h5 h6)⟩

/-- **A call's guarantee from held entries read at its heaps**: at the
admissible states a run from the call's entry reaches, the guarantee from a
held entry is the guarantee at some indexed states, the first with the
call's heap (`Exits.heapPost`); a throw of the evaluation leaves the call's
heap. -/
theorem SafePostExcV.heldPosts {Ξ T : Fam} {x : Exits ExitSchema} {r : Tm} {args : List Tm} {n : Nat}
    {W : WorldT n} {h : Heap} {t : Tm} (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : SafePostExcV Ξ T (x.heldPost r args W h) (x.heldExc r args W h) n W h t) :
    SafePostExc Ξ T (x.heapPost .normal r args h)
      (fun h' => (∃ v, x.heapPost .exceptional r args h h' v) ∨ h' = h) n W h t := by
  cases n with
  | zero => exact hs
  | succ n =>
    refine SafePostExcV.erase_reached ⟨n + 1, W, h, Nat.succ_pos _, hw, hh⟩ ?_ ?_ hs
    · rintro s' v - ⟨s, ⟨hsh, -⟩, hp⟩
      exact ⟨s, s', hsh, rfl, hp s.pos s.adm s.ok s'.pos s'.adm s'.ok⟩
    · rintro s' v - (⟨s, ⟨hsh, -⟩, hp⟩ | heq)
      · exact .inl ⟨v, s, s', hsh, rfl, hp s.pos s.adm s.ok s'.pos s'.adm s'.ok⟩
      · exact .inr heq

/-- **Consequence of a call's guarantee to held entries**: where every
invocation meeting `E` is at the call's heap, and the exit at the reached
invocation's receiver and actuals entails another specification's at given
ones (both read at the invocation), the call's guarantee gives the other's from an entry held from the
call's (`HeldEntry`). -/
theorem Exits.callExit_held {x y : Exits ExitSchema} {c : Completion}
    {E : (n : Nat) → WorldT n → Heap → Tm → Tm → List Tm → Prop} {n : Nat} {W : WorldT n} {h : Heap} {t : Tm}
    {r' : Tm} {other : List Tm} (hE : ∀ m U h' f r vs, E m U h' f r vs → h' = h)
    (hxy : ∀ m U f r vs, E m U h f r vs → ∀ s s' v, x.exitPost c r vs s s' v → y.exitPost c r' other s s' v)
    {k : Nat} {V : WorldT k} {after : Heap} {v : Tm} (hp : x.callExit c E W h t k V after v) :
    y.fromEntry c r' other (HeldEntry W h) k V after v := by
  obtain ⟨s, m, U, f, r, vs, -, hEm, hw, hx⟩ := Exits.callExit_entry hp
  obtain rfl := hE _ _ _ _ _ _ hEm
  exact ⟨s, ⟨rfl, hw⟩, fun h1 h2 h3 h4 h5 h6 => hxy _ _ _ _ _ hEm _ _ _ (hx h1 h2 h3 h4 h5 h6)⟩

end Verification.CallEffects
