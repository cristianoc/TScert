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

/-- **A call is safe where its evaluation is and each invocation it
reaches is**: every completion is a throw of the evaluation, meeting `R`, or
a completion of an invocation the evaluation reached. -/
theorem call_site_sound {Ξ T : Fam} {Q : WPost} {R : WExcV}
    {E : (n : Nat) → WorldT n → Heap → Tm → Tm → List Tm → Prop}
    (hinvoke : ∀ n (W : WorldT n) h f r vs, E n W h f r vs → SafePostExcV Ξ T Q R n W h (.invoke f r vs)) :
    ∀ {n W h t}, EvalCallSafe Ξ E R n W h t → SafePostExcV Ξ T Q R n W h t := by
  intro n
  induction n with
  | zero => intro _ _ _ he; exact he
  | succ n ih =>
    intro W h t he
    obtain ⟨hrf, he⟩ := he
    rcases he with (hinv | hraise) | hstep
    · obtain ⟨f, r, vs, rfl, hE⟩ := hinv
      exact hinvoke _ W h f r vs hE
    · exact ⟨hrf, .inl (.inr hraise)⟩
    · obtain ⟨U, h', t', hx, hu, st, hh, he⟩ := hstep
      exact ⟨hrf, .inr ⟨U, h', t', hx, hu, st, hh, ih he⟩⟩

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

/-- **One exit specification entails another** at every call and every
pair of states: the rule of consequence on both completions. -/
def Exits.Entails (x y : Exits ExitSchema) : Prop :=
  ∀ c r args s s' v, x.exitPost c r args s s' v → y.exitPost c r args s s' v

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
  s.h = h ∧ ∃ hle : s.n ≤ n, WExt (trunc s.n hle W) s.W

/-- An entry held from a world extending the truncation of another is held
from that other. -/
theorem HeldEntry.trans {n j : Nat} {W : WorldT n} {U : WorldT j} (hj : j ≤ n) (hx : WExt (trunc j hj W) U)
    {h : Heap} {s : IndexedHeap} (hs : HeldEntry U h s) : HeldEntry W h s := by
  obtain ⟨rfl, hle, hy⟩ := hs
  refine ⟨rfl, Nat.le_trans hle hj, WExt_trans ?_ hy⟩
  simpa only [trunc_trunc] using WExt_trunc hle hx

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

/-- **Consequence from held entries**: where one specification's exit
entails another's at other actuals, the guarantee from an entry held from
an invocation's entry gives the other's from an entry held from the entry of
a call the invocation's is an extension of. -/
theorem Exits.fromEntry_weaken {x y : Exits ExitSchema} {c : Completion} {r r' : Tm} {args other : List Tm}
    (hxy : ∀ s s' v, x.exitPost c r args s s' v → y.exitPost c r' other s s' v)
    {n j : Nat} {W : WorldT n} {U : WorldT j} (hj : j ≤ n) (hx : WExt (trunc j hj W) U) {h : Heap}
    {k : Nat} {V : WorldT k} {after : Heap} {v : Tm}
    (hp : x.fromEntry c r args (HeldEntry U h) k V after v) : y.fromEntry c r' other (HeldEntry W h) k V after v := by
  obtain ⟨s, hs, hp⟩ := hp
  exact ⟨s, hs.trans hj hx, fun h1 h2 h3 h4 h5 h6 => hxy _ _ _ (hp h1 h2 h3 h4 h5 h6)⟩

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

end Verification.CallEffects
