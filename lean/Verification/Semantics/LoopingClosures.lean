import Verification.Semantics.CallEffects

/-! # Looping closures

A closure whose graph returns to its one node forever (`loopFn`): its run
never returns or throws and keeps the heap, so it is safe at every
postcondition (`loop_safe`), and it meets every fixed and variadic signature
at any effect, argument family, receiver and result (`loop_promise`,
`loop_callsT`, `loop_restsT`). It is the value the inhabitance of a framed
plan's initial premise gives each member of a native slot's contract
(the framed acceptance draft, "The initialization as a premise"). -/
namespace Verification.LoopingClosures
open Verification HeapObservations

/-- The looping graph's one node. -/
def loopE : List Tm := [.undef]
/-- Its continuation: back to the node. -/
def loopK : List (ControlFlow.Continuation × Option ControlFlow.Target) := [(.effect ⟨0, none⟩, none)]

def gotoL (L : List Tm) (d : Tm) (c : ComponentTag) : Tm := .goto loopE loopK 0 L d c
def frameL (L : List Tm) (d : Tm) (c : ComponentTag) : Tm :=
  .frame loopE loopK .undef L d (.effect ⟨0, none⟩) none c

theorem refs_frameL (L : List Tm) (d : Tm) (c : ComponentTag) : refs (frameL L d c) = refs (gotoL L d c) := by
  simp [frameL, gotoL, refs]

theorem step_goto (h : Heap) (L : List Tm) (d : Tm) (c : ComponentTag) : Step h (gotoL L d c) h (frameL L d c) := by
  have := Step.gotoEnter (h := h) (L := L) (d := d) (comp := c) (E := loopE) (K := loopK) (l := 0)
    (e := .undef) (k := .effect ⟨0, none⟩) (x := none) rfl rfl
  simpa [gotoL, frameL, instantiate] using this

theorem step_frame (h : Heap) (L : List Tm) (d : Tm) (c : ComponentTag) : Step h (frameL L d c) h (gotoL L d c) := by
  have := Step.frameEffect (h := h) (v := .undef) (E := loopE) (K := loopK) (L := L) (d := d)
    (l := ⟨0, none⟩) (x := none) (comp := c) rfl
  simpa [gotoL, frameL, envMap] using this

/-- **A run that loops is safe at every postcondition**: it never returns
or throws, and keeps the heap. -/
theorem loop_safe {Ξ T : Fam} {Q : WPost} {R : WExcV} (L : List Tm) (d : Tm) (c : ComponentTag) :
    ∀ n (W : WorldT n) h, WorldAdm W → HeapOk n W h → RefsOk W (gotoL L d c) →
      SafePostExcV Ξ T Q R n W h (gotoL L d c) ∧ SafePostExcV Ξ T Q R n W h (frameL L d c) := by
  intro n
  induction n with
  | zero =>
    intro W h _ _ hr
    have hr' : RefsOk W (frameL L d c) := by simpa [RefsOk, refs_frameL] using hr
    exact ⟨hr, hr'⟩
  | succ n ih =>
    intro W h hA hh hr
    have hr' : RefsOk W (frameL L d c) := by simpa [RefsOk, refs_frameL] using hr
    have hA' := WorldAdm_trunc (Nat.le_succ n) hA
    have hh' := HeapOk_trunc n W h hh
    obtain ⟨ig, if_⟩ := ih _ h hA' hh' (RefsOk_trunc (Nat.le_succ n) hr)
    exact ⟨⟨hr, .inr ⟨_, h, _, WExt_refl _, hA', step_goto h L d c, hh', if_⟩⟩,
      ⟨hr', .inr ⟨_, h, _, WExt_refl _, hA', step_frame h L d c, hh', ig⟩⟩⟩


/-- The closure whose body loops. -/
def loopFn (n : Nat) (c : ComponentTag) (oid : Nat) : Tm := .objAt [] (.graph n loopE loopK 0 [] .call false c) oid

theorem refs_parameters : ∀ (n : Nat) (args : List Tm), ∀ r ∈ (CallArguments.parameters n args).flatMap refs, r ∈ args.flatMap refs
  | 0, _ => by simp [CallArguments.parameters]
  | _ + 1, [] => by simpa [CallArguments.parameters, refs] using refs_parameters _ []
  | n + 1, a :: args => by
    intro r hr
    simp only [CallArguments.parameters, List.flatMap_cons, List.mem_append] at hr ⊢
    rcases hr with h | h
    · exact .inl h
    · exact .inr (refs_parameters n args r h)

/-- **The looping closure meets every signature** (the arrow equation at
any effect, argument family, receiver and result). -/
theorem loop_promise {Ξ : Fam} {effect} {Acc : ArgFam} {Rc Rr : Fam} {k : Nat} {W : WorldT k}
    (n : Nat) (c : ComponentTag) (oid : Nat) : CallEffects.PromiseWith Ξ effect Acc Rc Rr k W (loopFn n c oid) := by
  intro j hj U hx hu heap hh hvr r hrv hr hrr args hv har ha hq
  refine ⟨_, CallArguments.Invoke.graph hrv hv rfl, ?_⟩
  refine (loop_safe (Ξ := Ξ) _ _ _ j U heap hu hh ?_).1
  intro x hx'
  have hx2 : x ∈ refs r ∨ x ∈ (CallArguments.parameters n args).flatMap refs ∨ x ∈ refs (loopFn n c oid) := by
    simpa [gotoL, loopFn, CallArguments.graphEntry, refs, loopE, or_assoc] using hx'
  rcases hx2 with h1 | h2 | h3
  · exact hrr x h1
  · obtain ⟨a, ha', hxa⟩ := List.mem_flatMap.mp (refs_parameters n args x h2)
    exact har a ha' x hxa
  · exact hvr x h3

theorem loop_invocable (n : Nat) (c : ComponentTag) (oid : Nat) : Invocable (loopFn n c oid) :=
  ⟨_, _, _, rfl, rfl, by simp [loopFn, Scoped, loopE]⟩

theorem loop_callsT {Ξ : Fam} (L : List (CallEffects.Arrow Fam)) {k W} (n c oid) :
    CallEffects.callsT Ξ L k W (loopFn n c oid) :=
  ⟨loop_invocable n c oid, fun _ _ => loop_promise n c oid⟩

theorem loop_restsT {Ξ : Fam} (L : List CallEffects.RestSignature) {k W} (n c oid) :
    CallEffects.restsT Ξ L k W (loopFn n c oid) :=
  ⟨loop_invocable n c oid, fun _ _ => loop_promise n c oid⟩

end Verification.LoopingClosures
