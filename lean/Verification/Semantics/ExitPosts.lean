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

end Verification.CallEffects
