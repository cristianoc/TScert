import Verification.Programs.TolerantFramesMergeEntailed

/-! # Tolerant frames: the facts near a merge's names, on fuel

`SinglePass.Store.linearNear` lists the unconditional index facts connected
to some names through linear facts, at most `limit` of them, by the
search on fuel `SinglePass.linearNearFuel` at fuel `s.size + 1`: each
round reads every frontier name's facts (`Store.about`), keeps an
unconditional index fact not kept yet while fewer than `limit` are kept,
and puts the names of a kept linear fact not seen yet on the next
frontier. Every fact it lists is an unconditional `index` fact of the
store (`linearNearFuel_sound`), so `LinearNearSound` holds
(`linearNearSound_of_eq` with `linearNearFuelEq`, the equation by the
pass's definition). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations HeapKnowledge
open Verification.SinglePass (Atom Store State NearState nearStep nearRound nearLoop linearNearFuel)

/-- The facts listed are unconditional index facts of the store. -/
def NearOk (s : Store) (st : NearState) : Prop := ∀ i ∈ st.out.toList, Atom.index i ∈ storeAll s ∧ i.cond = none

theorem nearStep_ok {s : Store} {limit : Nat} {x : Nat} {a : Atom} (ha : a ∈ s.about x) {st : NearState}
    (hst : NearOk s st) : NearOk s (nearStep limit st a) := by
  have hnames : ∀ (L : List Nat) (st : NearState), NearOk s st → NearOk s (L.foldl (fun (st : NearState) y =>
      if !st.seen.contains y then { st with seen := st.seen.insert y, next := y :: st.next } else st) st) := by
    intro L st hst
    refine foldl_inv (NearOk s) _ _ _ hst fun y _ st hst => ?_
    split
    · exact hst
    · exact hst
  unfold nearStep
  split
  · rename_i i
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
      have hpush : NearOk s { st with kept := st.kept.insert (.index i), out := st.out.push i } := by
        intro j hj
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact hst j hj
        · exact ⟨about_storeAll ha, hc.1.1⟩
      split
      · exact hnames _ _ hpush
      · exact hpush
    · exact hst
  · exact hst

theorem nearRound_ok {s : Store} {limit : Nat} {frontier : List Nat} {st : NearState} (hst : NearOk s st) :
    NearOk s (nearRound s limit frontier st) := by
  unfold nearRound
  refine foldl_inv (NearOk s) _ _ _ (fun i hi => hst i hi) fun x _ st hst => ?_
  exact foldl_inv (NearOk s) _ _ _ hst fun a ha st hst => nearStep_ok ha hst

theorem nearLoop_ok {s : Store} {limit : Nat} :
    ∀ (fuel : Nat) (frontier : List Nat) (st : NearState), NearOk s st → NearOk s (nearLoop s limit fuel frontier st)
  | 0, _, _, h => h
  | n + 1, frontier, st, h => by
    unfold nearLoop
    split
    · exact nearLoop_ok n _ _ (nearRound_ok h)
    · exact h

/-- **The search on fuel lists facts of its store**: every fact
`linearNearFuel` returns is an unconditional `index` fact of the store. -/
theorem linearNearFuel_sound (s : Store) (names : List Nat) (limit fuel : Nat) :
    ∀ x ∈ linearNearFuel s names limit fuel, Atom.index x ∈ storeAll s ∧ x.cond = none :=
  nearLoop_ok fuel names _ (fun i hi => by simp at hi)

/-- **The pass's `linearNear` is the search on fuel**: `linearNearFuel` at
fuel `s.size + 1`. -/
def LinearNearFuelEq : Prop :=
  ∀ (s : Store) (names : List Nat) (limit : Nat), s.linearNear names limit = linearNearFuel s names limit

/-- **(`linearNearFuelEq`) The pass's `linearNear` is the search on fuel**,
by its definition. -/
theorem linearNearFuelEq : LinearNearFuelEq := fun _ _ _ => rfl

/-- **`LinearNearSound` from the equation.** -/
theorem linearNearSound_of_eq (heq : LinearNearFuelEq) : LinearNearSound := by
  intro s names limit x hx
  rw [heq] at hx
  exact (linearNearFuel_sound s names limit _ x hx).1

end Verification.TolerantFrames
