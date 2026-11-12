import Verification.Programs.TolerantFramesMergeEntailed

/-! # Tolerant frames: the facts near a merge's names, on fuel

`SinglePass.Store.linearNear` lists the unconditional index facts connected
to some names through linear facts, at most `limit` of them, by a `while`
loop over a frontier of names. This module states the same search by
structural recursion on fuel (`linearNearFuel`): each round reads every
frontier name's facts (`Store.about`), keeps an unconditional index fact not
kept yet while fewer than `limit` are kept, and puts the names of a kept
linear fact not seen yet on the next frontier. Every fact it lists is an
unconditional `index` fact of the store (`linearNearFuel_sound`). A round
that leaves the frontier non-empty kept a fact it had not kept, and the
facts kept are distinct live facts, so the store's size plus one rounds
reach the loop's end (read from the code, not proved here).

The single residue (`LinearNearFuelEq`): the pass's `linearNear` equals this
search at fuel `s.size + 1`; it gives `LinearNearSound`
(`linearNearSound_of_eq`). -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations HeapKnowledge
open Verification.SinglePass (Atom Store State)

/-- The search's state: the names seen, the next frontier, the facts kept
and the facts listed. -/
structure NearState where
  seen : Std.HashSet Nat
  next : List Nat
  kept : Std.HashSet Atom
  out : Array IndexAtom

/-- One fact read at a frontier name: kept where it is an unconditional
index fact not kept yet and fewer than `limit` are listed; its names put on
the next frontier, where it is linear, if not seen yet. -/
def nearStep (limit : Nat) (st : NearState) (a : Atom) : NearState :=
  match a with
  | .index i =>
    if i.cond.isNone && !st.kept.contains a && st.out.size < limit then
      let st := { st with kept := st.kept.insert a, out := st.out.push i }
      match i.fact with
      | .linear _ => a.names.foldl (fun (st : NearState) y =>
          if !st.seen.contains y then { st with seen := st.seen.insert y, next := y :: st.next } else st) st
      | _ => st
    else st
  | _ => st

/-- One round over the frontier `frontier`, from an empty next frontier. -/
def nearRound (s : Store) (limit : Nat) (frontier : List Nat) (st : NearState) : NearState :=
  frontier.foldl (fun st x => (s.about x).foldl (nearStep limit) st) { st with next := [] }

/-- The search on fuel: rounds while the frontier is non-empty and fewer than
`limit` facts are listed. -/
def nearLoop (s : Store) (limit : Nat) : Nat → List Nat → NearState → NearState
  | 0, _, st => st
  | n + 1, frontier, st =>
    if !frontier.isEmpty && st.out.size < limit then
      let st' := nearRound s limit frontier st
      nearLoop s limit n st'.next st'
    else st

/-- **`Store.linearNear` on fuel**: the facts the search lists from `names`,
at most `limit`, in `fuel` rounds. -/
def linearNearFuel (s : Store) (names : List Nat) (limit : Nat := 40) (fuel : Nat := s.size + 1) :
    List IndexAtom :=
  (nearLoop s limit fuel names { seen := Std.HashSet.ofList names, next := [], kept := {}, out := #[] }).out.toList

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

/-- **(Named hypothesis) The pass's `linearNear` is the search on fuel**: its
`while` loop, which Lean does not unfold, returns what `linearNearFuel`
returns at fuel `s.size + 1`. It holds by construction once the pass's own
search is written on that fuel. -/
def LinearNearFuelEq : Prop :=
  ∀ (s : Store) (names : List Nat) (limit : Nat), s.linearNear names limit = linearNearFuel s names limit

/-- **`LinearNearSound` from the equation.** -/
theorem linearNearSound_of_eq (heq : LinearNearFuelEq) : LinearNearSound := by
  intro s names limit x hx
  rw [heq] at hx
  exact (linearNearFuel_sound s names limit _ x hx).1

end Verification.TolerantFrames
