import Verification.Source.Claims.FramedSpec

/-! # A call of a native at a node: the decision and its soundness

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The algorithm", step 4, "A call of a
native"). A call node of a code calls a native where its callee's value is
a native's: read from a native's outside slot of the code's closure. Which
capture each environment position of a graph run holds at each node is a
must analysis over the code's edges (`slotTable`), checked
(`slotTableB`); a node whose expression invokes the position holding an
outside capture calls that capture (`nativeAtB`). Where that capture holds
a value of the realm's code (`FramedSpec.RealmSlots`), the callee is a
closure of the realm's code (`nativeAt_sound`).

- **The run's gotos** (`RunGoto`): the entry of a closure of the code at
  its start, with the environment the entry builds, and each goto a node's
  frame steps to, by its continuation or its handler.
- **The table holds along the run** (`runGoto_holds`): at each goto of the
  run, each position the checked table gives a capture holds that capture.
- **The decision is sound** (`nativeAt_sound`): at a node `nativeAtB`
  decides, the node's callee, instantiated in the run's environment, is
  the outside capture the table names, a closure of the realm's code where
  it is a function and the capture holds a value of the realm's code.

A callee read through a receiver whose type's prototype is a native's slot
(`out.push(s)`, `w.flags.pop()`) is the next sub-step of step 1.4.3. -/
namespace Verification.SourceClaimJson
open Verification.TolerantFrames.ReadOnly ControlFlow

/-- A row of the table: per environment position, the capture it holds. -/
abbrev SlotRow := List (Option Nat)

/-- **The row at a code's entry** (`CallArguments.graphEntry`): the receiver,
`arity` parameters, the captures in order, then the closure itself. -/
def entryRow (arity ncaps : Nat) : SlotRow :=
  List.replicate (1 + arity) none ++ ((List.range ncaps).map some ++ [none])

/-- **A node's successors**: each target its continuation or its handler
goes to, with whether the node's value (or the thrown value) is bound
before the target's map. -/
def succs : Continuation × Option Target → List (Target × Bool)
  | (k, x) =>
    (match k with
      | .ret => []
      | .bind y => [(y, true)]
      | .effect y => [(y, false)]
      | .branch y n => [(y, false), (n, false)]
      | .branchBind y n => [(y, true), (n, true)]
      | .tagBind _ y n => [(y, true), (n, true)]) ++
    (match x with
      | some y => [(y, true)]
      | none => [])

/-- **A row through an edge**, as `envMap` maps the environment. -/
def transfer (row : SlotRow) (bind : Bool) (m : Option (List Nat)) : SlotRow :=
  let src := if bind then none :: row else row
  match m with
  | none => src
  | some slots => slots.map fun i => src.getD i none

/-- The positions both rows give one capture. -/
def meetRow (r₁ r₂ : SlotRow) : SlotRow :=
  (List.range (max r₁.length r₂.length)).map fun i =>
    if r₁.getD i none = r₂.getD i none then r₁.getD i none else none

/-- One round of the analysis: each reached node's row carried to its
successors, met with what they hold. -/
def slotRound (K : List (Continuation × Option Target)) (T : List (Option SlotRow)) : List (Option SlotRow) :=
  (List.range K.length).foldl (fun T l =>
    match T.getD l none, K[l]? with
    | some row, some kx =>
      (succs kx).foldl (fun T (y, b) =>
        let r := transfer row b y.mapping
        T.set y.label (some (match T.getD y.label none with
          | none => r
          | some r' => meetRow r' r))) T
    | _, _ => T) T

/-- **The table of a code** from its start, by rounds of the analysis; the
check (`slotTableB`) decides that it holds, whatever the number of rounds. -/
def slotTable (K : List (Continuation × Option Target)) (start arity ncaps : Nat) : List (Option SlotRow) :=
  let T₀ := (List.replicate K.length none).set start (some (entryRow arity ncaps))
  (List.range (K.length * (arity + ncaps + 3) + 1)).foldl (fun T _ => slotRound K T) T₀

/-- A row gives no capture another row does not give at that position. -/
def rowLe (r r' : SlotRow) : Prop := ∀ i k, r.getD i none = some k → r'.getD i none = some k

def rowLeB (r r' : SlotRow) : Bool :=
  (List.range r.length).all fun i => match r.getD i none with
    | some k => r'.getD i none == some k
    | none => true

theorem rowLeB_sound {r r' : SlotRow} (h : rowLeB r r' = true) : rowLe r r' := by
  intro i k hk
  have hi : i < r.length := by
    refine Decidable.byContradiction fun hn => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hk
    simp at hk
  have := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
  rw [hk] at this
  simpa using this

/-- **The table holds for a code** (decided): the start's row gives no
capture the entry row does not, and at each reached node, each successor
is reached with a row giving no capture the edge does not carry. -/
def slotTableB (K : List (Continuation × Option Target)) (start arity ncaps : Nat) (T : List (Option SlotRow)) : Bool :=
  (match T.getD start none with
    | some r => rowLeB r (entryRow arity ncaps)
    | none => false) &&
  (List.range K.length).all fun l => match T.getD l none, K[l]? with
    | some row, some kx => (succs kx).all fun (y, b) => match T.getD y.label none with
      | some r => rowLeB r (transfer row b y.mapping)
      | none => false
    | _, _ => true

/-- **A goto of one run of a code** from the entry of a closure with
captures `caps`: the entry's, and each one a node's frame steps to. -/
inductive RunGoto (E : List Tm) (K : List (Continuation × Option Target)) (start arity : Nat) (caps : List Tm)
    (comp : ComponentTag) : Nat → List Tm → Tm → Prop where
  | start (recv self : Tm) (args : List Tm) :
      RunGoto E K start arity caps comp start (recv :: CallArguments.parameters arity args ++ (caps ++ [self])) .nul
  | next {l l' : Nat} {L L' : List Tm} {d d' t : Tm} {k : Continuation} {x : Option Target} {h h' : Heap} :
      RunGoto E K start arity caps comp l L d → K[l]? = some (k, x) →
      Step h (.frame E K t L d k x comp) h' (.goto E K l' L' d' comp) →
      RunGoto E K start arity caps comp l' L' d'

/-- **The table's claims at a goto**: the node is reached, and each position
its row gives a capture holds that capture. -/
def Holds (T : List (Option SlotRow)) (caps : List Tm) (l : Nat) (L : List Tm) : Prop :=
  ∃ row, T.getD l none = some row ∧ ∀ i k, row.getD i none = some k → ∃ c, caps[k]? = some c ∧ L[i]? = some c

theorem entryParameters_length : ∀ (n : Nat) (args : List Tm), (CallArguments.parameters n args).length = n
  | 0, _ => rfl
  | n + 1, [] => by simp [CallArguments.parameters, entryParameters_length n []]
  | n + 1, _ :: as => by simp [CallArguments.parameters, entryParameters_length n as]

theorem entryRow_getD (arity ncaps i k : Nat) (h : (entryRow arity ncaps).getD i none = some k) :
    k < ncaps ∧ i = 1 + arity + k := by
  unfold entryRow at h
  rw [List.getD_eq_getElem?_getD] at h
  by_cases h₁ : i < 1 + arity
  · rw [List.getElem?_append_left (by simpa using h₁)] at h
    simp [h₁] at h
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt h₁)] at h
    simp only [List.length_replicate] at h
    by_cases h₂ : i - (1 + arity) < ncaps
    · rw [List.getElem?_append_left (by simpa using h₂)] at h
      simp [h₂] at h
      omega
    · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt h₂)] at h
      simp only [List.length_map, List.length_range] at h
      rcases hj : i - (1 + arity) - ncaps with _ | j
      · simp [hj] at h
      · simp [hj] at h

/-- **The table holds at the entry** (proved). -/
theorem holds_start {K : List (Continuation × Option Target)} {start arity : Nat} {caps : List Tm}
    {T : List (Option SlotRow)} (hT : slotTableB K start arity caps.length T = true) (recv self : Tm) (args : List Tm) :
    Holds T caps start (recv :: CallArguments.parameters arity args ++ (caps ++ [self])) := by
  simp only [slotTableB, Bool.and_eq_true] at hT
  obtain ⟨hs, -⟩ := hT
  cases hr : T.getD start none with
  | none => rw [hr] at hs; simp at hs
  | some row =>
    rw [hr] at hs
    refine ⟨row, hr, fun i k hk => ?_⟩
    obtain ⟨hkc, rfl⟩ := entryRow_getD arity caps.length i k (rowLeB_sound hs i k hk)
    refine ⟨caps[k], List.getElem?_eq_getElem hkc, ?_⟩
    have hp := entryParameters_length arity args
    rw [show 1 + arity + k = (recv :: CallArguments.parameters arity args).length + k by simp [hp]; omega,
      List.getElem?_append_right (by omega)]
    simp [List.getElem?_append_left hkc]

/-- A row through an edge gives the position of the source it names. -/
theorem transfer_holds {caps L : List Tm} {d v : Tm} {row : SlotRow} {b : Bool} {m : Option (List Nat)}
    (hL : ∀ i k, row.getD i none = some k → ∃ c, caps[k]? = some c ∧ L[i]? = some c) :
    ∀ i k, (transfer row b m).getD i none = some k → ∃ c, caps[k]? = some c ∧
      (envMap m (if b then v :: L else L) d).1[i]? = some c := by
  have hsrc : ∀ i k, (if b then none :: row else row).getD i none = some k →
      ∃ c, caps[k]? = some c ∧ (if b then v :: L else L)[i]? = some c := by
    intro i k hk
    cases b with
    | false => exact hL i k (by simpa using hk)
    | true =>
      cases i with
      | zero => simp at hk
      | succ i => simpa using hL i k (by simpa using hk)
  intro i k hk
  cases m with
  | none => exact hsrc i k (by simpa [transfer] using hk)
  | some slots =>
    simp only [transfer, List.getD_eq_getElem?_getD, List.getElem?_map] at hk
    cases hi : slots[i]? with
    | none => simp [hi] at hk
    | some j =>
      simp only [hi, Option.map_some, Option.getD_some] at hk
      obtain ⟨c, hc, hj⟩ := hsrc j k (by simpa [List.getD_eq_getElem?_getD] using hk)
      refine ⟨c, hc, ?_⟩
      simp [envMap, List.getElem?_map, hi, List.getD_eq_getElem?_getD, hj]

/-- **A frame's step to a goto follows one of its node's successors**
(proved, by cases on the step): the goto's label is a successor's, and its
environment the edge's map of the frame's, the value bound where the
successor binds. -/
theorem frame_goto_succ {E : List Tm} {K : List (Continuation × Option Target)} {t d d' : Tm} {L L' : List Tm}
    {k : Continuation} {x : Option Target} {comp : ComponentTag} {h h' : Heap} {l' : Nat}
    (hs : Step h (.frame E K t L d k x comp) h' (.goto E K l' L' d' comp)) :
    ∃ y b v, (y, b) ∈ succs (k, x) ∧ y.label = l' ∧ L' = (envMap y.mapping (if b then v :: L else L) d).1 := by
  cases hs with
  | frameRet hv => simp [isVal] at hv
  | frameBind _ => exact ⟨_, true, _, by simp [succs], rfl, rfl⟩
  | frameEffect _ => exact ⟨_, false, .nul, by simp [succs], rfl, rfl⟩
  | frameYes => exact ⟨_, false, .nul, by simp [succs], rfl, rfl⟩
  | frameNo => exact ⟨_, false, .nul, by simp [succs], rfl, rfl⟩
  | frameYesBind => exact ⟨_, true, _, by simp [succs], rfl, rfl⟩
  | frameNoBind => exact ⟨_, true, _, by simp [succs], rfl, rfl⟩
  | frameTag _ => exact ⟨_, true, _, by split <;> simp [succs], rfl, rfl⟩
  | frameHandle _ => exact ⟨_, true, _, by cases k <;> simp [succs], rfl, rfl⟩

/-- **The table holds at every goto of a run** (proved): from the entry
(`holds_start`) along each edge (`transfer_holds`), the check giving each
successor's row below the edge's. -/
theorem runGoto_holds {E : List Tm} {K : List (Continuation × Option Target)} {start arity : Nat} {caps : List Tm}
    {comp : ComponentTag} {T : List (Option SlotRow)} (hT : slotTableB K start arity caps.length T = true)
    {l : Nat} {L : List Tm} {d : Tm} (hr : RunGoto E K start arity caps comp l L d) : Holds T caps l L := by
  induction hr with
  | start recv self args => exact holds_start hT recv self args
  | @next l l' L L' d d' t k x h h' _ hK hs ih =>
    obtain ⟨row, hrow, hL⟩ := ih
    obtain ⟨y, b, v, hy, rfl, rfl⟩ := frame_goto_succ hs
    have hl : l < K.length := (List.getElem?_eq_some_iff.mp hK).1
    simp only [slotTableB, Bool.and_eq_true] at hT
    have hn := (List.all_eq_true.mp hT.2) l (List.mem_range.mpr hl)
    rw [hrow, hK] at hn
    have hy' := (List.all_eq_true.mp hn) (y, b) hy
    cases hr' : T.getD y.label none with
    | none => rw [hr'] at hy'; simp at hy'
    | some r =>
      rw [hr'] at hy'
      exact ⟨r, hr', fun i k hk => transfer_holds (v := v) (d := d) hL i k (rowLeB_sound hy' i k hk)⟩

/-- **A call of a native at a node** (the draft's `nativeAt`, for a callee
read from a slot): the node's expression invokes the position its row in
the code's table gives an outside capture, `outside` telling which captures
are outside slots. -/
def nativeAtB (E : List Tm) (T : List (Option SlotRow)) (outside : Nat → Bool) (l : Nat) : Bool :=
  match E[l]?, T.getD l none with
  | some (.invoke (.var j) _ _), some row => match row.getD j none with
    | some k => outside k
    | none => false
  | _, _ => false

/-- **The callee at a node `nativeAtB` decides is the realm's code**
(proved, conditional on the captures): at a goto of a run of a closure
whose code's table the check accepts, entering a node the decision reads as
a call of a native gives a term invoking an outside capture `c` of the
closure; where every outside capture holds a value of the realm's code at
the heap, `c` is a closure of the realm's code where it is a function. -/
theorem nativeAt_sound {E : List Tm} {K : List (Continuation × Option Target)} {start arity : Nat} {caps : List Tm}
    {comp : ComponentTag} {T : List (Option SlotRow)} {outside : Nat → Bool} {rl : Realm} {h : Heap}
    (hT : slotTableB K start arity caps.length T = true)
    (hrealm : ∀ k c, outside k = true → caps[k]? = some c → FramedSpec.RealmVal rl h c)
    {l : Nat} {L : List Tm} {d : Tm} (hr : RunGoto E K start arity caps comp l L d)
    (hn : nativeAtB E T outside l = true) :
    ∃ j k c r as, E[l]? = some (.invoke (.var j) r as) ∧ outside k = true ∧ caps[k]? = some c ∧
      instantiate 0 (envOf L d) (.var j) = c ∧ ∀ fs cc oid, c = .objAt fs cc oid → cc ≠ .absent → RealmFn rl c := by
  obtain ⟨row, hrow, hL⟩ := runGoto_holds hT hr
  unfold nativeAtB at hn
  split at hn
  · rename_i j r as row' hE hrow'
    rw [hrow] at hrow'
    cases hrow'
    split at hn
    · rename_i k hk
      obtain ⟨c, hc, hLj⟩ := hL j k hk
      exact ⟨j, k, c, r, as, hE, hn, hc, by simp [instantiate, envOf, List.getD_eq_getElem?_getD, hLj],
        (hrealm k c hn hc).1⟩
    · simp at hn
  · simp at hn

end Verification.SourceClaimJson
