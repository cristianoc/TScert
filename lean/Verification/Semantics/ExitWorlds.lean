import Verification.Semantics.ExitPosts

/-! # The exit world of a guarantee

A safety derivation chooses the world of each state it reaches (`Safe`), so
two derivations of one computation reach the same heaps and terms
(`Step_det`) at worlds of their own. Their guarantees conjoin at one exit
state where the second's does not depend on which admissible world, at that
heap and budget, the exit is read at (`IndependentFrom`): then both hold at
the first derivation's worlds (`SafePostExcV.cross_independent`).

- **Monotonicity** (`Parity.Holds.mono_exit`): every two-state formula true
  at an exit stays true where the exit is replaced by a state admissible
  from it with the same heap; such a state has fewer admissible futures.
- **Independence** (`Parity.Holds.exit_heap`): a formula reading its exit
  only through the exit heap (`FormulaF.exitHeapOnly`) holds at every exit
  state admissible from the entry with that heap. The exit's assertions and
  a transport certifying rigid images read the exit's futures, which depend
  on its world: two worlds a heap satisfies need have no common extension,
  where they give one location different contracts.
- **Exits** (`Exits.independent`): a specification whose completion's
  postconditions read the exit only through its heap has its guarantee at
  that completion independent of the exit world. -/

namespace Verification.Parity
open Verification Footprints TolerantFrames

/-! ## Monotonicity in the exit state -/

/-- **An assertion true at a state is true at every state admissible from it
with the same heap** (the note, §4, "Satisfaction"): atoms, separation,
apartness and freshness read the heap; a box quantifies over the actions
from the state, and each action from the second state is one from the
first. -/
theorem satNode.mono_exit {nodes : Array AssertionNode} {s u : IndexedHeap} (ha : Admissible s u)
    (hh : s.h = u.h) : ∀ (i : Nat) (η : Env) (m : Nat), satNode nodes i η m s → satNode nodes i η m u := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    have step : ∀ (j : Nat) (η : Env) (m : Nat), (if _ : j < i then satNode nodes j η m s else False) →
        (if _ : j < i then satNode nodes j η m u else False) := by
      intro j η m hj
      by_cases hji : j < i
      · rw [dif_pos hji] at hj ⊢; exact ih j hji η m hj
      · rw [dif_neg hji] at hj; exact hj.elim
    intro η m hs
    rw [satNode] at hs ⊢
    cases hn : nodes[i]? with
    | none => rw [hn] at hs; exact hs.elim
    | some node =>
      rw [hn] at hs
      cases node with
      | truth => exact hs
      | falsity => exact hs
      | atom a => rw [← hh]; exact hs
      | and l r => exact ⟨step _ _ _ hs.1, step _ _ _ hs.2⟩
      | guarded g b => exact hs.imp (step _ _ _) (step _ _ _)
      | existsValue b => obtain ⟨v, hv⟩ := hs; exact ⟨v, step _ _ _ hv⟩
      | separated p q => rw [← hh]; exact hs
      | apart p q => rw [← hh]; exact hs
      | fresh p => rw [← hh]; exact hs
      | box Φ b =>
        intro s' ⟨hadm, hpost⟩
        exact hs s' ⟨WorldReach.trans ha hadm, by rw [hh]; exact hpost⟩

/-- A two-state variable reads the exit only through its heap. -/
theorem stepValue_after_heap {t : TwoState} {u : IndexedHeap} (hh : t.after.h = u.h) :
    stepValue { t with after := u } = stepValue t := by
  funext x
  cases x <;> simp [stepValue, hh]

/-- **An operational post reads the exit only through its heap.** -/
theorem OperationPostF.holds_after_heap {t : TwoState} {u : IndexedHeap} (hh : t.after.h = u.h)
    (q : OperationPost) : q.Holds { t with after := u } ↔ q.Holds t := by
  cases q with
  | fact p l F => cases p <;> simp [OperationPostF.Holds, TwoState.state, TwoState.env, hh]
  | _ => simp [OperationPostF.Holds, hh]

/-- **Monotonicity in the exit state**: every two-state formula true at an
exit is true where the exit is replaced by a state admissible from it with
the same heap, entry, environments and mark fixed. A transition composes
admissibility; a transport's current agreement reads the heap, and each
future of the replacement is a future of the exit; an assertion at the exit
is monotone (`satNode.mono_exit`). -/
theorem Holds.mono_exit {arena : AssertionArena} {t : TwoState} {u : IndexedHeap}
    (ha : Admissible t.after u) (hh : t.after.h = u.h) :
    ∀ {F : Formula}, Holds arena t F → Holds arena { t with after := u } F
  | .at .before _, h => h
  | .at .after _, h => satNode.mono_exit ha hh _ _ _ h
  | .transition _, h => ⟨WorldReach.trans h.1 ha, by rw [← hh]; exact h.2⟩
  | .operation q, h => (OperationPostF.holds_after_heap hh q).mpr h
  | .linear F, h => by show HeapKnowledge.FactAt (stepValue _) F; rw [stepValue_after_heap hh]; exact h
  | .defined v, h => by show (stepValue _ v).isSome; rw [stepValue_after_heap hh]; exact h
  | .transport _, h => ⟨by rw [← hh]; exact h.1, fun s' hs' => h.2 s' (WorldReach.trans ha hs')⟩
  | .and _ _, h => ⟨Holds.mono_exit ha hh h.1, Holds.mono_exit ha hh h.2⟩
  | .truth, h => h
  | .falsity, h => h

/-! ## Independence of the exit world -/

/-- **A formula reading its exit only through the exit heap**: no assertion
at the exit, whose boxes read the exit's futures, and transports certifying
no rigid image, whose agreement under a box then holds at every heap
(`Substitution.Holds.box`). `stable` gives a transport's certified slots. -/
def FormulaF.exitHeapOnly {S T : Type} (stable : T → List Nat) : FormulaF S T → Bool
  | .at .after _ => false
  | .transport θ => (stable θ).isEmpty
  | .and F G => F.exitHeapOnly stable && G.exitHeapOnly stable
  | _ => true

theorem FormulaF.exitHeapOnly_map {S S' T T' : Type} (f : S → S') (g : T → T') (stable : T' → List Nat)
    (F : FormulaF S T) : (F.map f g).exitHeapOnly stable = F.exitHeapOnly (stable ∘ g) := by
  induction F with
  | «at» p _ => cases p <;> rfl
  | and F G ihF ihG => simp only [FormulaF.map, FormulaF.exitHeapOnly, ihF, ihG]
  | _ => rfl

/-- **A formula reading its exit only through the exit heap holds at every
exit state admissible from the entry with that heap.** -/
theorem Holds.exit_heap {arena : AssertionArena} {t : TwoState} {u : IndexedHeap}
    (ha : Admissible t.before u) (hh : t.after.h = u.h) :
    ∀ {F : Formula}, F.exitHeapOnly Substitution.stable = true → Holds arena t F →
      Holds arena { t with after := u } F
  | .at .before _, _, h => h
  | .transition _, _, h => ⟨ha, by rw [← hh]; exact h.2⟩
  | .operation q, _, h => (OperationPostF.holds_after_heap hh q).mpr h
  | .linear F, _, h => by show HeapKnowledge.FactAt (stepValue _) F; rw [stepValue_after_heap hh]; exact h
  | .defined v, _, h => by show (stepValue _ v).isSome; rw [stepValue_after_heap hh]; exact h
  | .transport θ, hF, h => by
    have hst : θ.stable = [] := List.isEmpty_iff.mp hF
    exact ⟨by rw [← hh]; exact h.1, fun s' _ => Substitution.Holds.box hst h.1 s'.h⟩
  | .and _ _, hF, h => by
    simp only [FormulaF.exitHeapOnly, Bool.and_eq_true] at hF
    exact ⟨Holds.exit_heap ha hh hF.1 h.1, Holds.exit_heap ha hh hF.2 h.2⟩
  | .truth, _, h => h
  | .falsity, _, h => h

/-! ## The entry state -/

/-- A two-state variable reads the entry only through its heap. -/
theorem stepValue_before_heap {t : TwoState} {u : IndexedHeap} (hh : t.before.h = u.h) :
    stepValue { t with before := u } = stepValue t := by
  funext x
  cases x <;> simp [stepValue, hh]

/-- **An operational post reads the entry only through its heap.** -/
theorem OperationPostF.holds_before_heap {t : TwoState} {u : IndexedHeap} (hh : t.before.h = u.h)
    (q : OperationPost) : q.Holds { t with before := u } ↔ q.Holds t := by
  cases q with
  | fact p l F => cases p <;> simp [OperationPostF.Holds, TwoState.state, TwoState.env, hh]
  | _ => simp [OperationPostF.Holds, hh]

/-- **A formula referencing no arena node holds from an earlier entry with
the same heap**: an entry from which the original is admissible. A
transition composes admissibility; every other formula reads the entry only
through its heap. -/
theorem Holds.entry_back {arena : AssertionArena} {t : TwoState} {u : IndexedHeap}
    (ha : Admissible u t.before) (hh : t.before.h = u.h) :
    ∀ {F : Formula}, F.arenaFree = true → Holds arena t F → Holds arena { t with before := u } F
  | .transition _, _, h => ⟨WorldReach.trans ha h.1, by rw [← hh]; exact h.2⟩
  | .operation q, _, h => (OperationPostF.holds_before_heap hh q).mpr h
  | .linear F, _, h => by show HeapKnowledge.FactAt (stepValue _) F; rw [stepValue_before_heap hh]; exact h
  | .defined v, _, h => by show (stepValue _ v).isSome; rw [stepValue_before_heap hh]; exact h
  | .transport _, _, h => h
  | .and _ _, hF, h => by
    simp only [FormulaF.arenaFree, Bool.and_eq_true] at hF
    exact ⟨Holds.entry_back ha hh hF.1 h.1, Holds.entry_back ha hh hF.2 h.2⟩
  | .truth, _, h => h
  | .falsity, _, h => h

end Verification.Parity

namespace Verification.CallEffects
open Verification Footprints Parity TolerantFrames HeapObservations

/-- **A postcondition independent of the admissible exit world** at a fixed
heap and budget: at any two states admissible from `s` with the same budget
and heap it holds of a value at one exactly where it holds at the other. -/
def IndependentFrom (s : IndexedHeap) (Q : WPost) : Prop :=
  ∀ u v : IndexedHeap, Admissible s u → Admissible s v → u.n = v.n → u.h = v.h →
    ∀ z, Q u.n u.W u.h z ↔ Q v.n v.W v.h z

/-- **Two derivations of one computation conjoin their guarantees at the
first's worlds** where the second's are independent of the exit world: both
take the same steps (`Step_det`) and raise the same value (`Raises_det`),
each reached world admissible from the common entry; the result families
combine as `CrossCompatUpTo` states. -/
theorem SafePostExcV.cross_independent {Ξ B C D : Fam} {Q Q' : WPost} {R R' : WExcV} (s : IndexedHeap)
    (hc : CrossCompatUpTo s.n B C D) (hq : IndependentFrom s Q') (hr : IndependentFrom s R') {t : Tm}
    (ha : SafePostExcV Ξ B Q R s.n s.W s.h t) (hb : SafePostExcV Ξ C Q' R' s.n s.W s.h t) :
    SafePostExcV Ξ D (fun k W h v => Q k W h v ∧ Q' k W h v) (fun k W h v => R k W h v ∧ R' k W h v)
      s.n s.W s.h t := by
  suffices H : ∀ (n : Nat) (hle : n ≤ s.n) (W W' : WorldT n) (h : Heap) (t : Tm),
      WExt (trunc n hle s.W) W → WExt (trunc n hle s.W) W' → WorldAdm W → WorldAdm W' →
      HeapOk n W h → HeapOk n W' h → SafePostExcV Ξ B Q R n W h t → SafePostExcV Ξ C Q' R' n W' h t →
      SafePostExcV Ξ D (fun k W h v => Q k W h v ∧ Q' k W h v) (fun k W h v => R k W h v ∧ R' k W h v)
        n W h t from
    H s.n (Nat.le_refl _) s.W s.W s.h t (by rw [trunc_id]; exact WExt_refl _)
      (by rw [trunc_id]; exact WExt_refl _) s.adm s.adm s.ok s.ok ha hb
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ hs _; exact hs
  | succ p ih =>
    intro hle W W' h t hx hx' hw hw' hok hok' hs1 hs2
    obtain ⟨hrf, hs1⟩ := hs1
    obtain ⟨-, hs2⟩ := hs2
    refine ⟨hrf, ?_⟩
    let u : IndexedHeap := ⟨p + 1, W, h, Nat.succ_pos _, hw, hok⟩
    let v : IndexedHeap := ⟨p + 1, W', h, Nat.succ_pos _, hw', hok'⟩
    have hu : Admissible s u := ⟨hle, hx⟩
    have hv : Admissible s v := ⟨hle, hx'⟩
    have ext : ∀ {Z : WorldT p} {X : WorldT (p + 1)}, WExt (trunc (p + 1) hle s.W) X →
        WExt (trunc p (Nat.le_succ p) X) Z → WExt (trunc p (by omega) s.W) Z := by
      intro Z X hX hZ
      simpa only [trunc_trunc] using WExt_trans (WExt_trunc (Nat.le_succ p) hX) hZ
    rcases hs1 with (⟨hv1, hBv, hQ⟩ | ⟨e1, hra1, hsc1, hξ1, hR1⟩) | ⟨Z, h1, t1, hz, huz, hst1, hok1, hcont1⟩ <;>
    rcases hs2 with (⟨hv2, hCv, hQ2⟩ | ⟨e2, hra2, -, -, hR2⟩) | ⟨Z', h2, t2, hz', huz', hst2, hok2, hcont2⟩
    · exact .inl (.inl ⟨hv1, hc (p + 1) hle W W' h hok hok' t hBv hCv, hQ, (hq u v hu hv rfl rfl t).mpr hQ2⟩)
    · rw [raises_not_val hra2] at hv1; cases hv1
    · exact absurd hst2 (value_no_step hv1)
    · rw [raises_not_val hra1] at hv2; cases hv2
    · cases Raises_det hra1 hra2
      exact .inl (.inr ⟨e1, hra1, hsc1, hξ1, hR1, (hr u v hu hv rfl rfl e1).mpr hR2⟩)
    · exact absurd hst2 (raises_no_step hra1)
    · exact absurd hst1 (value_no_step hv2)
    · exact absurd hst1 (raises_no_step hra2)
    · obtain ⟨rfl, rfl⟩ := Step_det hst1 hst2
      exact .inr ⟨Z, h1, t1, hz, huz, hst1, hok1,
        ih (by omega) Z Z' h1 t1 (ext hx hz) (ext hx' hz') huz huz' hok1 hok2 hcont1 hcont2⟩

/-- Whether an exit schema's postconditions read the exit only through its
heap (`FormulaF.exitHeapOnly`). -/
def ExitSchema.exitHeapOnly (q : ExitSchema) : Bool := q.ensures.all (·.exitHeapOnly TransportSchema.stable)

/-- **Whether both exits of a schema read the exit through its heap
alone** (`ExitSchema.exitHeapOnly`): the condition under which its
guarantee is independent of the exit world (`Exits.independent`). -/
def Exits.exitHeapOnly (x : Exits ExitSchema) : Bool := x.normal.exitHeapOnly && x.exceptional.exitHeapOnly

theorem Exits.exitHeapOnly_get {x : Exits ExitSchema} (h : x.exitHeapOnly = true) (c : Completion) :
    (x.get c).exitHeapOnly = true := by
  simp only [Exits.exitHeapOnly, Bool.and_eq_true] at h
  cases c
  · exact h.1
  · exact h.2

/-- **A completion's guarantee is kept at every exit state admissible from
the entry with the same heap**, where its schema's postconditions read the
exit only through its heap: the frame reads the heaps, and each instantiated
postcondition holds there (`Parity.Holds.exit_heap`). -/
theorem Exits.exitPost_exit_heap {x : Exits ExitSchema} {c : Completion} (hx : (x.get c).exitHeapOnly = true)
    {r : Tm} {args : List Tm} {s s' u : IndexedHeap} {v : Tm} (ha : Admissible s u) (hh : s'.h = u.h)
    (hp : x.exitPost c r args s s' v) : x.exitPost c r args s u v := by
  have hens : ∀ F ∈ (x.get c).ensures, Holds AssertionArena.empty (callState r args v s.h.length s s')
      (instantiateFormula (x.callInstantiation args.length) F) := Exits.exitPost_ensures hp
  refine ⟨⟨ha, ?_⟩, ?_⟩
  · have h2 := hp.1.2
    simp only [callState] at h2 ⊢
    rw [← hh]; exact h2
  have hmem : ∀ F ∈ ((x.atArity args.length).get c).ensures, ∃ G ∈ (x.get c).ensures,
      F = instantiateFormula (x.callInstantiation args.length) G := by
    intro F hF
    cases c <;> exact List.mem_map.mp hF |>.imp fun G hG => ⟨hG.1, hG.2.symm⟩
  intro F hF
  obtain ⟨G, hG, rfl⟩ := hmem F hF
  have hGo : G.exitHeapOnly TransportSchema.stable = true := List.all_eq_true.mp hx G hG
  refine Holds.exit_heap (t := callState r args v s.h.length s s') ha hh ?_ (hens G hG)
  rw [instantiateFormula, FormulaF.exitHeapOnly_map]
  exact hGo

/-- **A completion's guarantee is independent of the exit world** where its
schema's postconditions read the exit only through its heap. -/
theorem Exits.independent {x : Exits ExitSchema} {c : Completion} (hx : (x.get c).exitHeapOnly = true)
    (r : Tm) (args : List Tm) (s : IndexedHeap) :
    IndependentFrom s (x.exitPostW c r args s.W s.h) := by
  intro u v hu hv _ hh z
  rw [Exits.exitPostW_iff x c r args s u z, Exits.exitPostW_iff x c r args s v z]
  exact ⟨Exits.exitPost_exit_heap hx hv hh, Exits.exitPost_exit_heap hx hu hh.symm⟩

/-- **A guarantee referencing no arena node holds from an earlier entry with
the same heap** (`Parity.Holds.entry_back`); the entry heap fixes the mark. -/
theorem Exits.exitPost_entry {x : Exits ExitSchema} {c : Completion} (hx : (x.get c).arenaFree = true)
    {r : Tm} {args : List Tm} {s u s' : IndexedHeap} {v : Tm} (ha : Admissible u s) (hh : s.h = u.h)
    (hp : x.exitPost c r args s s' v) : x.exitPost c r args u s' v := by
  have hens : ∀ F ∈ (x.get c).ensures, Holds AssertionArena.empty (callState r args v s.h.length s s')
      (instantiateFormula (x.callInstantiation args.length) F) := Exits.exitPost_ensures hp
  refine ⟨⟨WorldReach.trans ha hp.1.1, ?_⟩, ?_⟩
  · have h2 := hp.1.2
    simp only [callState] at h2 ⊢
    rw [← hh]; exact h2
  have hmem : ∀ F ∈ ((x.atArity args.length).get c).ensures, ∃ G ∈ (x.get c).ensures,
      F = instantiateFormula (x.callInstantiation args.length) G := by
    intro F hF
    cases c <;> exact List.mem_map.mp hF |>.imp fun G hG => ⟨hG.1, hG.2.symm⟩
  intro F hF
  obtain ⟨G, hG, rfl⟩ := hmem F hF
  have hl : u.h.length = s.h.length := by rw [hh]
  rw [hl]
  refine Holds.entry_back (t := callState r args v s.h.length s s') ha hh ?_ (hens G hG)
  rw [instantiateFormula, FormulaF.arenaFree_map]
  exact List.all_eq_true.mp hx G hG

end Verification.CallEffects
