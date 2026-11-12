import Verification.Programs.TolerantFramesDriverHeads

/-! # Tolerant frames: the depth-first walk ends within its fuel

The rounds of `dfsStep` decrease a measure (`dfsMeasure`): each frame
counts one and one per successor it has left to examine, each new node
below the bound two and one per successor. Popping a frame takes one off,
examining a successor takes one off, pushing a new node takes two off (its
weight as a new node is its frame's weight and one more). So the walk
empties its stack within as many rounds as its start's measure
(`dfsLoop_ends`), at most twice the nodes plus their successors
(`dfsInit_measure`). -/
namespace Verification.TolerantFrames

section DfsFuel

/-- The weight of the new nodes below `k`: two and one per successor each. -/
def zeroWeight (succ : Nat → List Nat) (st : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => zeroWeight succ st k + (if st k = 0 then 2 + (succ k).length else 0)

/-- The successors of the nodes below `k`, counted. -/
def succCount (succ : Nat → List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => succCount succ k + (succ k).length

/-- The frames' weight: one and one per successor left, each. -/
def framesWeight : List (Nat × List Nat) → Nat
  | [] => 0
  | (_, ws) :: rest => 1 + ws.length + framesWeight rest

/-- **The walk's measure**: the frames' weight and the new nodes' below `n`. -/
def dfsMeasure (succ : Nat → List Nat) (n : Nat) (σ : Dfs) : Nat :=
  framesWeight σ.stack + zeroWeight succ σ.state n

/-- Marking a node with a state other than new takes its weight off where it
was new and below the bound. -/
theorem zeroWeight_upd (succ : Nat → List Nat) (st : Nat → Nat) (x b : Nat) (hb : b ≠ 0) :
    ∀ k, zeroWeight succ (upd st x b) k + (if x < k ∧ st x = 0 then 2 + (succ x).length else 0) =
      zeroWeight succ st k
  | 0 => by simp [zeroWeight]
  | k + 1 => by
    have ih := zeroWeight_upd succ st x b hb k
    simp only [zeroWeight]
    by_cases hx : k = x
    · subst hx
      have hn : ¬ (k < k ∧ st k = 0) := fun h => Nat.lt_irrefl _ h.1
      rw [if_neg hn] at ih
      rw [upd_self, if_neg hb]
      by_cases hz : st k = 0
      · rw [if_pos ⟨Nat.lt_succ_self k, hz⟩, if_pos hz]; omega
      · rw [if_neg (fun h => hz h.2), if_neg hz]; omega
    · rw [upd_ne b hx]
      have e : (if x < k + 1 ∧ st x = 0 then 2 + (succ x).length else 0) =
          (if x < k ∧ st x = 0 then 2 + (succ x).length else 0) := by
        by_cases hz : x < k ∧ st x = 0
        · rw [if_pos hz, if_pos ⟨by have := hz.1; omega, hz.2⟩]
        · rw [if_neg hz, if_neg (fun h => hz ⟨by have := h.1; omega, h.2⟩)]
      rw [e]
      omega

theorem zeroWeight_upd_le (succ : Nat → List Nat) (st : Nat → Nat) (x b : Nat) (hb : b ≠ 0) (k : Nat) :
    zeroWeight succ (upd st x b) k ≤ zeroWeight succ st k := by
  have := zeroWeight_upd succ st x b hb k
  omega

/-- The new nodes' weight with every node new: two per node and its
successors. -/
theorem zeroWeight_zero (succ : Nat → List Nat) :
    ∀ k, zeroWeight succ (fun _ => 0) k = 2 * k + succCount succ k
  | 0 => rfl
  | k + 1 => by simp only [zeroWeight, succCount, if_true, zeroWeight_zero succ k]; omega

/-- A stack with a frame weighs at least one. -/
theorem framesWeight_pos {st : List (Nat × List Nat)} (h : st ≠ []) : 0 < framesWeight st := by
  cases st with
  | nil => exact absurd rfl h
  | cons f rest => obtain ⟨v, ws⟩ := f; simp only [framesWeight]; omega

/-- **A round decreases the measure.** -/
theorem dfsStep_measure {succ : Nat → List Nat} {n : Nat} {σ σ' : Dfs} (h : dfsStep succ n σ = some σ') :
    dfsMeasure succ n σ' < dfsMeasure succ n σ := by
  obtain ⟨heads, state, stack⟩ := σ
  unfold dfsStep at h
  unfold dfsMeasure
  simp only at h ⊢
  match stack, h with
  | [], h => cases h
  | (v, []) :: rest, h =>
    simp only [Option.some.injEq] at h
    subst h
    have := zeroWeight_upd_le succ state v 2 (by decide) n
    simp only [framesWeight, List.length_nil]
    omega
  | (v, w :: ws) :: rest, h =>
    simp only at h
    split at h
    · rename_i hw
      split at h
      · rename_i hz
        simp only [Option.some.injEq] at h
        subst h
        have := zeroWeight_upd succ state w 1 (by decide) n
        rw [if_pos ⟨hw, hz⟩] at this
        simp only [framesWeight, List.length_cons]
        omega
      · split at h <;>
        · simp only [Option.some.injEq] at h
          subst h
          simp only [framesWeight, List.length_cons]
          omega
    · simp only [Option.some.injEq] at h
      subst h
      simp only [framesWeight, List.length_cons]
      omega

/-- A round is refused only on an empty stack. -/
theorem dfsStep_none {succ : Nat → List Nat} {n : Nat} {σ : Dfs} (h : dfsStep succ n σ = none) : σ.stack = [] := by
  obtain ⟨heads, state, stack⟩ := σ
  unfold dfsStep at h
  simp only at h ⊢
  match stack, h with
  | [], _ => rfl
  | (v, []) :: rest, h => cases h
  | (v, w :: ws) :: rest, h =>
    simp only at h
    split at h
    · split at h
      · cases h
      · split at h <;> cases h
    · cases h

/-- **The walk ends within its measure**: from a state of measure at most
`k`, `k` rounds empty the stack. -/
theorem dfsLoop_ends (succ : Nat → List Nat) (n : Nat) :
    ∀ (k : Nat) (σ : Dfs), dfsMeasure succ n σ ≤ k → (dfsLoop succ n k σ).stack = []
  | 0, σ, h => by
    simp only [dfsLoop]
    cases hst : σ.stack with
    | nil => rfl
    | cons f rest =>
      have := framesWeight_pos (st := f :: rest) (List.cons_ne_nil _ _)
      unfold dfsMeasure at h
      rw [hst] at h
      omega
  | k + 1, σ, h => by
    simp only [dfsLoop]
    cases hs : dfsStep succ n σ with
    | none => exact dfsStep_none hs
    | some σ' =>
      have := dfsStep_measure hs
      exact dfsLoop_ends succ n k σ' (by omega)

/-- **The start's measure**: at most twice the nodes below the bound and
their successors. -/
theorem dfsInit_measure (succ : Nat → List Nat) (n start : Nat) :
    dfsMeasure succ n (dfsInit succ n start) ≤ 2 * n + succCount succ n := by
  unfold dfsInit dfsMeasure
  split
  · rename_i hs
    have h := zeroWeight_upd succ (fun _ => 0) start 1 (by decide) n
    rw [if_pos ⟨hs, rfl⟩, zeroWeight_zero] at h
    simp only [framesWeight]
    omega
  · simp only [framesWeight, zeroWeight_zero]
    omega

/-- **The walk from the start ends** at every fuel of at least twice the
nodes and their successors. -/
theorem dfsLoop_init_ends (succ : Nat → List Nat) (n start k : Nat) (hk : 2 * n + succCount succ n ≤ k) :
    (dfsLoop succ n k (dfsInit succ n start)).stack = [] :=
  dfsLoop_ends succ n k _ (Nat.le_trans (dfsInit_measure succ n start) hk)

/-- **The walk touches no label past its bound**: where every frame's node
is below `n`, and past `n` no head is marked and every state is new, a
round keeps both. -/
def OutsideClear (n : Nat) (σ : Dfs) : Prop :=
  (∀ f ∈ σ.stack, f.1 < n) ∧ ∀ t, n ≤ t → σ.heads t = false ∧ σ.state t = 0

theorem dfsStep_clear {succ : Nat → List Nat} {n : Nat} {σ σ' : Dfs} (hc : OutsideClear n σ)
    (h : dfsStep succ n σ = some σ') : OutsideClear n σ' := by
  obtain ⟨heads, state, stack⟩ := σ
  obtain ⟨hf, ho⟩ := hc
  unfold dfsStep at h
  simp only at h hf ho
  match stack, h, hf with
  | [], h, _ => cases h
  | (v, []) :: rest, h, hf =>
    simp only [Option.some.injEq] at h
    subst h
    have hv : v < n := hf _ (List.mem_cons_self ..)
    refine ⟨fun f hm => hf f (List.mem_cons_of_mem _ hm), fun t ht => ?_⟩
    dsimp only
    rw [upd_ne _ (by omega)]
    exact ho t ht
  | (v, w :: ws) :: rest, h, hf =>
    have hrest : ∀ f ∈ (v, ws) :: rest, f.1 < n := by
      intro f hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hf (v, w :: ws) (List.mem_cons_self ..)
      · exact hf f (List.mem_cons_of_mem _ hm)
    simp only at h
    split at h
    · rename_i hw
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun f hm => ?_, fun t ht => ?_⟩
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact hw
          · exact hrest f hm
        · dsimp only; rw [upd_ne _ (by omega)]; exact ho t ht
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact ⟨hrest, fun t ht => by dsimp only; rw [upd_ne _ (by omega)]; exact ho t ht⟩
        · simp only [Option.some.injEq] at h
          subst h
          exact ⟨hrest, ho⟩
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨hrest, ho⟩

theorem dfsLoop_clear (succ : Nat → List Nat) (n : Nat) :
    ∀ (k : Nat) (σ : Dfs), OutsideClear n σ → OutsideClear n (dfsLoop succ n k σ)
  | 0, _, h => h
  | k + 1, σ, h => by
    simp only [dfsLoop]
    cases hs : dfsStep succ n σ with
    | none => exact h
    | some σ' => exact dfsLoop_clear succ n k σ' (dfsStep_clear h hs)

theorem dfsInit_clear (succ : Nat → List Nat) (n start : Nat) : OutsideClear n (dfsInit succ n start) := by
  unfold dfsInit
  split
  · rename_i hs
    refine ⟨fun f hm => by simp at hm; subst hm; exact hs, fun t ht => ⟨rfl, ?_⟩⟩
    dsimp only
    rw [upd_ne _ (show t ≠ start by omega)]
  · exact ⟨fun f hm => by simp at hm, fun _ _ => ⟨rfl, rfl⟩⟩

end DfsFuel

end Verification.TolerantFrames
