import Verification.Programs.TolerantFramesDriverHeadsFuel

/-! # Tolerant frames: the labels the depth-first walk reaches

A node the walk has seen (state other than 0) stays seen, and a marked
head is seen (`HeadsSeen`), round after round (`dfsStep_seen`,
`dfsLoop_seen`). On an empty stack the seen nodes are closed under
successors below the bound (`dfs_closed`): a seen node is done, and a done
node's successors below the bound are heads or done (`DfsInv.finished`).
The start is seen from the walk's start on (`dfsLoop_init_start`). -/
namespace Verification.TolerantFrames

/-- Every marked head has been seen. -/
def HeadsSeen (σ : Dfs) : Prop := ∀ w, σ.heads w = true → σ.state w ≠ 0

/-- **A round keeps every seen node seen and every head seen.** -/
theorem dfsStep_seen {succ : Nat → List Nat} {n : Nat} {σ σ' : Dfs} (hs : dfsStep succ n σ = some σ') :
    (∀ v, σ.state v ≠ 0 → σ'.state v ≠ 0) ∧ (HeadsSeen σ → HeadsSeen σ') := by
  unfold dfsStep at hs
  split at hs
  · cases hs
  · cases hs
    refine ⟨fun x hx => ?_, fun hH x hx => ?_⟩
    · dsimp only [upd]; split <;> simp_all
    · have := hH x hx; dsimp only [upd]; split <;> simp_all
  · split at hs
    · split at hs
      · cases hs
        rename_i w _ _ _ hw0
        refine ⟨fun x hx => ?_, fun hH x hx => ?_⟩
        · dsimp only [upd]; split <;> simp_all
        · have := hH x hx; dsimp only [upd]; split <;> simp_all
      · split at hs
        · cases hs
          refine ⟨fun x hx => hx, fun hH x hx => ?_⟩
          simp only [upd] at hx ⊢
          split at hx
          · subst_vars; omega
          · exact hH x hx
        · cases hs; exact ⟨fun x hx => hx, fun hH => hH⟩
    · cases hs; exact ⟨fun x hx => hx, fun hH => hH⟩

/-- **The rounds on fuel keep every seen node seen and every head seen.** -/
theorem dfsLoop_seen {succ : Nat → List Nat} {n : Nat} :
    ∀ (k : Nat) (σ : Dfs), (∀ v, σ.state v ≠ 0 → (dfsLoop succ n k σ).state v ≠ 0) ∧
      (HeadsSeen σ → HeadsSeen (dfsLoop succ n k σ))
  | 0, _ => ⟨fun _ h => h, fun h => h⟩
  | k + 1, σ => by
    unfold dfsLoop
    split
    · exact ⟨fun _ h => h, fun h => h⟩
    · rename_i σ' hs
      have h1 := dfsStep_seen hs
      have h2 := dfsLoop_seen (succ := succ) (n := n) k σ'
      exact ⟨fun v hv => h2.1 v (h1.1 v hv), fun hH => h2.2 (h1.2 hH)⟩

/-- **On an empty stack the seen nodes are closed under successors below
the bound**: a seen node is done (`DfsInv.onStack`, `DfsInv.done`), and a
done node's successors below the bound are heads, which are seen, or done. -/
theorem dfs_closed {succ : Nat → List Nat} {n : Nat} {σ : Dfs} {fin : Nat → Option Nat} {time : Nat}
    (hI : DfsInv succ n σ fin time) (hH : HeadsSeen σ) (hempty : σ.stack = []) :
    ∀ v w, σ.state v ≠ 0 → w ∈ succ v → w < n → σ.state w ≠ 0 := by
  intro v w hv hw hwn
  have h1 : σ.state v ≠ 1 := fun h => by have := hI.onStack v h; rw [hempty] at this; simp at this
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((hI.done v).mp (by have := hI.le v; omega))
  rcases hI.finished v t ht w hw hwn with h | ⟨t', ht', -⟩
  · exact hH w h
  · intro h0
    have := (hI.done w).mpr (by rw [ht']; rfl)
    omega

/-- **From the walk's start, the start is seen and every head is seen**,
at every fuel, where the start is below the bound. -/
theorem dfsLoop_init_start (succ : Nat → List Nat) (n start k : Nat) :
    (start < n → (dfsLoop succ n k (dfsInit succ n start)).state start ≠ 0) ∧
      HeadsSeen (dfsLoop succ n k (dfsInit succ n start)) := by
  have h := dfsLoop_seen (succ := succ) (n := n) k (dfsInit succ n start)
  refine ⟨fun hs => h.1 start ?_, h.2 ?_⟩
  · unfold dfsInit; simp [hs, upd_self]
  · intro w hw; unfold dfsInit at hw; split at hw <;> simp at hw

/-- **The walk from the start on enough fuel**: its stack empty, its seen
nodes closed under successors below the bound, the start seen where it is
below the bound (`dfsLoop_init_ends`, `dfs_closed`). -/
theorem dfsLoop_init_closed (succ : Nat → List Nat) (n start k : Nat) (hk : 2 * n + succCount succ n ≤ k) :
    (dfsLoop succ n k (dfsInit succ n start)).stack = [] ∧
      (∀ v w, (dfsLoop succ n k (dfsInit succ n start)).state v ≠ 0 → w ∈ succ v → w < n →
        (dfsLoop succ n k (dfsInit succ n start)).state w ≠ 0) ∧
      (start < n → (dfsLoop succ n k (dfsInit succ n start)).state start ≠ 0) := by
  have hempty := dfsLoop_init_ends succ n start k hk
  obtain ⟨fin, time, hI⟩ := dfsLoop_inv k _ _ _ (dfsInit_inv succ n start)
  have hs := dfsLoop_init_start succ n start k
  exact ⟨hempty, dfs_closed hI hs.2 hempty, hs.1⟩

end Verification.TolerantFrames
