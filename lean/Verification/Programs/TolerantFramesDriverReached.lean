import Verification.Programs.TolerantFramesDriverHeadsFuel

/-! # Tolerant frames: the labels the depth-first walk reaches

A node the walk has seen (state other than 0) stays seen, and a marked
head is seen (`HeadsSeen`), round after round (`dfsStep_seen`,
`dfsLoop_seen`). On an empty stack the seen nodes are closed under
successors below the bound (`dfs_closed`): a seen node is done, and a done
node's successors below the bound are heads or done (`DfsInv.finished`).
The start is seen from the walk's start on (`dfsLoop_init_start`). -/
namespace Verification.TolerantFrames
open SinglePass (upd Dfs dfsStep dfsLoop dfsInit nodeSucc)

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

/-! ## The pass's loop heads

`SinglePass.loopHeads` is the marks of `SinglePass.loopHeadsWalk`, the
walk from the start on `SinglePass.dfsFuel`: twice the nodes, their
successors and one more, at least the start's measure. So the walk ends
(`loopHeadsWalk_ends`), the setup's fuel check never refuses
(`loopHeadsRun_ended`), and the marks, read by label, are the walk's heads
and seen nodes, past the bound none (`OutsideClear`). -/

/-- The successors of the first `k` nodes, counted as `dfsFuel` folds them. -/
theorem succCount_nodeSucc (nodes : Array ControlFlow.Node) :
    ∀ k, k ≤ nodes.size → succCount (nodeSucc nodes) k =
      (nodes.toList.take k).foldl (fun acc node =>
        acc + (CertificateProducer.successors node.continuation).length + node.handler.toList.length) 0
  | 0, _ => by simp [succCount]
  | k + 1, hk => by
    rw [succCount, succCount_nodeSucc nodes k (by omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, nodeSucc, List.length_map, List.length_append,
      Array.getElem_toList, getElem!_pos nodes k (by omega)]
    omega

/-- **The walk's fuel covers the start's measure.** -/
theorem dfsFuel_ge (nodes : Array ControlFlow.Node) :
    2 * nodes.size + succCount (nodeSucc nodes) nodes.size ≤ SinglePass.dfsFuel nodes := by
  rw [succCount_nodeSucc nodes nodes.size (Nat.le_refl _), List.take_of_length_le (by simp)]
  unfold SinglePass.dfsFuel
  rw [← Array.foldl_toList]
  omega

/-- **The loop heads' walk ends within its fuel** (`dfsLoop_init_ends`). -/
theorem loopHeadsWalk_ends (nodes : Array ControlFlow.Node) (start : Nat) :
    (SinglePass.loopHeadsWalk nodes start).stack = [] :=
  dfsLoop_init_ends _ _ _ _ (dfsFuel_ge nodes)

/-- **The setup's fuel check passes**: `loopHeadsRun`'s first component. -/
theorem loopHeadsRun_ended (nodes : Array ControlFlow.Node) (start : Nat) :
    (SinglePass.loopHeadsRun nodes start).1 = true := by
  simp [SinglePass.loopHeadsRun, loopHeadsWalk_ends]

/-- **The walk marks no label past the bound** (`OutsideClear`). -/
theorem loopHeadsWalk_clear (nodes : Array ControlFlow.Node) (start : Nat) :
    OutsideClear nodes.size (SinglePass.loopHeadsWalk nodes start) :=
  dfsLoop_clear _ _ _ _ (dfsInit_clear _ _ _)

/-- **`loopHeads`' marks, read by label, are the walk's heads.** -/
theorem loopHeads_heads (nodes : Array ControlFlow.Node) (start t : Nat) :
    (SinglePass.loopHeads nodes start).1[t]?.getD false = (SinglePass.loopHeadsWalk nodes start).heads t := by
  unfold SinglePass.loopHeads SinglePass.Dfs.marks
  by_cases ht : t < nodes.size
  · simp [ht]
  · rw [((loopHeadsWalk_clear nodes start).2 t (by omega)).1]
    simp [ht]

/-- **`loopHeads`' reached flags, read by label, are the walk's seen nodes.** -/
theorem loopHeads_reached (nodes : Array ControlFlow.Node) (start t : Nat) :
    (SinglePass.loopHeads nodes start).2[t]?.getD false = ((SinglePass.loopHeadsWalk nodes start).state t != 0) := by
  unfold SinglePass.loopHeads SinglePass.Dfs.marks
  by_cases ht : t < nodes.size
  · simp [ht]
  · rw [((loopHeadsWalk_clear nodes start).2 t (by omega)).2]
    simp [ht]

/-- `loopHeads`' reached flags: one per node. -/
theorem loopHeads_reached_size (nodes : Array ControlFlow.Node) (start : Nat) :
    (SinglePass.loopHeads nodes start).2.size = nodes.size := by
  simp [SinglePass.loopHeads, SinglePass.Dfs.marks]

/-- **`loopHeads` cuts every cycle of the nodes it reaches**: its marks,
read by label, cut every cycle of the labels its reached flags mark
(`dfs_cuts` at the walk's end, `loopHeadsWalk_ends`). -/
theorem loopHeads_cuts (nodes : Array ControlFlow.Node) (start : Nat) :
    HeadsCutCycles (nodeSucc nodes) nodes.size (fun t => (SinglePass.loopHeads nodes start).2[t]?.getD false)
      (fun t => (SinglePass.loopHeads nodes start).1[t]?.getD false) := by
  obtain ⟨fin, time, hI⟩ := dfsLoop_inv (SinglePass.dfsFuel nodes) _ _ _
    (dfsInit_inv (nodeSucc nodes) nodes.size start)
  have h := dfs_cuts hI (loopHeadsWalk_ends nodes start)
  have hr : (fun t => (SinglePass.loopHeads nodes start).2[t]?.getD false) =
      fun v => (SinglePass.loopHeadsWalk nodes start).state v != 0 := funext (loopHeads_reached nodes start)
  have hh : (fun t => (SinglePass.loopHeads nodes start).1[t]?.getD false) =
      (SinglePass.loopHeadsWalk nodes start).heads := funext (loopHeads_heads nodes start)
  rw [hr, hh]
  exact h

/-- **`loopHeads`' reached nodes are closed under successors below the
bound, and hold the start where it is below the bound**
(`dfsLoop_init_closed` at `dfsFuel`). -/
theorem loopHeads_closed (nodes : Array ControlFlow.Node) (start : Nat) :
    (∀ v w, (SinglePass.loopHeads nodes start).2[v]?.getD false = true → w ∈ nodeSucc nodes v → w < nodes.size →
      (SinglePass.loopHeads nodes start).2[w]?.getD false = true) ∧
    (start < nodes.size → (SinglePass.loopHeads nodes start).2[start]?.getD false = true) := by
  obtain ⟨-, hc, hs⟩ := dfsLoop_init_closed (nodeSucc nodes) nodes.size start _ (dfsFuel_ge nodes)
  change ∀ v w, (SinglePass.loopHeadsWalk nodes start).state v ≠ 0 → w ∈ nodeSucc nodes v → w < nodes.size →
    (SinglePass.loopHeadsWalk nodes start).state w ≠ 0 at hc
  change _ → (SinglePass.loopHeadsWalk nodes start).state start ≠ 0 at hs
  refine ⟨fun v w hv hw hwn => ?_, fun h => ?_⟩
  · rw [loopHeads_reached] at hv ⊢
    simpa using hc v w (by simpa using hv) hw hwn
  · rw [loopHeads_reached]; simpa using hs h

end Verification.TolerantFrames
