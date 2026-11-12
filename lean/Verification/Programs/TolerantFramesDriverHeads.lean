import Verification.Programs.SinglePass

/-! # Tolerant frames: the loop heads cut every cycle

`SinglePass.loopHeads` marks each target of a retreating edge of a
depth-first walk from the start (`SinglePass.loopHeadsWalk`): the rounds
`SinglePass.dfsStep` on fuel (`SinglePass.dfsLoop`) over the marks, the
node states (0 new, 1 on the stack, 2 done) and a stack of frames, each a
node with its successors not yet examined.

**Every cycle of reached nodes passes through a head** (`dfs_cuts`): with
a ghost finishing time per done node, the rounds keep `DfsInv`: done nodes
are those with a time; each done node's successors below the bound are
heads or done earlier; each frame's examined successors are heads, done, or
nodes of frames above it (`FramesOk`); a node on the stack is a frame's
node, frames' nodes distinct. On an empty stack every reached node is done,
so a non-head edge between reached nodes goes to an earlier time, and no
cycle avoids the heads. -/
namespace Verification.TolerantFrames

section Dfs
open SinglePass (upd Dfs dfsStep dfsLoop dfsInit nodeSucc)

/-- **Each frame's examined successors are fine** (`good`) or nodes of the
frames above it (`above`, the top's none). -/
def FramesOk (succ : Nat → List Nat) (n : Nat) (good : Nat → Prop) : List Nat → List (Nat × List Nat) → Prop
  | _, [] => True
  | above, (v, ws) :: rest =>
    (∃ pre, succ v = pre ++ ws ∧ ∀ w ∈ pre, w < n → good w ∨ w ∈ above) ∧ FramesOk succ n good (v :: above) rest

theorem FramesOk.mono {succ : Nat → List Nat} {n : Nat} {good good' : Nat → Prop} (hg : ∀ w, good w → good' w) :
    ∀ (st : List (Nat × List Nat)) (above above' : List Nat), (∀ w ∈ above, good' w ∨ w ∈ above') →
      FramesOk succ n good above st → FramesOk succ n good' above' st
  | [], _, _, _, _ => trivial
  | (v, ws) :: rest, above, above', ha, ⟨⟨pre, hpre, hw⟩, hr⟩ => by
    refine ⟨⟨pre, hpre, fun w hm hn => ?_⟩, FramesOk.mono hg rest (v :: above) (v :: above') ?_ hr⟩
    · rcases hw w hm hn with h | h
      · exact .inl (hg w h)
      · exact ha w h
    · intro w hm
      rcases List.mem_cons.mp hm with rfl | h
      · exact .inr (List.mem_cons_self ..)
      · rcases ha w h with h' | h'
        · exact .inl h'
        · exact .inr (List.mem_cons_of_mem _ h')

/-- **The walk's invariant**, with the ghost finishing times `fin` below
`time`. -/
structure DfsInv (succ : Nat → List Nat) (n : Nat) (σ : Dfs) (fin : Nat → Option Nat) (time : Nat) : Prop where
  times : ∀ v t, fin v = some t → t < time
  done : ∀ v, σ.state v = 2 ↔ (fin v).isSome = true
  le : ∀ v, σ.state v ≤ 2
  finished : ∀ v t, fin v = some t → ∀ w ∈ succ v, w < n → σ.heads w = true ∨ ∃ t', fin w = some t' ∧ t' < t
  frames : FramesOk succ n (fun w => σ.heads w = true ∨ (fin w).isSome = true) [] σ.stack
  onStack : ∀ w, σ.state w = 1 → w ∈ σ.stack.map (·.1)
  stackOn : ∀ w ∈ σ.stack.map (·.1), σ.state w = 1
  nodup : (σ.stack.map (·.1)).Nodup

theorem upd_self {α : Type} (f : Nat → α) (a : Nat) (b : α) : upd f a b a = b := by simp [upd]

theorem upd_ne {α : Type} {f : Nat → α} {a x : Nat} (b : α) (h : x ≠ a) : upd f a b x = f x := by simp [upd, h]

/-- **A round keeps the invariant**, with the times extended where a node
is done. -/
theorem dfsStep_inv {succ : Nat → List Nat} {n : Nat} {σ σ' : Dfs} {fin : Nat → Option Nat} {time : Nat}
    (hI : DfsInv succ n σ fin time) (hs : dfsStep succ n σ = some σ') :
    ∃ fin' time', DfsInv succ n σ' fin' time' := by
  unfold dfsStep at hs
  split at hs
  · cases hs
  · -- a frame with no successor left: done at `time`
    rename_i v rest hst
    cases hs
    have hv1 : σ.state v = 1 := hI.stackOn v (by simp [hst])
    have hvfin : fin v = none := by
      cases h : fin v with
      | none => rfl
      | some t => have := (hI.done v).mpr (by simp [h]); omega
    have hframes := hI.frames
    rw [hst] at hframes
    obtain ⟨⟨pre, hpre, hpw⟩, hrest⟩ := hframes
    have hpre' : pre = succ v := by simpa using hpre.symm
    have hnd := hI.nodup
    rw [hst] at hnd
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine ⟨upd fin v (some time), time + 1, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro u t hu
      by_cases huv : u = v
      · subst huv; simp only [upd_self] at hu; cases hu; omega
      · simp only [upd_ne _ huv] at hu; have := hI.times u t hu; omega
    · intro u
      by_cases huv : u = v
      · subst huv; simp [upd_self]
      · simp only [upd_ne _ huv]; exact hI.done u
    · intro u
      by_cases huv : u = v
      · subst huv; simp [upd_self]
      · simp only [upd_ne _ huv]; exact hI.le u
    · intro u t hu w hw hwn
      by_cases huv : u = v
      · subst huv
        simp only [upd_self] at hu; cases hu
        rw [← hpre'] at hw
        rcases hpw w hw hwn with h | h
        · rcases h with h | h
          · exact .inl h
          · right
            obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp h
            have hwu : w ≠ u := by intro e; subst e; rw [hvfin] at ht'; cases ht'
            exact ⟨t', by simp only [upd_ne _ hwu]; exact ht', hI.times w t' ht'⟩
        · cases h
      · simp only [upd_ne _ huv] at hu
        rcases hI.finished u t hu w hw hwn with h | ⟨t', ht', hlt⟩
        · exact .inl h
        · right
          have hwv : w ≠ v := by intro e; subst e; rw [hvfin] at ht'; cases ht'
          exact ⟨t', by simp only [upd_ne _ hwv]; exact ht', hlt⟩
    · refine FramesOk.mono (good := fun w => σ.heads w = true ∨ (fin w).isSome = true) ?_ rest [v] [] ?_ hrest
      · intro w h
        rcases h with h | h
        · exact .inl h
        · right
          by_cases hwv : w = v
          · subst hwv; simp [upd_self]
          · simp only [upd_ne _ hwv]; exact h
      · intro w hw
        simp only [List.mem_singleton] at hw
        subst hw
        exact .inl (.inr (by simp [upd_self]))
    · intro w hw
      by_cases hwv : w = v
      · subst hwv; simp [upd_self] at hw
      · simp only [upd_ne _ hwv] at hw
        have := hI.onStack w hw
        rw [hst] at this
        simp only [List.map_cons, List.mem_cons] at this
        rcases this with h | h
        · exact absurd h hwv
        · exact h
    · intro w hw
      have hwv : w ≠ v := fun e => hnd.1 (e ▸ hw)
      simp only [upd_ne _ hwv]
      exact hI.stackOn w (by rw [hst]; exact List.mem_cons_of_mem _ hw)
    · exact hnd.2
  · -- the next successor `w`
    rename_i v w ws rest hst
    have hframes := hI.frames
    rw [hst] at hframes
    obtain ⟨⟨pre, hpre, hpw⟩, hrest⟩ := hframes
    have hpre2 : succ v = (pre ++ [w]) ++ ws := by simpa using hpre
    split at hs
    · rename_i hwn
      split at hs
      · -- new: pushed
        rename_i h0
        cases hs
        refine ⟨fin, time, ⟨hI.times, ?_, ?_, hI.finished, ?_, ?_, ?_, ?_⟩⟩
        · intro u
          by_cases huw : u = w
          · subst huw; simp only [upd_self]
            constructor
            · intro h; cases h
            · intro h; have := (hI.done u).mpr h; omega
          · simp only [upd_ne _ huw]; exact hI.done u
        · intro u
          by_cases huw : u = w
          · subst huw; simp [upd_self]
          · simp only [upd_ne _ huw]; exact hI.le u
        · refine ⟨⟨[], by simp, fun _ h => by cases h⟩, ⟨pre ++ [w], hpre2, fun x hx hxn => ?_⟩, ?_⟩
          · rcases List.mem_append.mp hx with hx | hx
            · rcases hpw x hx hxn with h | h
              · exact .inl h
              · cases h
            · simp only [List.mem_singleton] at hx; subst hx; exact .inr (List.mem_singleton_self _)
          · exact FramesOk.mono (fun _ h => h) rest [v] [v, w]
              (fun x hx => .inr (by simp only [List.mem_singleton] at hx; simp [hx])) hrest
        · intro u hu
          by_cases huw : u = w
          · subst huw; simp
          · simp only [upd_ne _ huw] at hu
            have := hI.onStack u hu
            rw [hst] at this
            simp only [List.map_cons, List.mem_cons] at this ⊢
            exact .inr this
        · intro u hu
          simp only [List.map_cons, List.mem_cons] at hu
          rcases hu with rfl | hu
          · exact upd_self _ _ _
          · have hu' : u ∈ σ.stack.map (·.1) := by rw [hst]; simpa using hu
            have h1 := hI.stackOn u hu'
            have huw : u ≠ w := by intro e; subst e; omega
            simp only [upd_ne _ huw]; exact h1
        · have hnd := hI.nodup
          rw [hst] at hnd
          simp only [List.map_cons] at hnd ⊢
          refine List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩
          have h1 := hI.stackOn w (by rw [hst]; simpa using hm)
          omega
      · split at hs
        · -- on the stack: a head
          rename_i h0 h1
          cases hs
          refine ⟨fin, time, ⟨hI.times, hI.done, hI.le, ?_, ?_, ?_, ?_, ?_⟩⟩
          · intro u t hu x hx hxn
            rcases hI.finished u t hu x hx hxn with h | h
            · left
              by_cases hxw : x = w
              · subst hxw; exact upd_self _ _ _
              · simp only [upd_ne _ hxw]; exact h
            · exact .inr h
          · have hg : ∀ x, (σ.heads x = true ∨ (fin x).isSome = true) →
                (upd σ.heads w true x = true ∨ (fin x).isSome = true) := by
              intro x h
              rcases h with h | h
              · left
                by_cases hxw : x = w
                · subst hxw; exact upd_self _ _ _
                · simp only [upd_ne _ hxw]; exact h
              · exact .inr h
            refine ⟨⟨pre ++ [w], hpre2, fun x hx hxn => ?_⟩, FramesOk.mono hg rest [v] [v] (fun x hx => .inr hx) hrest⟩
            rcases List.mem_append.mp hx with hx | hx
            · rcases hpw x hx hxn with h | h
              · exact .inl (hg x h)
              · cases h
            · simp only [List.mem_singleton] at hx; subst hx; exact .inl (.inl (upd_self _ _ _))
          · intro u hu
            have := hI.onStack u hu
            rw [hst] at this
            simpa using this
          · intro u hu
            exact hI.stackOn u (by rw [hst]; simpa using hu)
          · have hnd := hI.nodup
            rw [hst] at hnd
            simpa using hnd
        · -- done
          rename_i h0 h1
          cases hs
          have h2 : σ.state w = 2 := by have := hI.le w; omega
          refine ⟨fin, time, ⟨hI.times, hI.done, hI.le, hI.finished, ?_, ?_, ?_, ?_⟩⟩
          · refine ⟨⟨pre ++ [w], hpre2, fun x hx hxn => ?_⟩, hrest⟩
            rcases List.mem_append.mp hx with hx | hx
            · exact hpw x hx hxn
            · simp only [List.mem_singleton] at hx; subst hx; exact .inl (.inr ((hI.done x).mp h2))
          · intro u hu
            have := hI.onStack u hu
            rw [hst] at this
            simpa using this
          · intro u hu
            exact hI.stackOn u (by rw [hst]; simpa using hu)
          · have hnd := hI.nodup
            rw [hst] at hnd
            simpa using hnd
    · -- past the bound
      rename_i hwn
      cases hs
      refine ⟨fin, time, ⟨hI.times, hI.done, hI.le, hI.finished, ?_, ?_, ?_, ?_⟩⟩
      · refine ⟨⟨pre ++ [w], hpre2, fun x hx hxn => ?_⟩, hrest⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact hpw x hx hxn
        · simp only [List.mem_singleton] at hx; subst hx; exact absurd hxn hwn
      · intro u hu
        have := hI.onStack u hu
        rw [hst] at this
        simpa using this
      · intro u hu
        exact hI.stackOn u (by rw [hst]; simpa using hu)
      · have hnd := hI.nodup
        rw [hst] at hnd
        simpa using hnd

/-- **The rounds keep the invariant.** -/
theorem dfsLoop_inv {succ : Nat → List Nat} {n : Nat} :
    ∀ (fuel : Nat) (σ : Dfs) (fin : Nat → Option Nat) (time : Nat), DfsInv succ n σ fin time →
      ∃ fin' time', DfsInv succ n (dfsLoop succ n fuel σ) fin' time'
  | 0, σ, fin, time, h => ⟨fin, time, h⟩
  | k + 1, σ, fin, time, h => by
    unfold dfsLoop
    split
    · exact ⟨fin, time, h⟩
    · rename_i σ' hs
      obtain ⟨fin', time', h'⟩ := dfsStep_inv h hs
      exact dfsLoop_inv k σ' fin' time' h'

/-- The invariant at the walk's start. -/
theorem dfsInit_inv (succ : Nat → List Nat) (n start : Nat) :
    DfsInv succ n (dfsInit succ n start) (fun _ => none) 0 := by
  unfold dfsInit
  split
  · constructor
    · intro _ _ h; simp at h
    · intro v
      by_cases hv : v = start
      · subst hv; simp [upd_self]
      · simp [upd_ne _ hv]
    · intro v
      by_cases hv : v = start
      · subst hv; simp [upd_self]
      · simp [upd_ne _ hv]
    · intro _ _ h; simp at h
    · exact ⟨⟨[], by simp, fun _ h => by simp at h⟩, trivial⟩
    · intro w hw
      by_cases hv : w = start
      · subst hv; simp
      · simp [upd_ne _ hv] at hw
    · intro w hw
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hw
      subst hw; simp [upd_self]
    · simp
  · constructor
    · intro _ _ h; simp at h
    · intro v; simp
    · intro v; simp
    · intro _ _ h; simp at h
    · trivial
    · intro w hw; simp at hw
    · intro w hw; simp at hw
    · simp

/-- **A non-head edge between reached nodes**: from `a`, reached, to a
successor `b` below the bound that is no head. -/
def NonHeadEdge (succ : Nat → List Nat) (n : Nat) (reached heads : Nat → Bool) (a b : Nat) : Prop :=
  reached a = true ∧ b ∈ succ a ∧ b < n ∧ heads b = false

/-- A path of one edge or more. -/
inductive Path (E : Nat → Nat → Prop) : Nat → Nat → Prop where
  | one {a b} : E a b → Path E a b
  | cons {a b c} : E a b → Path E b c → Path E a c

/-- **Every cycle of reached nodes passes through a head**: no path of
non-head edges between reached nodes returns to its node. -/
def HeadsCutCycles (succ : Nat → List Nat) (n : Nat) (reached heads : Nat → Bool) : Prop :=
  ∀ v, ¬ Path (NonHeadEdge succ n reached heads) v v

/-- A path along which a rank decreases at each edge ends lower. -/
theorem Path.rank_lt {E : Nat → Nat → Prop} {r : Nat → Nat} (hE : ∀ a b, E a b → r b < r a) :
    ∀ {a b}, Path E a b → r b < r a
  | _, _, .one h => hE _ _ h
  | _, _, .cons h p => Nat.lt_trans (Path.rank_lt hE p) (hE _ _ h)

/-- **(`dfs_cuts`) The rounds' heads cut every cycle of the nodes they
reach** where the stack is empty: each reached node is done, so each
non-head edge goes to an earlier finishing time. -/
theorem dfs_cuts {succ : Nat → List Nat} {n : Nat} {σ : Dfs} {fin : Nat → Option Nat} {time : Nat}
    (hI : DfsInv succ n σ fin time) (hempty : σ.stack = []) :
    HeadsCutCycles succ n (fun v => σ.state v != 0) σ.heads := by
  have hfin : ∀ v, σ.state v ≠ 0 → (fin v).isSome = true := by
    intro v hv
    have h1 : σ.state v ≠ 1 := fun h => by have := hI.onStack v h; rw [hempty] at this; simp at this
    exact (hI.done v).mp (by have := hI.le v; omega)
  intro v hp
  have hE : ∀ a b, NonHeadEdge succ n (fun v => σ.state v != 0) σ.heads a b → (fin b).getD 0 < (fin a).getD 0 := by
    intro a b ⟨ha, hb, hbn, hh⟩
    have ha' : σ.state a ≠ 0 := by simpa using ha
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hfin a ha')
    rcases hI.finished a t ht b hb hbn with h | ⟨t', ht', hlt⟩
    · rw [hh] at h; cases h
    · rw [ht, ht']; exact hlt
  exact Nat.lt_irrefl _ (Path.rank_lt hE hp)

/-- **More heads still cut every cycle.** -/
theorem HeadsCutCycles.mono {succ : Nat → List Nat} {n : Nat} {reached heads heads' : Nat → Bool}
    (hle : ∀ v, heads v = true → heads' v = true) (h : HeadsCutCycles succ n reached heads) :
    HeadsCutCycles succ n reached heads' := by
  intro v hp
  apply h v
  have : ∀ {a b}, Path (NonHeadEdge succ n reached heads') a b → Path (NonHeadEdge succ n reached heads) a b := by
    intro a b p
    induction p with
    | one he =>
      obtain ⟨h1, h2, h3, h4⟩ := he
      exact .one ⟨h1, h2, h3, by cases hb : heads _ <;> simp_all⟩
    | cons he _ ih =>
      obtain ⟨h1, h2, h3, h4⟩ := he
      exact .cons ⟨h1, h2, h3, by cases hb : heads _ <;> simp_all⟩ ih
  exact this hp

end Dfs

end Verification.TolerantFrames
