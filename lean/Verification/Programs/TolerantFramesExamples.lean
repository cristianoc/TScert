import Verification.Programs.TolerantFramesInvocation

/-! # Tolerant frames: two graphs with throws

Two instances of `graph_safe` with an actual throw. In `handledGraph`, node 0
throws `null` and its handler, node 1, returns the thrown value: the raise
target is the handler's assertion with the thrown value bound
(`handled_safe`). In `escapingGraph`, node 0 throws `null` with no handler:
the raise target is the graph's exception family (`escaping_safe`), and a run
to the raised state is an action of every exceptional effect the post bounds
(`escaping_raised`). -/
namespace Verification.TolerantFrames
variable {ε : Verification.HeapKnowledge.EntryState}
open Verification Footprints HeapObservations ControlFlow PointClaims

/-- The family holding `null` alone. -/
def nulFam : Fam := fun _ _ v => v = .nul

/-- The empty family. -/
def noFam : Fam := fun _ _ _ => False

/-- Node 0 throws `null` to node 1, which returns the value it receives. -/
def handledGraph : Program :=
  [⟨.throw .nul, .ret, some ⟨1, none⟩⟩, ⟨.var 0, .ret, none⟩]

/-- Node 0 throws `null`, uncaught. -/
def escapingGraph : Program := [⟨.throw .nul, .ret, none⟩]

/-- The assertions: true at node 0; at node 1, slot 0 holds `null`. -/
def handledPre : Nat → Assertion
  | 0 => fun _ _ _ => True
  | 1 => fun ρ _ _ => ρ 0 = .nul
  | _ => fun _ _ _ => False

def escapingPre : Nat → Assertion
  | 0 => fun _ _ _ => True
  | _ => fun _ _ _ => False

theorem handledPre_admin (m : Nat) : AdminClosed handledPre m := by
  intro l ρ s s' _ _ hp
  match l, hp with
  | 0, hp => exact hp
  | 1, hp => exact hp

theorem escapingPre_admin (m : Nat) : AdminClosed escapingPre m := by
  intro l ρ s s' _ _ hp
  match l, hp with
  | 0, hp => exact hp

/-- A throw of `null` raises `null`, at every positive budget, with the heap
unchanged: within every footprint. -/
theorem throw_nul_safe {T : Fam} {cn ce : Footprints.Closed} {Qn : Post} {s : IndexedHeap} :
    SafePostExc nulFam T (fun h' v => cn.Holds s.h h' ∧ Qn h' v) (fun h' => ce.Holds s.h h' ∧ True)
      s.n s.W s.h (.throw .nul) := by
  obtain ⟨n, W, h, pos, adm, ok⟩ := s
  cases n with
  | zero => exact absurd pos (Nat.lt_irrefl 0)
  | succ j =>
    exact ⟨RefsOk_of_nil rfl, .inl (.inr ⟨⟨.nul, .throwV rfl rfl, trivial, rfl⟩, Footprints.Closed.Holds.refl _ _, trivial⟩)⟩

/-- **The handled throw: `handledGraph` is safe from node 0**, its result
`null`, no exception escaping. -/
theorem handled_safe (m : Nat) {ρ : Env} {s : IndexedHeap} (hρ : ∀ i, RefsOk s.W (ρ i)) :
    SafeGraph noFam handledGraph nulFam s.n s.W s.h (.at 0 ρ) := by
  refine graph_safe_at (Qres := fun _ => True) (Rres := fun _ => True) (pre := handledPre) (m := m) ?_
    (handledPre_admin m) (l := 0) trivial
    (by intro node hm; simp only [handledGraph, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl <;> exact RefsOk_of_nil rfl) hρ
  intro l ρ s hp
  match l, hp with
  | 0, _ =>
    refine ⟨_, rfl, fun _ => ?_⟩
    refine ⟨nulFam, noFam, .empty, .empty, fun _ _ => True, fun _ => True, throw_nul_safe, ?_⟩
    refine ⟨fun _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ ⟨_, _, hT⟩ _ => hT.elim, ?_⟩
    rintro s' e - - ⟨U, -, he⟩ -
    show (mapEnv none (push e ρ)) 0 = .nul
    simpa [mapEnv, slot, push, nulFam] using he
  | 1, hp =>
    refine ⟨_, rfl, fun _ => ?_⟩
    refine ⟨noFam, nulFam, .empty, .empty, fun _ _ => True, fun _ => True, ?_, ?_⟩
    · obtain ⟨n, W, h, pos, adm, ok⟩ := s
      cases n with
      | zero => exact absurd pos (Nat.lt_irrefl 0)
      | succ j =>
        simp only [instantiate] at hp ⊢
        exact ⟨by rw [hp]; exact RefsOk_nul, .inl (.inl ⟨by rw [hp]; rfl, hp, Footprints.Closed.Holds.refl _ _, trivial⟩)⟩
    · refine ⟨fun _ _ _ _ _ _ _ _ => trivial, fun s' v _ _ ⟨U, _, hT⟩ _ => ⟨hT, trivial⟩, ?_⟩
      rintro s' e - - ⟨U, -, he⟩ -
      exact he.elim

/-- `escapingGraph`'s node meets its obligations: its throw escapes with a
value of the graph's exception family. -/
theorem escaping_checked (m : Nat) :
    NodesChecked escapingGraph escapingPre nulFam noFam (fun _ => True) (fun _ => True) m := by
  intro l _ _ hp
  match l, hp with
  | 0, _ => exact ⟨⟨.throw .nul, .ret, none⟩, rfl, fun _ => ⟨nulFam, noFam, .empty, .empty, fun _ _ => True,
      fun _ => True, throw_nul_safe, fun _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ ⟨_, _, hT⟩ _ => hT.elim,
      fun _ _ _ _ ⟨_, _, he⟩ _ => ⟨he, trivial⟩⟩⟩

/-- **The escaping throw: `escapingGraph` is safe from node 0**, its raised
value `null`. -/
theorem escaping_safe (m : Nat) {ρ : Env} {s : IndexedHeap} (hρ : ∀ i, RefsOk s.W (ρ i)) :
    SafeGraph nulFam escapingGraph noFam s.n s.W s.h (.at 0 ρ) :=
  graph_safe_at (Qres := fun _ => True) (Rres := fun _ => True) (pre := escapingPre) (m := m)
    (escaping_checked m)
    (escapingPre_admin m) (l := 0) trivial
    (by intro node hm; simp only [escapingGraph, List.mem_cons, List.not_mem_nil, or_false] at hm
        subst hm; exact RefsOk_of_nil rfl) hρ

/-- A run of `escapingGraph` to its raised state, with budget left, raises
`null`. -/
theorem escaping_raised (m : Nat) {ρ : Env} {s : IndexedHeap} (hρ : ∀ i, RefsOk s.W (ρ i)) {k : Nat}
    {h' : Heap} {e : Tm} (hrun : Transitions escapingGraph k s.h (.at 0 ρ) h' (.raised e)) (hk : k < s.n) : e = .nul := by
  obtain ⟨s', -, -, -, -, he, -⟩ := invocation_raised (Ξres := nulFam) (Tres := noFam) (Qres := fun _ => True)
    (Rres := fun _ => True)
    (pre := escapingPre) (m := m)
    (escaping_checked m)
    (escapingPre_admin m) (l := 0) trivial
    (by intro node hm; simp only [escapingGraph, List.mem_cons, List.not_mem_nil, or_false] at hm
        subst hm; exact RefsOk_of_nil rfl) hρ hrun hk
  exact he

/-! ## The loop's increment

The increment node of the loop of `out[j] = xs[j]` (`loop_back_edge`):
`j + 1` at the write node's environment `v, j, to, xs, out`, `j` in slot 1 and
`to` in slot 2. Under the guard's fact `j < to`, with `0 ≤ j`, the sum is a
safe integer, and the node's judgment is the one `loop_back_edge` names: the
empty effect, the post `j' = j + 1`. -/

/-- The double `1`. -/
def oneBits : UInt64 := bitsOfNat 1

/-- The increment's term: `j + 1`, `j` in slot 1. -/
def incTerm : Tm := .arith .add (.var 1) (.num oneBits)

theorem oneBits_safe : SafeIntegers.SafeInt oneBits 1 := ⟨by decide, .inl ⟨by decide, rfl⟩⟩

/-- **The increment's local judgment**: where slot 1 holds a non-negative
integer below the integer slot 2 holds, `j + 1` takes one step to the double
of the sum, keeping the heap, its value of every family admitting doubles; its
post is the one `loop_back_edge` takes. -/
theorem increment_judgment {Ξ T : Fam} {ce : Footprints.Closed} {Qe : Heap → Prop} {ρ : Env} {s : IndexedHeap}
    (hT : ∀ n W b, T n W (.num b)) {a b : Int} (ha : HeapKnowledge.intValue (ρ 1) = some a)
    (hb : HeapKnowledge.intValue (ρ 2) = some b) (h0 : 0 ≤ a) (hlt : a < b) :
    SafePostExc Ξ T
      (fun h' v => Footprints.Closed.empty.Holds s.h h' ∧
        ∃ a, HeapKnowledge.intValue (ρ 1) = some a ∧ HeapKnowledge.intValue v = some (a + 1))
      (fun h' => ce.Holds s.h h' ∧ Qe h') s.n s.W s.h (instantiate 0 ρ incTerm) := by
  obtain ⟨x, hx⟩ : ∃ x, ρ 1 = .num x := by
    cases h : ρ 1 <;> rw [h] at ha <;> first | exact ⟨_, rfl⟩ | cases ha
  rw [hx] at ha
  have hsx : SafeIntegers.SafeInt x a := SafeIntegers.safeIntOfBits_sound ha
  have hbsafe : b.natAbs < 2 ^ 53 := by
    cases h : ρ 2 <;> rw [h] at hb <;> first | exact (SafeIntegers.safeIntOfBits_sound hb).1 | cases hb
  have hsum : SafeIntegers.SafeInt (arithBits .add x oneBits) (a + 1) :=
    SafeIntegers.add_safe hsx oneBits_safe (by omega)
  obtain ⟨n, W, h, pos, adm, ok⟩ := s
  cases n with
  | zero => exact absurd pos (Nat.lt_irrefl 0)
  | succ n =>
    have hinst : instantiate 0 ρ incTerm = .arith .add (.num x) (.num oneBits) := by
      simp [incTerm, instantiate, hx]
    rw [hinst]
    have hstep : Step h (.arith .add (.num x) (.num oneBits)) h (.num (arithBits .add x oneBits)) :=
      .arithV (by simp [binop, Arith.relational])
    refine ⟨RefsOk_of_nil rfl, .inr ⟨trunc n (Nat.le_succ n) W, h, _, WExt_refl _, WorldAdm_trunc _ adm, hstep,
      HeapOk_trunc n W h ok, SafePostExc.value rfl (hT _ _ _)
        ⟨Footprints.Closed.Holds.refl _ _, a, by rw [hx]; exact ha,
          SafeIntegers.safeIntOfBits_complete hsum⟩ (RefsOk_of_nil rfl)⟩⟩

/-- **The increment node checked**: its local judgment and its back edge's
obligations together, the form `NodesChecked` asks of a node, from the head's
facts `0 ≤ j`, `to ≤ |xs|` and the guard's `j < to` at the node's entry. -/
theorem increment_checked {pre : Nat → Assertion} {Ξres Tres Ξ T : Fam} {Qres Rres : Heap → Prop}
    {ce : Footprints.Closed} {Qe : Heap → Prop} {ρ : Env} {m : Nat} {s₀ : IndexedHeap} {hd : Nat}
    (hT : ∀ n W b, T n W (.num b))
    (hhead : ∀ ρ' s, NonNeg 0 ρ' m s → LowerBound ε 1 2 ρ' m s → pre hd ρ' m s)
    (hΞ : ∀ s e, Above Ξ s e → Ξres s.n s.W e ∧ Rres s.h)
    (hj : NonNeg 1 ρ m s₀) (hb : LowerBound ε 2 3 ρ m s₀)
    (hguard : ∃ a b, HeapKnowledge.intValue (ρ 1) = some a ∧ HeapKnowledge.intValue (ρ 2) = some b ∧ a < b) :
    SafePostExc Ξ T
      (fun h' v => Footprints.Closed.empty.Holds s₀.h h' ∧
        ∃ a, HeapKnowledge.intValue (ρ 1) = some a ∧ HeapKnowledge.intValue v = some (a + 1))
      (fun h' => ce.Holds s₀.h h' ∧ Qe h') s₀.n s₀.W s₀.h (instantiate 0 ρ incTerm) ∧
    NodeObligations pre Ξres Tres Qres Rres Ξ T Footprints.Closed.empty ce
      (fun _ v => ∃ a, HeapKnowledge.intValue (ρ 1) = some a ∧ HeapKnowledge.intValue v = some (a + 1)) Qe
      ρ m s₀ (.bind ⟨hd, some [0, 3, 4, 5]⟩) none := by
  obtain ⟨a, b, ha, hb', hlt⟩ := hguard
  obtain ⟨a', ha', h0⟩ := hj
  rw [ha] at ha'; cases ha'
  exact ⟨increment_judgment hT ha hb' h0 hlt, loop_back_edge hhead hΞ ⟨a, ha, h0⟩ hb⟩

end Verification.TolerantFrames
