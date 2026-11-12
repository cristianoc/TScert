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
    exact .inl (.inr ⟨⟨.nul, .throwV rfl rfl, trivial, rfl⟩, Footprints.Closed.Holds.refl _ _, trivial⟩)

/-- **The handled throw: `handledGraph` is safe from node 0**, its result
`null`, no exception escaping. -/
theorem handled_safe (m : Nat) {ρ : Env} {s : IndexedHeap} :
    SafeGraph noFam handledGraph nulFam s.n s.W s.h (.at 0 ρ) := by
  refine graph_safe_at (Qres := fun _ => True) (Rres := fun _ => True) (pre := handledPre) (m := m) ?_
    (handledPre_admin m) (l := 0) trivial
  intro l ρ s hp
  match l, hp with
  | 0, _ =>
    refine ⟨_, rfl, nulFam, noFam, .empty, .empty, fun _ _ => True, fun _ => True, throw_nul_safe, ?_⟩
    refine ⟨fun _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ ⟨_, _, hT⟩ _ => hT.elim, ?_⟩
    rintro s' e - - ⟨U, -, he⟩ -
    show (mapEnv none (push e ρ)) 0 = .nul
    simpa [mapEnv, slot, push, nulFam] using he
  | 1, hp =>
    refine ⟨_, rfl, noFam, nulFam, .empty, .empty, fun _ _ => True, fun _ => True, ?_, ?_⟩
    · obtain ⟨n, W, h, pos, adm, ok⟩ := s
      cases n with
      | zero => exact absurd pos (Nat.lt_irrefl 0)
      | succ j =>
        simp only [instantiate] at hp ⊢
        exact .inl (.inl ⟨by rw [hp]; rfl, hp, Footprints.Closed.Holds.refl _ _, trivial⟩)
    · refine ⟨fun _ _ _ _ _ _ _ _ => trivial, fun s' v _ _ ⟨U, _, hT⟩ _ => ⟨hT, trivial⟩, ?_⟩
      rintro s' e - - ⟨U, -, he⟩ -
      exact he.elim

/-- `escapingGraph`'s node meets its obligations: its throw escapes with a
value of the graph's exception family. -/
theorem escaping_checked (m : Nat) :
    NodesChecked escapingGraph escapingPre nulFam noFam (fun _ => True) (fun _ => True) m := by
  intro l _ _ hp
  match l, hp with
  | 0, _ => exact ⟨⟨.throw .nul, .ret, none⟩, rfl, nulFam, noFam, .empty, .empty, fun _ _ => True,
      fun _ => True, throw_nul_safe, fun _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ ⟨_, _, hT⟩ _ => hT.elim,
      fun _ _ _ _ ⟨_, _, he⟩ _ => ⟨he, trivial⟩⟩

/-- **The escaping throw: `escapingGraph` is safe from node 0**, its raised
value `null`. -/
theorem escaping_safe (m : Nat) {ρ : Env} {s : IndexedHeap} :
    SafeGraph nulFam escapingGraph noFam s.n s.W s.h (.at 0 ρ) :=
  graph_safe_at (Qres := fun _ => True) (Rres := fun _ => True) (pre := escapingPre) (m := m)
    (escaping_checked m)
    (escapingPre_admin m) (l := 0) trivial

/-- A run of `escapingGraph` to its raised state, with budget left, raises
`null`. -/
theorem escaping_raised (m : Nat) {ρ : Env} {s : IndexedHeap} {k : Nat} {h' : Heap} {e : Tm}
    (hrun : Transitions escapingGraph k s.h (.at 0 ρ) h' (.raised e)) (hk : k < s.n) : e = .nul := by
  obtain ⟨s', -, -, -, -, he, -⟩ := invocation_raised (Ξres := nulFam) (Tres := noFam) (Qres := fun _ => True)
    (Rres := fun _ => True)
    (pre := escapingPre) (m := m)
    (escaping_checked m)
    (escapingPre_admin m) (l := 0) trivial hrun hk
  exact he

end Verification.TolerantFrames
