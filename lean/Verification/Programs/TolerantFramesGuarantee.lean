import Verification.Programs.TolerantFramesMergeGraph
import Verification.Programs.TolerantFramesGuaranteeRuns
import Verification.Programs.TolerantFramesEdge
import Verification.Programs.TolerantFramesMergeHead

/-! # Tolerant frames: what an accepted run guarantees, from its walk

The unit lane states what an accepted run of the pass guarantees
(`PassUnit.GraphGuarantee`, branch `engine-proof-unit`): safety from every
entry, the footprint and fresh result where a bound is stated, the
postcondition at returns, the regional bound, and every stated assertion at
every state reached at its label. `GraphGuarantee` below is that record field
by field, the reachability relation being `Transitions`, which has the same
constructors as the unit lane's `ReachesIn`.

Each field follows from the walk predicates of the safety proof
(`WalkSound`: `Traversed`, `StepEdgesSound`, `HeadsEntered`, `MergesSound`)
and one per-node hypothesis in the pass's terms, an instance of
`NodesKeep`: the footprint check's (`FootprintKept`), the return check's
(`ReturnsEnsured`), the regional check's (`RegionsKept`) and the stated
assertions' (`AssertionsHeld`). `run_guarantee` assembles them:
`PassWalkSound` at every admitted assignment ⟹ `GraphGuarantee`. -/
namespace Verification.TolerantFrames
open Verification Footprints HeapObservations ControlFlow PointClaims ProgramTyping PositiveGraphs PositiveRules

section Guarantee
variable {ι : Type} [DecidableEq ι] [Hashable ι]

/-- What a request assumes of its entry (the unit lane's `EntryHolds`). -/
def EntryHolds (G : NormalGraph ι) (inputs : List (Ty ι)) (sep : HeapSeparation.Separation)
    (idx : List HeapKnowledge.IndexAtom) (ρ : Env) (n : Nat) (W : WorldT n) (h : Heap) : Prop :=
  EnvOk G inputs ρ n W ∧ HeapSeparation.Holds sep ρ ∧ HeapKnowledge.IndexHolds idx ρ h ∧
    WorldAdm W ∧ HeapOk n W h

/-- **What an accepted run of a graph guarantees** (the unit lane's
`GraphGuarantee`, field by field). -/
structure GraphGuarantee (G : NormalGraph ι) (admits : MixedAssignment ι → Prop) (P : Program)
    (start : Nat) (goal : Goal ι) (inputs : List (Ty ι)) (sep : HeapSeparation.Separation)
    (idx : List HeapKnowledge.IndexAtom) (assertions : List (Nat × HeapKnowledge.Knowledge))
    (bound : Option (Footprints.Closed × Bool × Bool)) (ensures : List HeapKnowledge.IndexFact)
    (regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)) : Prop where
  safe : ∀ η, admits η → ∀ n W h ρ, EntryHolds (reassign G η) inputs sep idx ρ n W h →
    SafeGraph (excOf (reassign G η)) P (GoalHolds (reassign G η) goal (goal.argument ρ)) n W h (.at start ρ)
  bounded : ∀ Φ fresh onThrow, bound = some (Φ, fresh, onThrow) → ∀ E K, GraphCode.program E K = P →
    ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h → (∀ v ∈ L, isVal v = true) → isVal d = true →
    SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' v => Φ.Holds h h' ∧ (fresh = true → Footprints.FreshAt h.length v))
      (fun h' => onThrow = true → Φ.Holds h h') n W h (.goto E K start L d)
  ensured : ensures ≠ [] → ∀ E K, GraphCode.program E K = P → ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h →
    SafePost (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' v => GraphCode.EnsuresAt ensures h' (push v (envOf L d))) n W h (.goto E K start L d)
  regionally : ∀ Φ regions exc, regional = some (Φ, regions, exc) → ∀ E K, GraphCode.program E K = P →
    ∀ η, admits η → ∀ n W h L d,
    EntryHolds (reassign G η) inputs sep idx (envOf L d) n W h →
    SafePostExc (excOf (reassign G η))
      (GoalHolds (reassign G η) goal (goal.argument (envOf L d)))
      (fun h' _ => Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      (fun h' => exc = true → Footprints.ArgumentStoreRegionsWithin Φ regions (envOf L d) h h')
      n W h (.goto E K start L d)
  asserted : ∀ η, admits η → ∀ n W h ρ, EntryHolds (reassign G η) inputs sep idx ρ n W h →
    ∀ l k, (l, k) ∈ assertions → ∀ j h' ρ', j < n → Transitions P j h (.at start ρ) h' (.at l ρ') →
      HeapKnowledge.Holds k ρ' h'

/-! ## The per-node hypotheses, in the pass's terms -/

/-- At a node entry under a bound `Φ` from the invocation's entry heap `h₀`:
the node is in the region `dead` from which no normal return is possible, or
the heap is within `Φ` from `h₀`. -/
def BoundX (Φ : Footprints.Closed) (h₀ : Heap) (dead : List Bool) : Nat → Env → Heap → Prop :=
  fun l _ h => GraphCode.deadAt dead l = true ∨ Φ.Holds h₀ h

/-- A return under the bound: within `Φ` from `h₀`, the value's store fresh
where the bound states a fresh result. -/
def BoundQ (Φ : Footprints.Closed) (h₀ : Heap) (fresh : Bool) : Heap → Tm → Prop :=
  fun h v => Φ.Holds h₀ h ∧ (fresh = true → Footprints.FreshAt h₀.length v)

/-- An escaping throw under the bound: within `Φ` where the bound covers
throws. -/
def BoundR (Φ : Footprints.Closed) (h₀ : Heap) (onThrow : Bool) : Heap → Prop :=
  fun h => onThrow = true → Φ.Holds h₀ h

/-- **(Named hypothesis) The footprint check keeps the bound**: from a node
entry where the pass's assertion holds, with mark `|h₀|`, and the node is
dead or the heap within `Φ` from `h₀`, every run of its term with budget
left reaches an exit whose target is dead or within `Φ`, a return within
`Φ` with a fresh result where `fresh`, an escaping throw within `Φ` where
`onThrow`. -/
def FootprintKept (P : Program) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (Φ : Footprints.Closed) (h₀ : Heap) (dead : List Bool) (fresh onThrow : Bool) : Prop :=
  NodesKeep P (passPre G w startNames ρ0) (BoundX Φ h₀ dead) (BoundQ Φ h₀ fresh) (BoundR Φ h₀ onThrow) h₀.length

/-- A return meets `ensures` at the returned value and the entry values. -/
def EnsuresQ (ens : List HeapKnowledge.IndexFact) (ρ0 : Env) : Heap → Tm → Prop :=
  fun h v => GraphCode.EnsuresAt ens h (push v ρ0)

/-- **(Named hypothesis) The return check establishes `ensures`**: from a
node entry where the pass's assertion holds, every run of its term with
budget left to a value at a return continuation meets `ensures` at the value
and the entry values `ρ0`. -/
def ReturnsEnsured (P : Program) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (ens : List HeapKnowledge.IndexFact) (m : Nat) : Prop :=
  NodesKeep P (passPre G w startNames ρ0) (fun _ _ _ => True) (EnsuresQ ens ρ0) (fun _ => True) m

/-- A return within the regional bound from the entry heap `h₀`. -/
def RegionQ (Φ : Footprints.Closed) (regions : List Footprints.ArgumentStoreRegion) (ρ0 : Env) (h₀ : Heap) :
    Heap → Tm → Prop :=
  fun h _ => Footprints.ArgumentStoreRegionsWithin Φ regions ρ0 h₀ h

/-- An escaping throw within the regional bound where it covers throws. -/
def RegionR (Φ : Footprints.Closed) (regions : List Footprints.ArgumentStoreRegion) (ρ0 : Env) (h₀ : Heap)
    (exc : Bool) : Heap → Prop :=
  fun h => exc = true → Footprints.ArgumentStoreRegionsWithin Φ regions ρ0 h₀ h

/-- **(Named hypothesis) The regional check keeps its facts `X`**: from a
node entry where the pass's assertion and `X` hold, every run of its term
with budget left reaches an exit whose target meets `X`, a return within
the regional bound, an escaping throw within it where `exc`. -/
def RegionsKept (P : Program) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (X : Nat → Env → Heap → Prop) (Φ : Footprints.Closed) (regions : List Footprints.ArgumentStoreRegion)
    (h₀ : Heap) (exc : Bool) : Prop :=
  NodesKeep P (passPre G w startNames ρ0) X (RegionQ Φ regions ρ0 h₀) (RegionR Φ regions ρ0 h₀ exc) h₀.length

/-- **(Named hypothesis) Each stated assertion holds where the pass's
assertion at its label does.** -/
def AssertionsHeld (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat) (ρ0 : Env)
    (assertions : List (Nat × HeapKnowledge.Knowledge)) (m : Nat) : Prop :=
  ∀ l k, (l, k) ∈ assertions → ∀ ρ (s : IndexedHeap), passPre G w startNames ρ0 l ρ m s →
    HeapKnowledge.Holds k ρ s.h

/-- **The walk predicates of the safety proof**, at entry values `ρ0` and
mark `m`. -/
structure WalkSound (P : Program) (G : NormalGraph ι) (w : Walk ι) (startNames : List Nat)
    (given : Nat → Bool) (ctx : Nat → List (Ty ι))
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (fresh : Nat → Nat) (Ξres Tres : Fam) (ρ0 : Env) (m : Nat) : Prop where
  traversed : Traversed G w startNames given ctx edgesIn fresh
  steps : StepEdgesSound P G w startNames ρ0 Ξres Tres (fun _ => True) (fun _ => True) m
  heads : HeadsEntered G w startNames ρ0 given m
  merges : MergesSound G w given ctx edgesIn fresh

/-! ## Each field from the walk -/

section Fields
variable {P : Program} {G : NormalGraph ι} {w : Walk ι} {startNames : List Nat} {given : Nat → Bool}
  {ctx : Nat → List (Ty ι)}
  {edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)}
  {fresh : Nat → Nat} {Ξres Tres : Fam} {ρ0 : Env} {m : Nat}

/-- **The walk checks every node**: the pass's assertions meet the graph's
node obligations. -/
theorem nodesChecked_of_walk (hw : WalkSound P G w startNames given ctx edgesIn fresh Ξres Tres ρ0 m) :
    NodesChecked P (passPre G w startNames ρ0) Ξres Tres (fun _ => True) (fun _ => True) m := by
  intro l ρ s hp
  obtain ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hsafe, ho⟩ := hw.steps l ρ s hp
  exact ⟨node, hn, Ξ, T, cn, ce, Qn, Qe, hsafe,
    nodeObligations_mono (fun t ρ s h => entries_of_traversed hw.traversed hw.heads hw.merges t ρ s h) ho⟩

/-- **`bounded` from the walk**: the term running the graph from the start
at `envOf L d` is safe, its return within `Φ` from the entry heap `h` (its
value fresh where `fr`), its escaping throw within `Φ` where `ex`. -/
theorem bounded_of_walk {E : List Tm} {K : List (Continuation × Option Target)} (hP : GraphCode.program E K = P)
    {start : Nat} {L : List Tm} {d : Tm} {n : Nat} {W : WorldT n} {h : Heap} {Φ : Footprints.Closed}
    {dead : List Bool} {fr ex : Bool}
    (hw : WalkSound P G w startNames given ctx edgesIn fresh Ξres Tres ρ0 h.length)
    (hkeep : FootprintKept P G w startNames ρ0 Φ h dead fr ex) (ha : WorldAdm W) (ho : HeapOk n W h)
    (hpre : ∀ hp ha ho, passPre G w startNames ρ0 start (envOf L d) h.length ⟨n, W, h, hp, ha, ho⟩) :
    SafePostExc Ξres Tres (BoundQ Φ h fr) (BoundR Φ h ex) n W h (.goto E K start L d) := by
  subst hP
  exact keeps_postExc (nodesChecked_of_walk hw) passPre_adminClosed hkeep (fun _ _ _ h => h) n W h _ _ .goto
    ha ho hpre (.inr (Footprints.Closed.Holds.refl Φ h))

/-- **`ensured` from the walk**: the term running the graph from the start
at `envOf L d` is safe and every return meets `ensures` at the value and
the entry values. -/
theorem ensured_of_walk {E : List Tm} {K : List (Continuation × Option Target)} (hP : GraphCode.program E K = P)
    {start : Nat} {L : List Tm} {d : Tm} {n : Nat} {W : WorldT n} {h : Heap} {ens : List HeapKnowledge.IndexFact}
    (hw : WalkSound P G w startNames given ctx edgesIn fresh Ξres Tres ρ0 m)
    (hkeep : ReturnsEnsured P G w startNames ρ0 ens m) (ha : WorldAdm W) (ho : HeapOk n W h)
    (hpre : ∀ hp ha ho, passPre G w startNames ρ0 start (envOf L d) m ⟨n, W, h, hp, ha, ho⟩) :
    SafePost Ξres Tres (EnsuresQ ens ρ0) n W h (.goto E K start L d) := by
  subst hP
  exact (keeps_postExc (nodesChecked_of_walk hw) passPre_adminClosed hkeep (fun _ _ _ h => h) n W h _ _ .goto
    ha ho hpre trivial).post

/-- **`regionally` from the walk**: where the regional facts `X` hold at the
start's entry, the term running the graph is safe and within the regional
bound from the entry heap `h`, on a throw too where `exc`. -/
theorem regionally_of_walk {E : List Tm} {K : List (Continuation × Option Target)}
    (hP : GraphCode.program E K = P) {start : Nat} {L : List Tm} {d : Tm} {n : Nat} {W : WorldT n} {h : Heap}
    {X : Nat → Env → Heap → Prop} {Φ : Footprints.Closed} {regions : List Footprints.ArgumentStoreRegion}
    {exc : Bool} (hw : WalkSound P G w startNames given ctx edgesIn fresh Ξres Tres ρ0 h.length)
    (hkeep : RegionsKept P G w startNames ρ0 X Φ regions h exc) (ha : WorldAdm W) (ho : HeapOk n W h)
    (hpre : ∀ hp ha ho, passPre G w startNames ρ0 start (envOf L d) h.length ⟨n, W, h, hp, ha, ho⟩)
    (hX : X start (envOf L d) h) :
    SafePostExc Ξres Tres (RegionQ Φ regions ρ0 h) (RegionR Φ regions ρ0 h exc) n W h (.goto E K start L d) := by
  subst hP
  exact keeps_postExc (nodesChecked_of_walk hw) passPre_adminClosed hkeep (fun _ _ _ h => h) n W h _ _ .goto
    ha ho hpre hX

/-- **`asserted` from the walk**: a stated assertion holds at every node
entry at its label a run from the start reaches with budget left. -/
theorem asserted_of_walk {start : Nat} {ρ : Env} {s : IndexedHeap}
    {assertions : List (Nat × HeapKnowledge.Knowledge)}
    (hw : WalkSound P G w startNames given ctx edgesIn fresh Ξres Tres ρ0 m)
    (hheld : AssertionsHeld G w startNames ρ0 assertions m) (hpre : passPre G w startNames ρ0 start ρ m s)
    {l : Nat} {k : HeapKnowledge.Knowledge} (hl : (l, k) ∈ assertions) {j : Nat} {h' : Heap} {ρ' : Env}
    (hrun : Transitions P j s.h (.at start ρ) h' (.at l ρ')) (hj : j < s.n) : HeapKnowledge.Holds k ρ' h' := by
  obtain ⟨s', he, hp'⟩ := reached_pre (nodesChecked_of_walk hw) passPre_adminClosed hpre hrun hj
  exact he ▸ hheld l k hl ρ' s' hp'

end Fields

/-! ## The guarantee of an accepted run -/

/-- **What the pass's walk at one assignment provides**: the walk
predicates at every entry value and mark, the start entered at every entry
meeting the request's inputs (`start_passPre`), and the per-node hypotheses
of each stated option. -/
structure PassWalkSound (G : NormalGraph ι) (P : Program) (start : Nat) (goal : Goal ι) (inputs : List (Ty ι))
    (sep : HeapSeparation.Separation) (idx : List HeapKnowledge.IndexAtom)
    (assertions : List (Nat × HeapKnowledge.Knowledge)) (bound : Option (Footprints.Closed × Bool × Bool))
    (ensures : List HeapKnowledge.IndexFact)
    (regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool))
    (w : Walk ι) (given : Nat → Bool) (ctx : Nat → List (Ty ι))
    (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
    (fresh : Nat → Nat) : Prop where
  walk : ∀ ρ0 m, WalkSound P G w (List.range inputs.length) given ctx edgesIn fresh (excOf G)
    (GoalHolds G goal (goal.argument ρ0)) ρ0 m
  entered : ∀ ρ m (s : IndexedHeap), EnvOk G inputs ρ s.n s.W → HeapSeparation.Holds sep ρ →
    HeapKnowledge.IndexHolds idx ρ s.h → passPre G w (List.range inputs.length) ρ start ρ m s
  footprint : ∀ Φ fr ex, bound = some (Φ, fr, ex) → ∃ dead, ∀ ρ0 h₀,
    FootprintKept P G w (List.range inputs.length) ρ0 Φ h₀ dead fr ex
  returns : ensures ≠ [] → ∀ ρ0 m, ReturnsEnsured P G w (List.range inputs.length) ρ0 ensures m
  regions : ∀ Φ regions exc, regional = some (Φ, regions, exc) →
    ∃ X : Env → Heap → Nat → Env → Heap → Prop, ∀ ρ0 h₀, X ρ0 h₀ start ρ0 h₀ ∧
      RegionsKept P G w (List.range inputs.length) ρ0 (X ρ0 h₀) Φ regions h₀ exc
  asserted : ∀ ρ0 m, AssertionsHeld G w (List.range inputs.length) ρ0 assertions m

/-- **An accepted run's guarantee from its walk**: where the pass's walk
provides `PassWalkSound` at every admitted assignment, the run guarantees
every field of `GraphGuarantee`. -/
theorem run_guarantee {G : NormalGraph ι} {admits : MixedAssignment ι → Prop} {P : Program} {start : Nat}
    {goal : Goal ι} {inputs : List (Ty ι)} {sep : HeapSeparation.Separation} {idx : List HeapKnowledge.IndexAtom}
    {assertions : List (Nat × HeapKnowledge.Knowledge)} {bound : Option (Footprints.Closed × Bool × Bool)}
    {ensures : List HeapKnowledge.IndexFact}
    {regional : Option (Footprints.Closed × List Footprints.ArgumentStoreRegion × Bool)}
    (hall : ∀ η, admits η → ∃ (w : Walk ι) (given : Nat → Bool) (ctx : Nat → List (Ty ι))
      (edgesIn : Nat → List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
      (fresh : Nat → Nat),
      PassWalkSound (reassign G η) P start goal inputs sep idx assertions bound ensures regional w given ctx
        edgesIn fresh) :
    GraphGuarantee G admits P start goal inputs sep idx assertions bound ensures regional where
  safe η hη n W h ρ he := by
    obtain ⟨w, given, ctx, edgesIn, fresh, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    cases n with
    | zero => trivial
    | succ n =>
      let s : IndexedHeap := ⟨n + 1, W, h, Nat.zero_lt_succ _, ha, ho⟩
      have hw := hp.walk ρ 0
      exact run_sound_of_walk hw.traversed hw.steps hw.heads hw.merges (hp.entered ρ 0 s hv hs hi)
  bounded Φ fr ex hb E K hP η hη n W h L d he _ _ := by
    obtain ⟨w, given, ctx, edgesIn, fresh, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    obtain ⟨dead, hkeep⟩ := hp.footprint Φ fr ex hb
    exact bounded_of_walk hP (hp.walk (envOf L d) h.length) (hkeep (envOf L d) h) ha ho
      fun hq ha' ho' => hp.entered (envOf L d) h.length ⟨n, W, h, hq, ha', ho'⟩ hv hs hi
  ensured hne E K hP η hη n W h L d he := by
    obtain ⟨w, given, ctx, edgesIn, fresh, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    exact ensured_of_walk hP (hp.walk (envOf L d) 0) (hp.returns hne (envOf L d) 0) ha ho
      fun hq ha' ho' => hp.entered (envOf L d) 0 ⟨n, W, h, hq, ha', ho'⟩ hv hs hi
  regionally Φ regions exc hr E K hP η hη n W h L d he := by
    obtain ⟨w, given, ctx, edgesIn, fresh, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    obtain ⟨X, hX⟩ := hp.regions Φ regions exc hr
    exact regionally_of_walk hP (hp.walk (envOf L d) h.length) (hX (envOf L d) h).2 ha ho
      (fun hq ha' ho' => hp.entered (envOf L d) h.length ⟨n, W, h, hq, ha', ho'⟩ hv hs hi) (hX (envOf L d) h).1
  asserted η hη n W h ρ he l k hl j h' ρ' hj hrun := by
    obtain ⟨w, given, ctx, edgesIn, fresh, hp⟩ := hall η hη
    obtain ⟨hv, hs, hi, ha, ho⟩ := he
    cases n with
    | zero => omega
    | succ n =>
      let s : IndexedHeap := ⟨n + 1, W, h, Nat.zero_lt_succ _, ha, ho⟩
      exact asserted_of_walk (hp.walk ρ 0) (hp.asserted ρ 0) (hp.entered ρ 0 s hv hs hi) hl hrun hj

end Guarantee

end Verification.TolerantFrames

namespace Verification.TolerantFrames
open Verification PointClaims ProgramTyping PositiveGraphs

/-- **The two statements of what an edge into a head establishes, joined**:
the edge lane's `EdgeEstablishes` (the given facts and the head's types at
`mapEnv θ ρ`, which `head_query_sound` gives from the pass's query) supplies
the facts of `HeadEstablishes`; its implications, inputs and promised input
are the edge check's other conjuncts. -/
theorem headEstablishes_of_edge {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {Δ : List (Ty ι)}
    {g : HeapKnowledge.Knowledge} {θ : Mapping} {ρ ρ0 : Env} {s : IndexedHeap}
    {implies : List (PromiseCalls.Implication ι)} {startNames : List Nat} {argName : Option Nat}
    {argSlots : List Nat} {inputSlots : List (Nat × Nat)}
    (he : EdgeEstablishes G Δ g θ ρ s.n s.W s.h)
    (hi : PromiseCalls.ImpliesOk G implies (mapEnv θ ρ) s.n s.W)
    (hin : ∀ j q x, (j, q) ∈ inputSlots → startNames[q]? = some x → mapEnv θ ρ j = ρ0 q)
    (harg : ∀ j a q, j ∈ argSlots → argName = some a → startNames[q]? = some a → mapEnv θ ρ j = ρ0 q) :
    HeadEstablishes G g implies startNames argName argSlots inputSlots ρ0 (mapEnv θ ρ) s :=
  ⟨he.1, hi, hin, harg⟩

end Verification.TolerantFrames
