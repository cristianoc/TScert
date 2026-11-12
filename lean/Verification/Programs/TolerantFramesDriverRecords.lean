import Verification.Programs.TolerantFramesDriverSummaries
import Verification.Programs.TolerantFramesRegionalInputs
import Verification.Programs.TolerantFramesComposeYields
import Verification.Programs.TolerantFramesDriverChecks

/-! # Tolerant frames: the driver's record from its visits

`RecordSound`, what the driver's record of a returned walk must give, is
carried along the walk by an invariant of the walk's state (`RecInv`): the
queue's labels are reached, unvisited and distinct, a node other than a
head in it with no exit left to come in (`deg` 0); each visited label is
reached and its record settled (`Settled`: its node checked, the start
entered, its entry built from the states that came in); a node other than
a head's in-degree counts the exits into it from reached nodes not yet
visited (`pend`); every state that came in is below the fresh counter.

What a visit gives (`VisitFacts`) is stated over the record's fields: the
record changes at the visited label only; states come in at its exits
only; its exits' in-degrees go down by their count; the labels it queues
are exits whose in-degree reaches 0; its label is settled. Where the setup
starts the invariant (`SetupFacts`) and every visit gives `VisitFacts`,
the record of every returned walk is sound (`recordsSound_of`): at its
end every reached label is visited, since the visited labels are reached
and at least as many (`filter_eq_of_le`), so every state that came in came
in before its target's visit. -/
namespace Verification.TolerantFrames
open Verification ControlFlow CertificateProducer PositiveCertificates PositiveGraphs LabelStore ProgramTyping

/-! ## Counting labels -/

/-- Where `p` implies `q` on a list, `q` keeps at least as many. -/
theorem filter_length_mono {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl _
  | y :: l, h => by
    have ih := filter_length_mono p q l fun x hx => h x (List.mem_cons_of_mem _ hx)
    cases hpy : p y with
    | true => simp [hpy, h y (List.mem_cons_self ..) hpy, ih]
    | false => cases hqy : q y <;> simp [hpy, hqy] <;> omega

/-- Where `p` implies `q` on a list and `q` holds no more often than `p`,
`q` implies `p` there. -/
theorem filter_eq_of_le {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) → (l.filter q).length ≤ (l.filter p).length →
      ∀ x ∈ l, q x = true → p x = true
  | [], _, _, x, hx, _ => by cases hx
  | y :: l, hpq, hle, x, hx, hq => by
    have hpq' : ∀ x ∈ l, p x = true → q x = true := fun x hx => hpq x (List.mem_cons_of_mem _ hx)
    have hmono := filter_length_mono p q l hpq'
    cases hpy : p y with
    | true =>
      have hqy := hpq y (List.mem_cons_self ..) hpy
      simp only [List.filter_cons, hpy, hqy, if_true, List.length_cons] at hle
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hpy
      · exact filter_eq_of_le p q l hpq' (by omega) x hx hq
    | false =>
      cases hqy : q y with
      | true =>
        simp only [List.filter_cons, hpy, hqy, if_true, List.length_cons] at hle
        simp at hle
        omega
      | false =>
        simp only [List.filter_cons, hpy, hqy] at hle
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hq] at hqy; cases hqy
        · exact filter_eq_of_le p q l hpq' (by simpa using hle) x hx hq

/-- Flipping one label of a list without repeats from false to true adds
one to the labels a filter keeps. -/
theorem filter_flip {α : Type} [DecidableEq α] (p p' : α → Bool) (a : α) (hpa : p a = false) (hpa' : p' a = true)
    (hrest : ∀ x, x ≠ a → p' x = p x) :
    ∀ (l : List α), l.Nodup → a ∈ l → (l.filter p').length = (l.filter p).length + 1
  | [], _, h => by cases h
  | y :: l, hnd, ha => by
    have hnd' := (List.nodup_cons.mp hnd)
    by_cases hy : y = a
    · subst hy
      have heq : l.filter p' = l.filter p :=
        List.filter_congr fun x hx => hrest x (fun h => hnd'.1 (h ▸ hx))
      simp [hpa, hpa', heq]
    · have ha' : a ∈ l := (List.mem_cons.mp ha).resolve_left (Ne.symm hy)
      have ih := filter_flip p p' a hpa hpa' hrest l hnd'.2 ha'
      rw [List.filter_cons, List.filter_cons, hrest y hy]
      split <;> simp [ih]

/-- A sum over a list in which one entry without repeats drops to 0. -/
theorem sum_drop {α : Type} [DecidableEq α] (f f' : α → Nat) (a : α) (hfa : f' a = 0)
    (hrest : ∀ x, x ≠ a → f' x = f x) :
    ∀ (l : List α), l.Nodup → a ∈ l → (l.map f).sum = (l.map f').sum + f a
  | [], _, h => by cases h
  | y :: l, hnd, ha => by
    have hnd' := (List.nodup_cons.mp hnd)
    by_cases hy : y = a
    · subst hy
      have heq : l.map f' = l.map f := List.map_congr_left fun x hx => hrest x (fun h => hnd'.1 (h ▸ hx))
      simp [heq, hfa]
      omega
    · have ha' : a ∈ l := (List.mem_cons.mp ha).resolve_left (Ne.symm hy)
      have ih := sum_drop f f' a hfa hrest l hnd'.2 ha'
      simp only [List.map_cons, List.sum_cons, hrest y hy, ih]
      omega

/-- A sum over a list is at least an entry of a label in it. -/
theorem le_sum_of_mem {α : Type} (f : α → Nat) : ∀ (l : List α) (a : α), a ∈ l → f a ≤ (l.map f).sum
  | [], _, h => by cases h
  | y :: l, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · have := le_sum_of_mem f l a ha
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **A state below a counter is below every larger one.** -/
theorem StateBelow.mono {st : SinglePass.State} {a b : Nat} (h : StateBelow st a) (hab : a ≤ b) : StateBelow st b :=
  ⟨fun x hx => Nat.lt_of_lt_of_le (h.1 x hx) hab, fun s hs x hx => Nat.lt_of_lt_of_le (h.2.1 s hs x hx) hab,
    fun x hx => Nat.lt_of_lt_of_le (h.2.2 x hx) hab⟩

/-! ## The record's reads -/

section Records
variable {ι : Type} [Labels ι] {G : NormalGraph ι} {I : InstanceImageCheck G}

omit [Labels ι] in
/-- Whether the record visited a label. -/
def visB (w : SinglePass.Walk ι) (t : Nat) : Bool := (w.labels[t]?).any (·.visited)

omit [Labels ι] in
theorem ofPass_visited (w : SinglePass.Walk ι) (heads : Nat → Bool) (t : Nat) :
    (ofPass w heads).visited t ↔ visB w t = true := by
  unfold ofPass visB
  simp only
  cases w.labels[t]? with
  | none => simp
  | some x => simp

omit [Labels ι] in
/-- The states that came into a label. -/
def incS (w : SinglePass.Walk ι) (t : Nat) : List SinglePass.State := (w.incoming[t]?).getD []

omit [Labels ι] in
/-- The implications that came into a label beside them. -/
def incI (w : SinglePass.Walk ι) (t : Nat) : List (List (PromiseCalls.Implication ι)) := (w.incomingImpl[t]?).getD []

/-- A label's in-degree as the walk keeps it. -/
def deg (σ : SinglePass.WalkState ι G) (t : Nat) : Nat := (σ.indeg[t]?).getD 0

/-- The setup's loop heads by label. -/
def envHead (env : SinglePass.WalkEnv ι G I) (t : Nat) : Bool := (env.isHead[t]?).getD false

/-- The labels the setup's walk reaches. -/
def envReached (env : SinglePass.WalkEnv ι G I) (t : Nat) : Bool := (env.reached[t]?).getD false

/-- A label's exits' targets (the pass's nodes' successors). -/
def exitsOf (env : SinglePass.WalkEnv ι G I) (l : Nat) : List Nat := SinglePass.nodeSucc env.nodes l

/-- **The exits still to come into `t`**: those of every reached label below
the bound not yet visited. -/
def pend (env : SinglePass.WalkEnv ι G I) (σ : SinglePass.WalkState ι G) (t : Nat) : Nat :=
  ((List.range env.n).map fun s => if envReached env s && !visB σ.walk s then (exitsOf env s).count t else 0).sum

/-- **A state that came into `t`**, with `t`'s width, a well-formed store,
below the fresh counter. -/
def PushOk (c : Target.RunCall G I) (t : Nat) (s : SinglePass.State) (fresh : Nat) : Prop :=
  s.names.length = (passCtx c t).length ∧ StoreWF s.store ∧ StateBelow s fresh

theorem PushOk.mono {c : Target.RunCall G I} {t : Nat} {s : SinglePass.State} {a b : Nat}
    (h : PushOk c t s a) (hab : a ≤ b) : PushOk c t s b :=
  ⟨h.1, h.2.1, h.2.2.mono hab⟩

/-- **A visited label's record as the visit leaves it**: its node checked
at every record agreeing with it at the label and extending its incoming
arrays (`WalkExtends`), and every summary table its answers are a prefix of,
with the visit's checks in the no-return region `dead` (`NodePassChecked`)
and its exit computation (`NodeExitTrace`) at the same node; at the start, the start entered; at a node other
than a head, its entry the written facts added to its one incoming state or
to the merge of those that came in (or to some state where none did). -/
structure SettledCore (c : Target.RunCall G I) (heads : Nat → Bool) (dead : List Bool) (σ : SinglePass.WalkState ι G)
    (l : Nat) : Prop where
  node : ∀ (w : SinglePass.Walk ι) (a : Answered G), w.labels[l]? = σ.walk.labels[l]? →
    WalkExtends σ.walk w → SumsPrefix σ.answers a →
    ProgramCertificates.SummariesSound G I a.summaries.toList →
    ∃ r : NodeChecked G I c.codes c.passChecker c.P (ofPass w heads) (List.range c.inputs.length) (passCtx c) l,
      NodePassChecked c dead r ∧ NodeExitTrace c (passEdgesIn w) r ∧
        (w.labels[l]?).bind (·.stepped) = some r.st
  start : l = c.start → ∀ w : SinglePass.Walk ι, w.labels[l]? = σ.walk.labels[l]? →
    StartEntered c (ofPass w heads) (passCtx c) (passStated c)
  entry : heads l = false → ∃ b, (ofPass σ.walk heads).entry l = withWritten (passStated c l) b ∧
    (∀ e, (ofPass σ.walk heads).incoming l = [e] → b = e.1 ∧ (ofPass σ.walk heads).implies l = e.2) ∧
    (2 ≤ ((ofPass σ.walk heads).incoming l).length →
      b = (SinglePass.mergeState G (passCtx c l) (((ofPass σ.walk heads).incoming l).map (·.1))
        (passEdgesIn σ.walk l) (passFresh σ.walk l)).state ∧
      (ofPass σ.walk heads).implies l = (SinglePass.mergeState G (passCtx c l)
        (((ofPass σ.walk heads).incoming l).map (·.1)) (passEdgesIn σ.walk l) (passFresh σ.walk l)).implies)

/-- **A visited label's record settled**: `SettledCore`, and at a merge the
states that came in and the start names below the merge's counter. -/
structure Settled (c : Target.RunCall G I) (heads : Nat → Bool) (dead : List Bool) (σ : SinglePass.WalkState ι G)
    (l : Nat) : Prop extends SettledCore c heads dead σ l where
  below : heads l = false → 2 ≤ ((ofPass σ.walk heads).incoming l).length →
    (∀ e ∈ (ofPass σ.walk heads).incoming l, StateBelow e.1 (passFresh σ.walk l)) ∧
    ∀ x ∈ List.range c.inputs.length, x < passFresh σ.walk l

/-- **What the setup's `env` states of the call**: its heads the call's
(`passHeads`); the labels it reaches closed under exits below the bound;
the start reached; the count `runWalk` reads of the reached labels; a
claim per label below the bound, the call's claims; a given state at
heads only; the call's nodes, checker, bound, goal, postcondition and written
assertions; the start's names, context and checked given entry. -/
structure EnvFacts (c : Target.RunCall G I) (env : SinglePass.WalkEnv ι G I) : Prop where
  heads : envHead env = passHeads c
  closed : ∀ s t, envReached env s = true → t ∈ exitsOf env s → t < env.n → envReached env t = true
  start : c.start < env.n ∧ envReached env c.start = true
  reachable : (env.reached.toList.filter id).length = ((List.range env.n).filter (envReached env)).length
  claimed : env.claimed.size = env.n
  claims : env.claimed = c.claims.toArray
  given : ∀ t : Nat, env.isHead[t]! = false → env.given[t]! = none
  nodes : env.nodes = c.P.toArray
  nodeCount : env.n = c.P.length
  codes : env.codes = c.codes
  checker : env.passChecker = c.passChecker
  bound : env.bound = c.bound
  goal : env.goal = c.goal
  ensures : env.ensures = c.ensures
  startNames : env.startNames = List.range c.inputs.length
  argName : env.argName = c.goal.slot.bind ((List.range c.inputs.length)[·]?)
  stated : ∀ l, env.stated[l]! = passStated c l
  startLabel : env.start = c.start
  startHead : env.isHead[c.start]! = true
  startContext : passCtx c c.start = c.inputs
  startGiven : ∃ supplied,
    SinglePass.entryRefusal G c.inputs c.claims c.start c.goal (passStated c c.start) supplied
      ((env.givenImplies[c.start]?).getD []) ((env.givenArgs[c.start]?).getD [])
      ((env.givenInputs[c.start]?).getD []) c.entryIndices c.entrySeparation = none ∧
    env.given[c.start]! = some (startGiven (passStated c c.start) c.entryIndices c.entrySeparation supplied)
  regional : env.regional = c.regional

omit [Labels ι] in
/-- A list's true entries, counted by position. -/
theorem filter_id_length (l : List Bool) :
    (l.filter id).length = ((List.range l.length).filter fun t => l[t]?.getD false).length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_cons, List.filter_map]
    cases b <;> simp [Function.comp_def, ih]

/-- **The setup's loop facts from `loopHeads`**: where the setup's nodes are
the call's, its reached flags `loopHeads`' and its heads the call's, with
the start below the bound, a claim per label and a given state at heads
only, and the call configuration and checked start entry, `env` states
the call (`loopHeads_closed`, `loopHeads_reached_size`).
The equations are read off `setup` (W4). -/
theorem envFacts_of_loopHeads {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I}
    (hnodes : env.nodes = c.P.toArray) (hn : env.n = c.P.toArray.size)
    (hreached : env.reached = (SinglePass.loopHeads c.P.toArray c.start).2) (hheads : envHead env = passHeads c)
    (hstart : c.start < env.n) (hclaimed : env.claimed.size = env.n) (hclaims : env.claimed = c.claims.toArray)
    (hgiven : ∀ t : Nat, env.isHead[t]! = false → env.given[t]! = none)
    (hcodes : env.codes = c.codes) (hchecker : env.passChecker = c.passChecker)
    (hbound : env.bound = c.bound) (hgoal : env.goal = c.goal) (hensures : env.ensures = c.ensures)
    (hnames : env.startNames = List.range c.inputs.length)
    (harg : env.argName = c.goal.slot.bind ((List.range c.inputs.length)[·]?))
    (hstated : ∀ l, env.stated[l]! = passStated c l) (hstartLabel : env.start = c.start)
    (hstartHead : env.isHead[c.start]! = true) (hstartCtx : passCtx c c.start = c.inputs)
    (hstartGiven : ∃ supplied,
      SinglePass.entryRefusal G c.inputs c.claims c.start c.goal (passStated c c.start) supplied
        ((env.givenImplies[c.start]?).getD []) ((env.givenArgs[c.start]?).getD [])
        ((env.givenInputs[c.start]?).getD []) c.entryIndices c.entrySeparation = none ∧
      env.given[c.start]! = some (startGiven (passStated c c.start) c.entryIndices c.entrySeparation supplied))
    (hregional : env.regional = c.regional) : EnvFacts c env := by
  have hc := loopHeads_closed c.P.toArray c.start
  refine ⟨hheads, fun s t hs ht htn => ?_, ⟨hstart, ?_⟩, ?_, hclaimed, hclaims, hgiven, hnodes,
    by simpa using hn, hcodes, hchecker, hbound, hgoal, hensures, hnames, harg, hstated, hstartLabel, hstartHead, hstartCtx, hstartGiven, hregional⟩
  · unfold envReached exitsOf at *
    rw [hreached] at hs ⊢
    rw [hnodes] at ht
    exact hc.1 s t hs ht (hn ▸ htn)
  · unfold envReached; rw [hreached]; exact hc.2 (hn ▸ hstart)
  · have hsz : env.reached.toList.length = env.n := by
      rw [Array.length_toList, hreached, loopHeads_reached_size, hn]
    rw [filter_id_length, hsz]
    unfold envReached
    simp only [Array.getElem?_toList]

/-- **What the walk's state gives a node's entry**: the start's names and
the promised input's name below the walk's counter, and the start's slots
`i + base` below it (`headEntry`'s names at the start). -/
def StartBelow (env : SinglePass.WalkEnv ι G I) (fresh : Nat) : Prop :=
  (∀ x ∈ env.startNames, x < fresh) ∧ (∀ a, env.argName = some a → a < fresh) ∧
    ∀ i < (env.claimed[env.start]!).context.length, i + env.startNames.headD 0 < fresh

theorem StartBelow.mono {env : SinglePass.WalkEnv ι G I} {a b : Nat} (h : StartBelow env a) (hab : a ≤ b) :
    StartBelow env b :=
  ⟨fun x hx => Nat.lt_of_lt_of_le (h.1 x hx) hab, fun x hx => Nat.lt_of_lt_of_le (h.2.1 x hx) hab,
    fun i hi => Nat.lt_of_lt_of_le (h.2.2 i hi) hab⟩

/-- Every implication carried into a label names values below the counter. -/
@[nospecialize] def IncomingBelow (w : SinglePass.Walk ι) (fresh : Nat) : Prop :=
  ∀ t xs, xs ∈ incI w t → ∀ y ∈ xs, y.test < fresh ∧ y.target < fresh

/-- The successful visit whose result supplies this label's record, including
its exits' complete optional regional result and summary prefix. -/
@[nospecialize] def VisitOrigin (env : SinglePass.WalkEnv ι G I) (w : SinglePass.Walk ι) (a : Answered G) (l : Nat) : Prop :=
  ∃ (σ : SinglePass.WalkState ι G) (en : SinglePass.Entered ι) (sd : SinglePass.StepDone ι G)
    (ex : SinglePass.ExitsDone ι G),
    SinglePass.visitEntry G I env σ l = .ok en ∧
    SinglePass.visitStep G I env σ l en = .ok sd ∧
    SinglePass.visitExits G I env σ l en sd = .ok ex ∧
    w.labels[l]? = some (SinglePass.LabelWalk.ofVisit σ.fresh en sd (ex.regional.map (·.state))) ∧
    SumsPrefix ex.answers a

/-- A recorded visit with its regional inputs frozen at a visited non-head,
and every state its exits accumulated retained in the current incoming table. -/
@[nospecialize] def RegionalOrigin (env : SinglePass.WalkEnv ι G I)
    (σ : SinglePass.WalkState ι G) (l : Nat) : Prop :=
  ∃ (before : SinglePass.WalkState ι G) (en : SinglePass.Entered ι)
    (sd : SinglePass.StepDone ι G) (ex : SinglePass.ExitsDone ι G),
    SinglePass.visitEntry G I env before l = .ok en ∧
    SinglePass.visitStep G I env before l en = .ok sd ∧
    SinglePass.visitExits G I env before l en sd = .ok ex ∧
    σ.walk.labels[l]? = some (SinglePass.LabelWalk.ofVisit before.fresh en sd (ex.regional.map (·.state))) ∧
    SumsPrefix ex.answers σ.answers ∧
    before.regionIn.size = env.n ∧
    (envHead env l = false → before.regionIn[l]? = σ.regionIn[l]?) ∧
    ∀ (t : Nat) (e : SinglePass.RegionState), e ∈ ex.regionIn[t]! → e ∈ σ.regionIn[t]!

/-- **The walk's invariant**: the queue's labels distinct, below the bound,
reached, unvisited and, other than heads, with no exit left to come in; the
visited labels reached, with no exit left to come in, their exits below the
bound, counted by the record, which has a record per label below the
bound; a node other than a head's in-degree the
exits still to come into it (`pend`); the states and implications that came
in paired, each from an exit of a visited label, with its target's width, a
well-formed store and below the fresh counter, the edges into heads from
visited labels' exits; the start names below the counter; every visited
label settled, its checks in the setup's no-return region `deadArr`; the
setup's start names and promised input's name below the counter
(`StartBelow`); incoming implications below the counter (`IncomingBelow`). -/
structure RecInv (c : Target.RunCall G I) (env : SinglePass.WalkEnv ι G I) (σ : SinglePass.WalkState ι G) :
    Prop where
  nodup : σ.queue.Nodup
  queue : ∀ q ∈ σ.queue, q < env.n ∧ envReached env q = true ∧ visB σ.walk q = false ∧
    (envHead env q = false → deg σ q = 0)
  visR : ∀ t, visB σ.walk t = true → t < env.n ∧ envReached env t = true
  visDeg : ∀ t, visB σ.walk t = true → envHead env t = false → deg σ t = 0
  exits : ∀ s, visB σ.walk s = true → ∀ t ∈ exitsOf env s, t < env.n
  count : σ.walk.visited = ((List.range env.n).filter (visB σ.walk)).length
  size : σ.walk.labels.size = env.n
  degs : ∀ t < env.n, envHead env t = false → deg σ t = pend env σ t
  inLen : ∀ t, (incS σ.walk t).length = (incI σ.walk t).length
  inSizes : σ.walk.incoming.size = σ.walk.incomingImpl.size
  inVis : ∀ t, incS σ.walk t ≠ [] → ∃ s, visB σ.walk s = true ∧ t ∈ exitsOf env s
  edgesVis : ∀ e ∈ σ.walk.edges.toList, ∃ s, visB σ.walk s = true ∧ e.target.label ∈ exitsOf env s
  push : ∀ t, ∀ s ∈ incS σ.walk t, PushOk c t s σ.fresh
  startFresh : ∀ x ∈ List.range c.inputs.length, x < σ.fresh
  startBelow : StartBelow env σ.fresh
  settled : ∀ t, visB σ.walk t = true → Settled c (envHead env) env.deadArr.toList σ t
  impBelow : IncomingBelow σ.walk σ.fresh
  vacuity : CachedVacuity G env.claimed σ.unsat
  origins : ∀ l, visB σ.walk l = true → VisitOrigin env σ.walk σ.answers l
  regionalOrigins : ∀ l, visB σ.walk l = true → RegionalOrigin env σ l
  regionSizes : σ.regionIn.size = env.n

/-- **At the walk's end every reached label is visited**, where the record
counts at least the reached labels (`filter_eq_of_le`). -/
theorem RecInv.all_visited {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G}
    (hE : EnvFacts c env) (hI : RecInv c env σ) (hle : (env.reached.toList.filter id).length ≤ σ.walk.visited) :
    ∀ t < env.n, envReached env t = true → visB σ.walk t = true := by
  intro t ht hr
  refine filter_eq_of_le (visB σ.walk) (envReached env) (List.range env.n) (fun x _ hv => (hI.visR x hv).2)
    ?_ t (List.mem_range.mpr ht) hr
  rw [← hI.count, ← hE.reachable]
  exact hle

/-- **At the walk's end every label something came into is visited.** -/
theorem RecInv.visited_of_incoming {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I}
    {σ : SinglePass.WalkState ι G} (hE : EnvFacts c env) (hI : RecInv c env σ)
    (hle : (env.reached.toList.filter id).length ≤ σ.walk.visited) :
    ∀ t, (ofPass σ.walk (envHead env)).incoming t ≠ [] → visB σ.walk t = true := by
  intro t hne
  have hfrom : ∀ s, visB σ.walk s = true → t ∈ exitsOf env s → visB σ.walk t = true := fun s hs hts =>
    hI.all_visited hE hle t (hI.exits s hs t hts) (hE.closed s t (hI.visR s hs).2 hts (hI.exits s hs t hts))
  unfold ofPass at hne
  simp only at hne
  split at hne
  · split at hne
    · rename_i hany
      obtain ⟨e, he, het⟩ := List.any_eq_true.mp hany
      obtain ⟨s, hs, hts⟩ := hI.edgesVis e he
      exact hfrom s hs (by simpa using (beq_iff_eq.mp het) ▸ hts)
    · exact (hne rfl).elim
  · have hinc : incS σ.walk t ≠ [] := by
      intro h0
      apply hne
      unfold incS at h0
      rw [h0]
      simp
    obtain ⟨s, hs, hts⟩ := hI.inVis t hinc
    exact hfrom s hs hts

/-- **The record of a walk that ended is sound** (`RecordSound`), where the
invariant holds, the record counts at least the reached labels and the
final summaries are sound: each visited node checked, the walk's
construction from the settled records (`TraversedA`, each visited label's
base its single incoming state, its merge, or its head entry), the start
entered. -/
theorem recordSound_of_inv {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I} {σ : SinglePass.WalkState ι G}
    (hE : EnvFacts c env) (hI : RecInv c env σ) (hle : (env.reached.toList.filter id).length ≤ σ.walk.visited)
    (hsums : ProgramCertificates.SummariesSound G I σ.answers.summaries.toList) : RecordSound G I c σ := by
  have hheads := hE.heads
  have hvi := hI.visited_of_incoming hE hle
  rw [hheads] at hvi
  have hset : ∀ t, visB σ.walk t = true → Settled c (passHeads c) env.deadArr.toList σ t :=
    fun t ht => hheads ▸ hI.settled t ht
  classical
  let base : Nat → SinglePass.State := fun t =>
    if h : visB σ.walk t = true ∧ passHeads c t = false then Classical.choose ((hset t h.1).entry h.2)
    else (ofPass σ.walk (passHeads c)).entry t
  have hbase : ∀ t (h : visB σ.walk t = true) (hg : passHeads c t = false),
      base t = Classical.choose ((hset t h).entry hg) := fun t h hg => by
    simp only [base, dif_pos (And.intro h hg)]
  refine ⟨fun l hl => ((hset l ((ofPass_visited _ _ _).mp hl)).node σ.walk σ.answers rfl (WalkExtends.refl _) (SumsPrefix.refl _)
    hsums).elim fun r _ => ⟨r⟩,
    ⟨base, ?_, fun t hv => ?_⟩, ?_⟩
  · refine { visited := fun t hne => (ofPass_visited σ.walk (passHeads c) t).mpr (hvi t hne),
             single := fun t e hg hin => ?_, merge := fun t hg h2 => ?_, width := fun t hg h2 e he => ?_,
             wf := fun t hg h2 e he => ?_, below := fun t hg h2 e he => ?_, startBelow := fun t hg h2 => ?_ }
    · have hv := hvi t (by simp only at hin; rw [hin]; simp)
      have hs := Classical.choose_spec ((hset t hv).entry hg)
      simp only at hin ⊢
      rw [hbase t hv hg]
      exact hs.2.1 e hin
    · have hv := hvi t (List.ne_nil_of_length_pos (by simp only at h2; omega))
      have hs := Classical.choose_spec ((hset t hv).entry hg)
      simp only at h2 ⊢
      rw [hbase t hv hg]
      exact hs.2.2 h2
    · simp only [ofPass, hg] at he
      exact (hI.push t e.1 (List.of_mem_zip he).1).1
    · simp only [ofPass, hg] at he
      exact (hI.push t e.1 (List.of_mem_zip he).1).2.1
    · have hv := hvi t (List.ne_nil_of_length_pos (by simp only at h2; omega))
      exact ((hset t hv).below hg h2).1 e he
    · have hv := hvi t (List.ne_nil_of_length_pos (by simp only at h2; omega))
      exact ((hset t hv).below hg h2).2
  · have hv' := (ofPass_visited _ _ _).mp hv
    cases hg : passHeads c t with
    | true => simp only [base, hg, if_true]; simp
    | false =>
      rw [if_neg (by simp), hbase t hv' hg]
      exact (Classical.choose_spec ((hset t hv').entry hg)).1
  · exact (hset c.start (hI.all_visited hE hle c.start hE.start.1 hE.start.2)).start rfl σ.walk rfl

/-- **A settled record stays settled** where the label's record, the
states, implications and merge edges that came into it (at a node other
than a head) are unchanged and the answers grow by a prefix. -/
theorem Settled.frame {c : Target.RunCall G I} {heads : Nat → Bool} {dead : List Bool}
    {σ σ' : SinglePass.WalkState ι G} {t : Nat} (h : Settled c heads dead σ t) (hl : σ'.walk.labels[t]? = σ.walk.labels[t]?)
    (hin : heads t = false → σ'.walk.incoming[t]? = σ.walk.incoming[t]? ∧
      σ'.walk.incomingImpl[t]? = σ.walk.incomingImpl[t]? ∧ σ'.walk.incomingEdges[t]? = σ.walk.incomingEdges[t]?)
    (hk : SumsPrefix σ.answers σ'.answers) (hext : WalkExtends σ.walk σ'.walk) : Settled c heads dead σ' t := by
  have he : (ofPass σ'.walk heads).entry t = (ofPass σ.walk heads).entry t := by simp only [ofPass, hl]
  have hi : (ofPass σ'.walk heads).implies t = (ofPass σ.walk heads).implies t := by simp only [ofPass, hl]
  have hf : passFresh σ'.walk t = passFresh σ.walk t := by simp only [passFresh, hl]
  have hinc : heads t = false → (ofPass σ'.walk heads).incoming t = (ofPass σ.walk heads).incoming t ∧
      passEdgesIn σ'.walk t = passEdgesIn σ.walk t := fun hg => by
    obtain ⟨h1, h2, h3⟩ := hin hg
    exact ⟨by simp [ofPass, hg, h1, h2], by simp only [passEdgesIn, h3]⟩
  refine { node := fun w a hw hwa hka hs => h.node w a (hw.trans hl) (hext.trans hwa) (SumsPrefix.trans hk hka) hs,
           start := fun hs w hw => h.start hs w (hw.trans hl),
           entry := fun hg => ?_, below := fun hg h2 => ?_ }
  · obtain ⟨hI, hE⟩ := hinc hg
    rw [he, hi, hI, hE, hf]
    exact h.entry hg
  · obtain ⟨hI, -⟩ := hinc hg
    rw [hI] at h2 ⊢
    rw [hf]
    exact h.below hg h2

/-- **What a visit gives**, from the state `σ` it starts from (the queue's
first label `l` taken off) to the state `σ'` it returns: `l`'s exits below
the bound; the record changed at `l` only, `l` visited, counted once, as
many records as before;
states, implications and merge edges coming in at `l`'s exits only, paired,
each with its target's width, a well-formed store and below the fresh
counter after the visit; the edges into heads at `l`'s exits; the fresh
counter not decreasing; a node other than a head's in-degree going down by
its count among `l`'s exits; the labels queued in front of the rest
`l`'s exits, other than heads, whose in-degree is 0, distinct where no
in-degree is below its count; `l`'s record settled where it is no exit of
its own other than a head; a merge's counter the one the visit starts
from. -/
structure VisitFacts (c : Target.RunCall G I) (env : SinglePass.WalkEnv ι G I) (σ : SinglePass.WalkState ι G)
    (l : Nat) (σ' : SinglePass.WalkState ι G) : Prop where
  exits : ∀ t ∈ exitsOf env l, t < env.n
  labels : ∀ t, t ≠ l → σ'.walk.labels[t]? = σ.walk.labels[t]?
  visits : visB σ'.walk l = true
  count : σ'.walk.visited = σ.walk.visited + 1
  size : σ'.walk.labels.size = σ.walk.labels.size
  frame : ∀ t, t ∉ exitsOf env l → σ'.walk.incoming[t]? = σ.walk.incoming[t]? ∧
    σ'.walk.incomingImpl[t]? = σ.walk.incomingImpl[t]? ∧ σ'.walk.incomingEdges[t]? = σ.walk.incomingEdges[t]?
  pushes : ∀ t, ∃ ns nis, incS σ'.walk t = ns ++ incS σ.walk t ∧ incI σ'.walk t = nis ++ incI σ.walk t ∧
    ns.length = nis.length ∧ ∀ s ∈ ns, PushOk c t s σ'.fresh
  edges : ∃ new, σ'.walk.edges.toList = σ.walk.edges.toList ++ new ∧ ∀ e ∈ new, e.target.label ∈ exitsOf env l
  fresh : σ.fresh ≤ σ'.fresh
  degs : ∀ t < env.n, envHead env t = false → deg σ' t = deg σ t - (exitsOf env l).count t
  queue : ∃ new, σ'.queue = new ++ σ.queue ∧ (∀ t ∈ new, t ∈ exitsOf env l ∧ envHead env t = false ∧ deg σ' t = 0) ∧
    ((∀ t < env.n, envHead env t = false → (exitsOf env l).count t ≤ deg σ t) → new.Nodup)
  settles : (envHead env l = false → l ∉ exitsOf env l) → SettledCore c (envHead env) env.deadArr.toList σ' l
  mergeFresh : envHead env l = false → 2 ≤ (incS σ.walk l).length → passFresh σ'.walk l = σ.fresh
  inSizes : σ.walk.incoming.size = σ.walk.incomingImpl.size → σ'.walk.incoming.size = σ'.walk.incomingImpl.size
  impBelow : IncomingBelow σ.walk σ.fresh → IncomingBelow σ'.walk σ'.fresh
  extendsWalk : WalkExtends σ.walk σ'.walk
  vacuity : CachedVacuity G env.claimed σ.unsat → CachedVacuity G env.claimed σ'.unsat
  origin : VisitOrigin env σ'.walk σ'.answers l
  regionFrame : ∀ t, t ∉ exitsOf env l → σ'.regionIn[t]? = σ.regionIn[t]?
  regionMono : ∀ (t : Nat) (e : SinglePass.RegionState), e ∈ σ.regionIn[t]! → e ∈ σ'.regionIn[t]!
  regionSizes : σ'.regionIn.size = σ.regionIn.size
  regionalOrigin : (envHead env l = false → l ∉ exitsOf env l) → RegionalOrigin env σ' l

omit [Labels ι] in
theorem visB_frame {w w' : SinglePass.Walk ι} {t : Nat} (h : w'.labels[t]? = w.labels[t]?) : visB w' t = visB w t := by
  unfold visB; rw [h]

omit [Labels ι] in
theorem incS_frame {w w' : SinglePass.Walk ι} {t : Nat} (h : w'.incoming[t]? = w.incoming[t]?) : incS w' t = incS w t := by
  unfold incS; rw [h]

/-- **A visit keeps the walk's invariant** (`VisitFacts`, the answers
growing by a prefix). The visited label `l` is the queue's first: below
the bound, reached, unvisited, with no exit left to come in where it is no
head; an exit's count is at most its target's in-degree (`l` is among the
labels `pend` counts), so `l` is no exit of its own where it is no head,
and no visited label other than a head is an exit of `l`: their records
and what came into them stay as they were (`Settled.frame`). -/
theorem recInv_visit {c : Target.RunCall G I} {env : SinglePass.WalkEnv ι G I} {σ σ' : SinglePass.WalkState ι G}
    {l : Nat} {rest : List Nat} (hE : EnvFacts c env) (hI : RecInv c env σ) (hq : σ.queue = l :: rest)
    (hF : VisitFacts c env { σ with queue := rest } l σ') (hk : SumsPrefix σ.answers σ'.answers) :
    RecInv c env σ' := by
  have hl := hI.queue l (by rw [hq]; exact List.mem_cons_self ..)
  obtain ⟨hln, hlR, hlv, hld⟩ := hl
  have hlmem : l ∈ List.range env.n := List.mem_range.mpr hln
  -- An exit's count is at most its target's in-degree.
  have hcount : ∀ t < env.n, envHead env t = false → (exitsOf env l).count t ≤ deg σ t := by
    intro t ht hg
    rw [hI.degs t ht hg]
    have := le_sum_of_mem (fun s => if envReached env s && !visB σ.walk s then (exitsOf env s).count t else 0)
      (List.range env.n) l hlmem
    simp only [hlR, hlv, Bool.not_false, Bool.and_self, if_true] at this
    exact this
  have hnotexit : ∀ t < env.n, envHead env t = false → deg σ t = 0 → t ∉ exitsOf env l := by
    intro t ht hg h0 hm
    have := hcount t ht hg
    have hpos := List.count_pos_iff.mpr hm
    omega
  have hself : envHead env l = false → l ∉ exitsOf env l := fun hg => hnotexit l hln hg (hld hg)
  have hvisOld : ∀ t, visB σ.walk t = true → envHead env t = false → t ∉ exitsOf env l := fun t hv hg =>
    hnotexit t (hI.visR t hv).1 hg (hI.visDeg t hv hg)
  have hvis : ∀ t, t ≠ l → visB σ'.walk t = visB σ.walk t := fun t ht => visB_frame (hF.labels t ht)
  have hdeg_le : ∀ t < env.n, envHead env t = false → deg σ' t ≤ deg σ t := fun t ht hg => by
    rw [hF.degs t ht hg]; exact Nat.sub_le _ _
  obtain ⟨newQ, hQ, hnewQ, hnodupQ⟩ := hF.queue
  have hnodupNew := hnodupQ hcount
  have hrest := (List.nodup_cons.mp (hq ▸ hI.nodup))
  -- A label queued now is unvisited and outside the rest.
  have hnew_deg : ∀ t ∈ newQ, deg σ t ≠ 0 := fun t ht h0 =>
    hnotexit t (hF.exits t (hnewQ t ht).1) (hnewQ t ht).2.1 h0 (hnewQ t ht).1
  have hnew_ne : ∀ t ∈ newQ, t ≠ l := fun t ht htl => by
    subst htl; exact hself (hnewQ t ht).2.1 (hnewQ t ht).1
  refine { nodup := ?_, queue := ?_, visR := ?_, visDeg := ?_, exits := ?_, count := ?_, size := ?_, degs := ?_,
           inLen := ?_, inSizes := hF.inSizes hI.inSizes, inVis := ?_, edgesVis := ?_, push := ?_, startFresh := ?_,
           startBelow := hI.startBelow.mono hF.fresh, impBelow := hF.impBelow hI.impBelow, vacuity := hF.vacuity hI.vacuity, settled := ?_, origins := ?_, regionalOrigins := ?_, regionSizes := hF.regionSizes.trans hI.regionSizes }
  · rw [hQ]
    refine List.nodup_append.mpr ⟨hnodupNew, hrest.2, fun a ha b hb hab => ?_⟩
    subst hab
    have := (hI.queue a (by rw [hq]; exact List.mem_cons_of_mem _ hb)).2.2.2 (hnewQ a ha).2.1
    exact hnew_deg a ha this
  · intro x hx
    rw [hQ] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨hxe, hxg, hx0⟩ := hnewQ x hx
      have hxn := hF.exits x hxe
      refine ⟨hxn, hE.closed l x hlR hxe hxn, ?_, fun _ => hx0⟩
      rw [hvis x (hnew_ne x hx)]
      cases hv : visB σ.walk x with
      | false => rfl
      | true => exact absurd hxe (hvisOld x hv hxg)
    · have hxq := hI.queue x (by rw [hq]; exact List.mem_cons_of_mem _ hx)
      have hxl : x ≠ l := fun h => hrest.1 (h ▸ hx)
      refine ⟨hxq.1, hxq.2.1, by rw [hvis x hxl]; exact hxq.2.2.1, fun hg => ?_⟩
      have := hdeg_le x hxq.1 hg
      have := hxq.2.2.2 hg
      omega
  · intro t ht
    by_cases htl : t = l
    · subst htl; exact ⟨hln, hlR⟩
    · rw [hvis t htl] at ht; exact hI.visR t ht
  · intro t ht hg
    by_cases htl : t = l
    · subst htl; have := hdeg_le t hln hg; have := hld hg; omega
    · rw [hvis t htl] at ht
      have := hdeg_le t (hI.visR t ht).1 hg; have := hI.visDeg t ht hg; omega
  · intro s hs
    by_cases hsl : s = l
    · subst hsl; exact hF.exits
    · rw [hvis s hsl] at hs; exact hI.exits s hs
  · rw [hF.count]
    simp only
    rw [hI.count]
    exact (filter_flip (visB σ.walk) (visB σ'.walk) l hlv hF.visits hvis (List.range env.n) List.nodup_range hlmem).symm
  · rw [hF.size]; exact hI.size
  · intro t ht hg
    rw [hF.degs t ht hg, show deg { σ with queue := rest } t = deg σ t from rfl, hI.degs t ht hg]
    unfold pend
    have hsum := sum_drop (fun s => if envReached env s && !visB σ.walk s then (exitsOf env s).count t else 0)
      (fun s => if envReached env s && !visB σ'.walk s then (exitsOf env s).count t else 0) l
      (by simp [hF.visits]) (fun x hx => by simp only [hvis x hx]) (List.range env.n) List.nodup_range hlmem
    simp only [hlR, hlv, Bool.not_false, Bool.and_self, if_true] at hsum
    omega
  · intro t
    obtain ⟨ns, nis, h1, h2, h3, -⟩ := hF.pushes t
    rw [h1, h2, List.length_append, List.length_append, h3]
    simp only
    rw [hI.inLen t]
  · intro t hne
    by_cases hte : t ∈ exitsOf env l
    · exact ⟨l, hF.visits, hte⟩
    · rw [incS_frame (hF.frame t hte).1] at hne
      obtain ⟨s, hs, hts⟩ := hI.inVis t hne
      have hsl : s ≠ l := fun h => by subst h; rw [hlv] at hs; cases hs
      exact ⟨s, by rw [hvis s hsl]; exact hs, hts⟩
  · obtain ⟨newE, hE', hnewE⟩ := hF.edges
    intro e he
    rw [hE'] at he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨s, hs, hts⟩ := hI.edgesVis e he
      have hsl : s ≠ l := fun h => by subst h; rw [hlv] at hs; cases hs
      exact ⟨s, by rw [hvis s hsl]; exact hs, hts⟩
    · exact ⟨l, hF.visits, hnewE e he⟩
  · intro t x hx
    obtain ⟨ns, nis, h1, -, -, hns⟩ := hF.pushes t
    rw [h1] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hns x hx
    · exact (hI.push t x hx).mono hF.fresh
  · intro x hx
    exact Nat.lt_of_lt_of_le (hI.startFresh x hx) hF.fresh
  · intro t ht
    by_cases htl : t = l
    · subst htl
      have hcore := hF.settles hself
      refine { toSettledCore := hcore, below := fun hg h2 => ?_ }
      have hfr := hF.frame t (hself hg)
      have hinc : (ofPass σ'.walk (envHead env)).incoming t = (incS σ.walk t).zip (incI σ.walk t) := by
        simp [ofPass, hg, hfr.1, hfr.2.1, incS, incI]
      rw [hinc] at h2 ⊢
      have h2' : 2 ≤ (incS σ.walk t).length := by
        rw [List.length_zip, ← hI.inLen t, Nat.min_self] at h2; exact h2
      rw [hF.mergeFresh hg h2']
      exact ⟨fun e he => (hI.push t e.1 (List.of_mem_zip he).1).2.2, hI.startFresh⟩
    · rw [hvis t htl] at ht
      exact (hI.settled t ht).frame (hF.labels t htl) (fun hg => hF.frame t (hvisOld t ht hg)) hk hF.extendsWalk

  · intro t ht
    by_cases htl : t = l
    · subst t; exact hF.origin
    · rw [hvis t htl] at ht
      obtain ⟨σ₀, en, sd, ex, he, hs, hx, hr, hp⟩ := hI.origins t ht
      exact ⟨σ₀, en, sd, ex, he, hs, hx, (hF.labels t htl).trans hr, hp.trans hk⟩

  · intro t ht
    by_cases htl : t = l
    · subst t; exact hF.regionalOrigin hself
    · rw [hvis t htl] at ht
      obtain ⟨before, en, sd, ex, he, hs, hx, hr, hp, hb, hf, hm⟩ := hI.regionalOrigins t ht
      refine ⟨before, en, sd, ex, he, hs, hx, (hF.labels t htl).trans hr, hp.trans hk, hb,
        fun hg => (hf hg).trans (hF.regionFrame t (hvisOld t ht hg)).symm,
        fun u e he => hF.regionMono u e (hm u e he)⟩

/-- A call's setup (`SinglePass.setup` over its arguments). -/
def RunCall.setup {G : NormalGraph ι} {I : InstanceImageCheck G} (c : Target.RunCall G I) :
    Except (SinglePass.WalkStop ι G) (SinglePass.WalkEnv ι G I × SinglePass.WalkState ι G) :=
  SinglePass.setup G I c.pool c.fuel c.P c.claims c.start c.inputs c.goal c.assertions c.cuts c.candidates
    c.entryIndices c.suggestions c.known c.codes c.aliases c.passChecker c.answers c.reference c.debugNode
    c.bound c.givenImplies c.givenArgs c.ensures c.givenInputs c.entrySeparation c.observe c.tracing
    c.observeEntry c.regional

variable (ι) in
/-- **(Named hypothesis) The setup starts the walk's invariant**: where a
call's setup returns, its `env` states the call (`EnvFacts`) and the state
the first visit starts from meets `RecInv`. -/
def SetupRecords : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) env σ0,
    RunCall.setup c = .ok (env, σ0) → EnvFacts c env ∧ RecInv c env σ0

variable (ι) in
/-- **(Named hypothesis) Every visit gives `VisitFacts`**: a visit of a
call's walk that returns, from a state meeting the invariant whose queue
starts with the visited label. -/
def VisitsRecord : Prop :=
  ∀ (G : NormalGraph ι) (I : InstanceImageCheck G) (c : Target.RunCall G I) env σ0 (σ σ' : SinglePass.WalkState ι G)
    (l : Nat) (rest : List Nat), RunCall.setup c = .ok (env, σ0) → EnvFacts c env → RecInv c env σ →
    σ.queue = l :: rest → SinglePass.visit G I env { σ with queue := rest } l = .ok σ' →
    VisitFacts c env { σ with queue := rest } l σ'

/-- **The walk's invariant at its end**: where the setup starts it and every
visit gives `VisitFacts`, the state a call's returned walk ends in meets
`RecInv` under the setup's `env`, which states the call (`Drives.inv`,
`recInv_visit`, `visitsKeepSummaries`). -/
theorem walk_inv (hs : SetupRecords ι) (hv : VisitsRecord ι) {G : NormalGraph ι} {I : InstanceImageCheck G}
    {c : Target.RunCall G I} {σ : SinglePass.WalkState ι G} {reach : Nat} (hw : RunCall.walk c = .ok (σ, reach)) :
    ∃ env, EnvFacts c env ∧ RecInv c env σ ∧ reach = (env.reached.toList.filter id).length := by
  unfold RunCall.walk SinglePass.runWalk at hw
  cases hr : RunCall.setup c with
  | error stop =>
    unfold RunCall.setup at hr
    simp only [hr, bind, Except.bind] at hw
    cases hw
  | ok p =>
    obtain ⟨env, σ0⟩ := p
    have hr' := hr
    unfold RunCall.setup at hr'
    obtain ⟨hE, hI0⟩ := hs G I c env σ0 hr
    cases hd : SinglePass.drive (SinglePass.visit G I env) (env.n + 1) σ0 with
    | error stop =>
      simp only [hr', hd, bind, Except.bind] at hw
      cases hw
    | ok σf =>
      simp only [hr', hd, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hdr := drives_of_drive _ _ _ hd
      have hinv := Drives.inv (RecInv c env)
        (fun σ σ₁ l rest hq hI hvis => recInv_visit hE hI hq (hv G I c env σ0 σ σ₁ l rest hr hE hI hq hvis)
          ((visitsKeepSummaries ι G I env).1 { σ with queue := rest } l σ₁ hvis)) hdr hI0
      exact ⟨env, hE, hinv, rfl⟩

/-- **(`recordsSound_of`) The driver's record of every returned walk is
sound** (`RecordsSound`), where the setup starts the invariant and every
visit gives `VisitFacts`: the invariant holds at the walk's end
(`walk_inv`), and `recordSound_of_inv` reads the record from it. -/
theorem recordsSound_of (hs : SetupRecords ι) (hv : VisitsRecord ι) :
    RecordsSound ι := by
  intro G I c σ reach hw hle hsums
  obtain ⟨env, hE, hinv, rfl⟩ := walk_inv hs hv hw
  exact recordSound_of_inv hE hinv hle hsums

/-- **(`recordsChecked_of`) The driver checked every node its record
visits** (`RecordsChecked`), where the setup starts the invariant and
every visit gives `VisitFacts`: at the walk's end every visited label is
settled (`walk_inv`), its node checked with `NodePassChecked` in the
setup's no-return region `deadArr`, at the record and the final answers. -/
theorem recordsChecked_of (hs : SetupRecords ι) (hv : VisitsRecord ι) : RecordsChecked ι := by
  intro G I c σ reach hw _ hsums
  obtain ⟨env, hE, hinv, -⟩ := walk_inv hs hv hw
  refine ⟨env.deadArr.toList, fun l hl => ?_⟩
  have hl' := (ofPass_visited _ _ _).mp hl
  have hset := hinv.settled l hl'
  rw [hE.heads] at hset
  exact hset.node σ.walk σ.answers rfl (WalkExtends.refl _) (SumsPrefix.refl _) hsums

end Records

end Verification.TolerantFrames
