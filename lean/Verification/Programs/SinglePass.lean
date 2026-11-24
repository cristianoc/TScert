import Verification.Programs.WorkTable
import Verification.Programs.DebugText
import Verification.Programs.CertificateProducer
import Verification.Programs.GraphCode
import Verification.Programs.SinglePassStats
import Verification.Programs.ArgumentRegionCertificates
import Verification.Semantics.ExitSummaries
-- PointerEquality.lean gives the pointer-equality fast path at a type variable; without it the generic fast equality does not compile.
import Verification.Semantics.PointerEquality
import Verification.Programs.LocalConfinement

/-! One forward pass over a graph cut at its statement entries
(docs/SINGLE-PASS.md): each node visited once, in a topological order
of the graph without the edges into cuts; bindings named once, by where they
are introduced; facts stored over names, indexed by the names they mention;
each step's proved rule applied to the facts over the names its expression
mentions, at the slots the node's table gives. Untrusted: a verdict of this
pass is not an acceptance. -/
namespace Verification.SinglePass
open ProgramTyping ControlFlow CertificateProducer PositiveCertificates PositiveGraphs ProgramCertificates
open HeapKnowledge (Knowledge IndexAtom ElemAtom)

deriving instance Hashable for HeapFacts.Fact

/-- One fact of a knowledge, over names. -/
inductive Atom where
  | cell (f : HeapFacts.Fact)
  | value (f : HeapFacts.Fact)
  | link (g : HeapLinks.Link)
  | elem (a : ElemAtom)
  | index (a : IndexAtom)
  /-- A separation fact, its subject and partners at slots (or names), not
  at levels. -/
  | sep (f : HeapSeparation.Fact)
  deriving DecidableEq, Hashable

/-- Atom equality as the compiled verifier decides it
(`instDecidableEqAtom_eq_fast`): by constructor, the fields answered at once
where they are one object (`ProgramCertificates.decideSame`). -/
def Atom.sameFast : Atom → Atom → Bool
  | .cell f, .cell g | .value f, .value g => ProgramCertificates.decideSame f g
  | .link f, .link g => ProgramCertificates.decideSame f g
  | .elem f, .elem g => ProgramCertificates.decideSame f g
  | .index f, .index g => ProgramCertificates.decideSame f g
  | .sep f, .sep g => ProgramCertificates.decideSame f g
  | _, _ => false

def Atom.decEqFast : DecidableEq Atom := fun a b =>
  decidable_of_iff (Atom.sameFast a b = true) (by
    cases a <;> cases b <;> simp [Atom.sameFast, ProgramCertificates.decideSame_iff])

@[csimp] theorem instDecidableEqAtom_eq_fast : @instDecidableEqAtom = @Atom.decEqFast := by
  funext a b
  exact Subsingleton.elim _ _

def Atom.names : Atom → List Nat
  | .cell f | .value f => [f.slot]
  | .link g => [g.cell, g.value]
  | .elem a => a.slot :: a.cond.toList
  | .index a => a.fact.slots ++ a.cond.toList
  | .sep f => f.slot :: f.partners.map (·.1)

def Atom.rename (f : Nat → Option Nat) : Atom → Option Atom
  | .cell x => (f x.slot).map fun s => .cell { x with slot := s }
  | .value x => (f x.slot).map fun s => .value { x with slot := s }
  | .link g => do
    let c ← f g.cell
    let v ← f g.value
    pure (.link { g with cell := c, value := v })
  | .elem a => do
    let s ← f a.slot
    let c ← a.cond.mapM f
    pure (.elem { a with slot := s, cond := c })
  | .index a => (HeapKnowledge.mapIndex f a).map .index
  | .sep x => do
    let s ← f x.slot
    let ps ← x.partners.mapM fun (p, fs) => (f p).map (·, fs)
    pure (.sep { x with slot := s, partners := ps })

/-- A fact restated under a renaming that may give a name several new
names: once per choice of each name's new name (at most 16 choices); a name
the renaming does not give keeps its own. -/
def Atom.renameEach (m : Std.HashMap Nat (List Nat)) (a : Atom) : List Atom :=
  let choices : List (List (Nat × Nat)) := a.names.eraseDups.foldl (fun acc x => match m.get? x with
    | some φs => (acc.flatMap fun c => φs.map fun φ => (x, φ) :: c).take 16
    | none => acc) [[]]
  choices.filterMap fun c => a.rename fun x => some ((c.lookup x).getD x)

/-- A separation fact between levels and slots, at depth `d`. -/
def flip (d : Nat) (f : HeapSeparation.Fact) : HeapSeparation.Fact :=
  ⟨d - 1 - f.slot, f.fields, f.partners.map fun (p, fs) => (d - 1 - p, fs)⟩

/-- A knowledge's facts, its separation's at slots. -/
def atomsOf (k : Knowledge) : List Atom :=
  let d := k.separation.depth
  k.cells.map .cell ++ k.values.map .value ++ k.links.map .link ++ k.elems.map .elem ++ k.indices.map .index ++
    k.separation.facts.map fun f => .sep (flip d f)

/-- The knowledge of facts at slots, its separation at depth `d`. -/
def ofAtoms (as : List Atom) (d : Nat) : Knowledge :=
  let k : Knowledge := as.foldr (fun a (k : Knowledge) => match a with
    | .cell f => { k with cells := f :: k.cells }
    | .value f => { k with values := f :: k.values }
    | .link g => { k with links := g :: k.links }
    | .elem e => { k with elems := e :: k.elems }
    | .index i => { k with indices := i :: k.indices }
    | .sep f => { k with separation := { k.separation with facts := f :: k.separation.facts } }) {}
  let seps := k.separation.facts.filter fun f => f.slot < d && f.partners.all (·.1 < d)
  { k with separation := HeapSeparation.norm d (seps.map (flip d)) }

/-- The facts a state holds, over names, and by each name the live facts
that mention it. -/
structure Store where
  live : Std.HashSet Atom := {}
  /-- Each name's list holds no fact twice: a fact is listed once under
  each of its distinct names, and only while live. -/
  byName : Std.HashMap Nat (List Atom) := {}

/-- The form and condition of an unconditional or conditional linear bound
`F ≤ d`, and `d`: one fact is kept per form and condition. -/
def Atom.linearKey : Atom → Option ((Linear.Form HeapKnowledge.Term × Option Nat × Bool) × Int)
  | .index ⟨.linear (.le F d), c, neg⟩ => some ((Linear.normalize F, c, neg), d)
  | _ => none

/-- A fact in one form: an unconditional fact's `negated`, which only a
condition reads, cleared. -/
def Atom.canon : Atom → Atom
  | .index ⟨f, none, true⟩ => .index ⟨f, none, false⟩
  | .elem e => if e.cond.isNone && e.negated then .elem { e with negated := false } else .elem e
  | a => a

/-- The fact `0 ≤ -1`, which holds at no environment: the one form a store
keeps of a false constant. -/
def Atom.bot : Atom := .index ⟨.linear (.le [] (-1)), none, false⟩

/-- Whether a fact is a true constant: a linear fact over no term, `0 ≤ d`
with `0 ≤ d` or `0 ≠ d` with `d ≠ 0`, under any condition. A form whose
terms cancel is no constant: it states each of its terms defined. -/
def Atom.trivial : Atom → Bool
  | .index ⟨.linear (.le [] d), _, _⟩ => decide (0 ≤ d)
  | .index ⟨.linear (.ne [] d), _, _⟩ => d != 0
  | _ => false

/-- Whether an unconditional fact is a false constant: a linear fact whose
form normalizes to no term (`Linear.normalize`), `0 ≤ d` with `d < 0` or
`0 ≠ 0`; it holds at no environment (`contradiction_false`). -/
def Atom.contradiction : Atom → Bool
  | .index ⟨.linear (.le F d), none, _⟩ => decide (d < 0) && (Linear.normalize F).isEmpty
  | .index ⟨.linear (.ne F d), none, _⟩ => d == 0 && (Linear.normalize F).isEmpty
  | _ => false

/-- A fact inserted as it is: live, and listed under each of its names. -/
def Store.insert (s : Store) (a : Atom) : Store :=
  if s.live.contains a then s else
  { live := s.live.insert a,
    byName := a.names.eraseDups.foldl (fun m n => m.insert n (a :: m.getD n [])) s.byName }

/-- A fact added in its canonical form: a true constant (`Atom.trivial`) is
not added, and a false one (`Atom.contradiction`) is added as `Atom.bot`. -/
def Store.addRaw (s : Store) (a : Atom) : Store :=
  let a := a.canon
  if a.trivial then s else s.insert (if a.contradiction then .bot else a)

/-- Whether the store holds `Atom.bot`: its facts hold at no environment
(`storeOk_impossible`), so the state is one no execution reaches. -/
def Store.impossible (s : Store) : Bool := s.live.contains .bot

def Store.remove (s : Store) (a : Atom) : Store :=
  let a := a.canon
  if s.live.contains a then
    { live := s.live.erase a,
      -- Off each name's list: the index holds live facts only.
      byName := a.names.eraseDups.foldl (fun m n => m.insert n ((m.getD n []).erase a)) s.byName }
  else s

/-- A fact added; of a linear bound, one per form and condition, the
strongest: a bound the store already states as strongly is not added, and a
stronger one replaces the weaker. -/
def Store.addBound (s : Store) (a : Atom) : Store :=
  let a := a.canon
  if s.live.contains a then s else
  match a.linearKey with
  | some (key, d) =>
    let same := (s.byName.getD (a.names.headD 0) []).filter fun b => match b.linearKey with
      | some (key', _) => key' == key
      | none => false
    if same.any (fun b => match b.linearKey with | some (_, d') => d' ≤ d | none => false) then s
    else (same.foldl Store.remove s).addRaw a
  | none => s.addRaw a

/-- A fact added (`addBound`); a length atom also as the linear facts it
means (`HeapKnowledge.atomLinear`), the form the call layers keep or drop. -/
def Store.add (s : Store) (a : Atom) : Store :=
  let a := a.canon
  if s.live.contains a then s else
  let s := match a with
    | .index ⟨f@(.length _ _), c, neg⟩ => (HeapKnowledge.atomLinear f).foldl (fun (s : Store) F =>
        s.addBound (.index ⟨.linear F, c, neg⟩)) s
    | _ => s
  s.addBound a

def Store.about (s : Store) (n : Nat) : List Atom := s.byName.getD n []

/-- The name a read link of the store gives the field `f` of the object
named `o`: the value `y` of a read link `o.f ↦ y`, which states that `o`'s
field `f` holds `y` in the current heap. -/
def Store.readName (s : Store) (o : Nat) (f : PropKey) : Option Nat :=
  (s.about o).findSome? fun
    | .link g => if !g.alias && g.cell == o && g.field == f then some g.value else none
    | _ => none

def Store.size (s : Store) : Nat := s.live.size

def Store.toList (s : Store) : List Atom := s.live.toList

/-- Whether an unconditional fact of the store makes the name's value an
integer: a linear fact over its value, or an `int`, `index`, length or
bound fact giving it (`IndexFact.HoldsAt`). -/
def Store.integral (s : Store) (x : Nat) : Bool :=
  (s.about x).any fun a => match a with
    | .index ⟨f, none, _⟩ => match f with
      | .int k | .index k | .length _ k | .bound _ k _ => k == x
      | .linear F => F.vars.contains (HeapKnowledge.Term.value x)
      | _ => false
    | _ => false

/-- A program point's state: the name at each slot, the facts. -/
structure State where
  names : List Nat
  store : Store := {}
  /-- The names holding a spine this run allocated (`GraphCode.inferFresh`'s
  facts, over names). -/
  fresh : List Nat := []

mutual
/-- The slots a term reads, below its binders; none for a term whose reads
are not listed here. -/
def mentioned (d : Nat) : Tm → Option (List Nat)
  | .var i => some (if i ≥ d then [i - d] else [])
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => some []
  | .objAt _ .absent _ => some []
  | .makeAt .absent _ args => mentionedAll d args
  | .objAt _ (.bound t r pre) _ => do pure ((← mentioned d t) ++ (← mentioned d r) ++ (← mentionedAll d pre))
  | .makeAt (.bound t r pre) _ args =>
    do pure ((← mentioned d t) ++ (← mentioned d r) ++ (← mentionedAll d pre) ++ (← mentionedAll d args))
  | .objAt _ (.graph _ _ _ _ caps _ _ _) _ => mentionedAll d caps
  | .makeAt (.graph _ _ _ _ caps _ _ _) _ args => do pure ((← mentionedAll d caps) ++ (← mentionedAll d args))
  | .letE a b => do pure ((← mentioned d a) ++ (← mentioned (d+1) b))
  | .invoke f r args => do pure ((← mentioned d f) ++ (← mentioned d r) ++ (← mentionedAll d args))
  | .construct f args => do pure ((← mentioned d f) ++ (← mentionedAll d args))
  | .writeAt _ a b | .arith _ a b | .elemAt a b | .indexAt a b | .merge _ a b | .makeKey a b =>
    do pure ((← mentioned d a) ++ (← mentioned d b))
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => mentioned d a
  | .setElem a b c => do pure ((← mentioned d a) ++ (← mentioned d b) ++ (← mentioned d c))
  | .arrLit args => mentionedAll d args
  | .ite c a b => do pure ((← mentioned d c) ++ (← mentioned d a) ++ (← mentioned d b))
  | _ => none
def mentionedAll (d : Nat) : List Tm → Option (List Nat)
  | [] => some []
  | a :: as => do pure ((← mentioned d a) ++ (← mentionedAll d as))
end

/-- Nanoseconds this process spent in `run`: a measurement. -/
initialize passNanos : IO.Ref Nat ← IO.mkRef 0

/-- Nanoseconds and applications per term kind: a measurement. -/
initialize kindNanos : IO.Ref (Std.HashMap String (Nat × Nat)) ← IO.mkRef {}


private unsafe def timedKindImpl {α : Type} (kind : String) (f : Unit → α) : α :=
  if !(unsafeBaseIO profiling.get) then f () else
  match unsafeIO (do
      let t0 ← IO.monoNanosNow
      let a ← IO.lazyPure f
      let t1 ← IO.monoNanosNow
      kindNanos.modify fun m => let (t, n) := m.getD kind (0, 0); m.insert kind (t + (t1 - t0), n + 1)
      pure a) with
  | .ok a => a
  | .error _ => f ()

private unsafe def clockImpl (kind : String) (since : Nat) (_ : Nat) : Nat :=
  if !(unsafeBaseIO profiling.get) then 0 else
  match unsafeIO (do
      let t ← IO.monoNanosNow
      if since != 0 then
        kindNanos.modify fun m => let (u, n) := m.getD kind (0, 0); m.insert kind (u + (t - since), n + 1)
      pure t) with
  | .ok t => t
  | .error _ => 0

/-- Measuring (`profiling`): the time since `since` added to `kind`'s, and
the time now; `at` orders the call after what computed it. -/
@[implemented_by clockImpl] def clock (_kind : String) (_since : Nat) (_at : Nat) : Nat := 0

private unsafe def dumpWalkImpl {α : Type} (text : Unit → String) (a : α) : α :=
  if !(unsafeBaseIO dumping.get) then a else dbgTrace (text ()) fun _ => a

/-- `a`, after printing `text ()` where walks are dumped (`dumping`,
`TSCERT_DUMP`). -/
@[implemented_by dumpWalkImpl] def dumpWalk {α : Type} (_text : Unit → String) (a : α) : α := a

/-- `f ()`, its time added to `kind`'s. -/
@[implemented_by timedKindImpl] def timedKind {α : Type} (_kind : String) (f : Unit → α) : α := f ()


/-- **A step's local effect** as its footprint check reads it: the closed
footprints the check's rules grant the step on normal return (`within`)
and on a throw (`throws`), each read from the step's evidence and none from
a bound, and whether its term is in scope. An inspection, an empty type,
or an empty context's type keeps everything; a typed write, an
initializing write and a call at its selected signature grant their own
grades (`ExpressionEffects.writeGrades`, `initWriteGrades`,
`GraphCode.selectedGrades`). -/
structure StepGrades where
  within : List Footprints.Closed
  «throws» : List Footprints.Closed
  scope : Bool

/-- **A step's local certificate**: for each exit, the exit specifications
its rules establish (`CallEffects.ExitSpec`: a frame read at the step's call
positions and the postconditions it states), each read from the step's
evidence and none from a bound; the call positions holding a fresh spine,
whose entries a frame's closed bound below the invocation's mark discharges
(`GraphCode.freshPositions`, `Footprint.boundBelow`); and whether its term is
in scope. -/
structure StepCertificate where
  normal : List CallEffects.ExitSpec
  exceptional : List CallEffects.ExitSpec
  fresh : List Nat
  scope : Bool

/-- **The grades a certificate projects to**: each exit specification's
frame closed below the mark (`Footprint.boundBelow`). -/
def StepCertificate.grades (q : StepCertificate) : StepGrades :=
  { within := q.normal.map fun x => Footprints.Footprint.boundBelow q.fresh x.frame
    throws := q.exceptional.map fun x => Footprints.Footprint.boundBelow q.fresh x.frame
    scope := q.scope }

/-- **A visit's record of its step's local effect**: the label visited, its
step's local certificate (`stepCertificate`), the grades its footprint check
reads, the certificate's projection (`VisitRecord.of_grades`), and its
result's freshness (`outFreshOf`), each over the read summaries that visit's
step left (`VisitRecord.of`). -/
structure VisitRecord where
  label : Nat
  certificate : StepCertificate
  grades : StepGrades
  outFresh : Bool
  returnAliases : List Nat := []

/-- What the pass counts. -/
structure Counts where
  visited : Nat := 0
  rules : Nat := 0
  fullRules : Nat := 0
  queries : Nat := 0
  queryAtoms : Nat := 0
  copies : Nat := 0
  edgeSearches : Nat := 0
  givenWritten : Nat := 0
  givenClaims : Nat := 0
  storeMax : Nat := 0
  directCalls : Nat := 0
  givenImplies : Nat := 0
  heads : Nat := 0
  stateSum : Nat := 0
  /-- The graph's nodes and edges (continuations and handlers). -/
  nodes : Nat := 0
  edges : Nat := 0
  /-- The nodes a path from the start reaches. -/
  reached : Nat := 0
  /-- The merges met, and the facts their predecessors state that the met
  store lacks. -/
  merges : Nat := 0
  mergeDiffs : Nat := 0
  /-- Under `grading` (`run`), each visit's record of its step's local
  effect (`Walk.visits`); empty otherwise. -/
  grades : Array VisitRecord := #[]

/-- The counts as one JSON object (`TSCERT_COUNTS`, `dev/perf-gate.mts`). -/
def Counts.json (c : Counts) : String :=
  "{" ++ ", ".intercalate ([("nodes", c.nodes), ("edges", c.edges), ("reached", c.reached),
    ("visited", c.visited), ("rules", c.rules), ("wholeStoreRules", c.fullRules),
    ("queries", c.queries), ("queryFacts", c.queryAtoms), ("merges", c.merges),
    ("mergeDiffs", c.mergeDiffs), ("stateFactsSum", c.stateSum), ("stateFactsMax", c.storeMax),
    ("headsWritten", c.givenWritten), ("headsFromClaims", c.givenClaims),
    ("headsSupplied", c.givenImplies), ("heads", c.heads), ("copies", c.copies),
    ("edgeSearches", c.edgeSearches), ("directCalls", c.directCalls)].map fun (k, v) => s!"\"{k}\":{v}") ++ "}"

instance : ToString Counts where
  toString c := s!"visited {c.visited}, rule applications {c.rules} (whole store {c.fullRules}), copies {c.copies}, entailment queries {c.queries} (mean atoms {c.queryAtoms / max c.queries 1}), edge searches {c.edgeSearches}, head facts written {c.givenWritten} + from claims {c.givenClaims}, largest store {c.storeMax}, calls read off their signature {c.directCalls}, head implications supplied {c.givenImplies}, loop heads {c.heads}, mean facts per state {c.stateSum / max c.visited 1}"

/-- The state at a node, at its slots: on entry, after its step (the
result at slot 0), and at a merge each predecessor's at the merge's slots. -/
structure Observation (ι : Type) where
  label : Nat
  before : Knowledge
  after : Knowledge
  preds : List (Nat × Knowledge) := []
  /-- At a merge, its names by slot and each predecessor's. -/
  names : List (List Nat) := []
  /-- The implications on entry, at its slots. -/
  implies : List (PromiseCalls.Implication ι) := []

/-- One precondition of a refused step, as its diagnostic reads it: an
elements precondition on the receiver slot, with whether it holds, and
each atom of its index facts, at the step's slots (none where an atom
names a position the step holds no slot for), with whether it holds, each
decided by the check acceptance uses for it. -/
structure StatedPrecondition where
  «requires» : Option (Nat × CallEffects.ElemPred × Bool) := none
  atoms : List (Option HeapKnowledge.IndexFact × Bool) := []

/-- The form of a step whose preconditions a diagnostic reads: a call, a
construction or a write of an element at a run-time index. -/
inductive StepForm where
  | call | construction | write

/-- What a refused step's diagnostic carries: its form, its preconditions
(`StatedPrecondition`; of a call or a construction, one per distinct
precondition the callee's signatures state; of an element write, the
bound its rule requires) and the facts connected to the step's slots
(`component`). -/
structure StepPreconditions where
  step : StepForm
  signatures : List StatedPrecondition
  known : Knowledge

/-- What an edge into a statement entry or an asserted target is refused
for: facts the target requires; a given implication (from its test slot
to its target slot); a slot stated to hold an input's entry value; a slot
stated to hold the promised input; slots at the target. -/
inductive EdgeRequirement where
  | facts
  | implication (test target : Nat)
  | inputValue (slot input : Nat)
  | promisedInput (slot : Nat)

/-- What a refused edge's diagnostic carries: its node `source`, its target
`target`, its exit's position among the node's (`Exit.ofNode`), the thrown
value's type where it is the handler's, what it is refused for; the facts
the target requires (`required`), split into those the edge establishes
and those it does not, each decided alone, with the requirement's links,
by the check that decides the whole; and the facts the edge holds over the
slots the mapping reads, as the check reads them, restated at every target
slot reading each (`known`), over the requirement's slots. All at the
target's slots. -/
structure EdgeFacts (ι : Type) where
  source : Nat
  target : Nat
  exit : Nat
  thrown : Option (Ty ι)
  requirement : EdgeRequirement
  required : Knowledge
  established : Knowledge
  lacking : Knowledge
  known : Knowledge

/-- What a return refused for its postcondition carries: each fact of the
postcondition (at the return's pushed slots, the result at 0; none for a
fact over an input no slot holds the entry value of), with whether the
return's facts entail it, decided alone by the check that decides the
whole (`GraphCode.returnEntails`), and the return's facts over those
slots. -/
structure ReturnFacts where
  facts : List (Option HeapKnowledge.IndexFact × Bool)
  known : Knowledge

/-- The explanatory data a refusal carries for its diagnostic: of a step's,
its preconditions; of an edge's, its facts; of a return's postcondition,
its facts. -/
inductive RefusalDetail (ι : Type) where
  | step (d : StepPreconditions)
  | edge (d : EdgeFacts ι)
  | postcondition (d : ReturnFacts)

/-- The verdict: refused at a located obligation, a construct the pass
does not handle, or the state observed at a chosen node. A refusal of an
edge into a statement entry for lacking given facts carries the entry and
those facts (`lacks`), as data; a refusal of a step or an edge, its
diagnostic's data (`RefusalDetail`), deferred to where the refusal is
printed. -/
inductive Outcome (ι : Type) where
  | accepted
  | refused (why : String) (lacks : Option (Nat × List HeapKnowledge.Candidate) := none)
      (detail : Option (Thunk (Option (RefusalDetail ι))) := none)
  /-- Refused at node `l`'s footprint check (`GraphCode.nodeChecked`): the
  one refusal a regional check may still answer. -/
  | outsideBound (l : Nat)
  | notHandled (what : String)
  | observed (o : Observation ι)

instance : ToString (Outcome ι) where
  toString
    | .accepted => "accepted"
    | .refused w _ _ => s!"refused: {w}"
    | .outsideBound l => s!"refused: footprint at node {l}"
    | .notHandled w => s!"not handled: {w}"
    | .observed o => s!"observed node {o.label}"

/-- A refusal at a footprint stated as its text. -/
def Outcome.asRefusal : Outcome ι → Outcome ι
  | .outsideBound l => .refused s!"footprint at node {l}"
  | o => o

/-- A node's exit: an edge of its continuation, with whether it pushes the
result, the observation of the result it makes (a `branchBind` or
`tagBind` arm) and the answer a `branch` arm promotes; or its handler's
edge, which pushes the thrown value. -/
inductive Exit where
  | normal (target : Target) (pushed : Bool) (observed : Option BranchRefinement.Observation) (promote : Option Bool)
  | handler (target : Target)

def Exit.target : Exit → Target
  | .normal t .. | .handler t => t

def Exit.pushed : Exit → Bool
  | .normal _ p .. => p
  | .handler _ => true

def Exit.observed : Exit → Option BranchRefinement.Observation
  | .normal _ _ o _ => o
  | .handler _ => none

def Exit.promote : Exit → Option Bool
  | .normal _ _ _ q => q
  | .handler _ => none

def Exit.isHandler : Exit → Bool
  | .normal .. => false
  | .handler _ => true

/-- A node's exits: its continuation's edges in order, then its handler's. -/
def Exit.ofNode (node : Node) : List Exit :=
  (match node.continuation with
  | .ret => []
  | .bind t => [.normal t true none none]
  | .effect t => [.normal t false none none]
  | .branch y m => [.normal y false none (some true), .normal m false none (some false)]
  | .branchBind y m => [.normal y true (some (.boolean true)) none, .normal m true (some (.boolean false)) none]
  | .tagBind tg y m => [.normal y true (some (.tag tg true)) none, .normal m true (some (.tag tg false)) none]) ++
  node.handler.toList.map .handler

/-- The first slot holding each name of `want` (every name, `whole`). -/
def slotTable (names : List Nat) (want : Std.HashSet Nat) (whole : Bool) : Std.HashMap Nat Nat := Id.run do
  let mut t : Std.HashMap Nat Nat := {}
  let mut i := 0
  let mut found := 0
  for n in names do
    if whole || want.contains n then
      if !t.contains n then
        t := t.insert n i
        found := found + 1
        if !whole && found == want.size then return t
    i := i + 1
  return t

/-- The names a selected fact chains through: an alias or read link's, and
with `chain` a linear fact's (the facts an entailment over the given names
may chain through). -/
def Atom.through (chain : Bool) (a : Atom) : List Nat := match a with
  | .link g => [g.cell, g.value]
  | .index x => match x.fact with
    | .linear _ => if chain then a.names else []
    | _ => []
  | _ => []

/-- The array and index of an element read, or the array of a quantified
fact. Observations select these witnesses together to instantiate the
body after a guard is discharged. -/
def elementDependencies : HeapKnowledge.IndexFact → List Nat
  | .element _ a idx => a :: idx.slots
  | .every a _ _ _ _ => [a]
  | .guarded _ _ _ body => elementDependencies body
  | _ => []

/-- The selector for ordinary steps and for observations that can use
element reads and quantified facts together. -/
def Atom.selectionThrough (chain observeElements : Bool) (a : Atom) : List Nat :=
  if observeElements then match a with
    | .index x => a.through chain ++ elementDependencies x.fact
    | _ => a.through chain
  else a.through chain

/-- One round of the selective worklist: each fact over a frontier name
not yet kept, kept in order; each name it chains through not yet seen,
seen and on the next frontier. -/
def selectRound (s : Store) (through : Atom → List Nat) (frontier : List Nat) (seen : Std.HashSet Nat)
    (kept : Std.HashSet Atom) (out : Array Atom) : List Nat × Std.HashSet Nat × Std.HashSet Atom × Array Atom :=
  frontier.foldl (fun acc x => (s.about x).foldl (fun (next, seen, kept, out) a =>
    if kept.contains a then (next, seen, kept, out) else
    (through a).foldl (fun (next, seen, kept, out) y =>
      if seen.contains y then (next, seen, kept, out) else (y :: next, seen.insert y, kept, out))
      (next, seen, kept.insert a, out.push a)) acc) ([], seen, kept, out)

/-- The value facts of names mentioned by collected facts that were not on the
frontier: leaf facts only, with no further chaining. -/
def selectValues (s : Store) (seen : Std.HashSet Nat) (kept : Std.HashSet Atom) (out : Array Atom) : Array Atom :=
  (out.toList.foldl (fun acc a =>
    a.names.foldl (fun (sn, kp, o) n =>
      if sn.contains n then (sn, kp, o) else
      (s.about n).foldl (fun (sn, kp, o) b => match b with
        | .value _ => if kp.contains b then (sn, kp, o) else (sn, kp.insert b, o.push b)
        | _ => (sn, kp, o)) (sn.insert n, kp, o)) acc) (seen, kept, out)).2.2

/-- The selective worklist (`selectRound`) from `frontier` until a round
finds no new name: each round with a next frontier keeps a new fact, so a
fuel of the store's size and two never runs out. -/
def selectFrom (s : Store) (through : Atom → List Nat) : Nat → List Nat → Std.HashSet Nat → Std.HashSet Atom → Array Atom → Array Atom
  | 0, _, seen, kept, out => selectValues s seen kept out
  | fuel + 1, frontier, seen, kept, out =>
    if frontier.isEmpty then selectValues s seen kept out else
    let (next, seen, kept, out) := selectRound s through frontier seen kept out
    selectFrom s through fuel next seen kept out

/-- The knowledge a step reads, at slots: the facts over the names of
`slots` and over the names those facts mention, a name out of scope
eliminated from the linear facts. With `whole`, every fact. The store's
facts with their images, for the step's delta, and the table of slots. -/
def materialize (st : State) (d : Nat) (slots : List Nat) (whole : Bool) (chain : Bool := true)
    (observeElements : Bool := false) :
    Knowledge × List (Atom × Atom) × Std.HashMap Nat Nat := timedKind (if whole then "materialize whole" else "materialize") fun _ =>
  let given := slots.filterMap fun s => st.names[s]?
  let atoms : List Atom := if whole then st.store.toList else
    (selectFrom st.store (Atom.selectionThrough chain observeElements) (st.store.size + 2) given (given.foldl (·.insert ·) {}) {} #[]).toList
  let want : Std.HashSet Nat := atoms.foldl (fun acc a => a.names.foldl (·.insert ·) acc)
    (given.foldl (·.insert ·) {})
  let table := slotTable st.names want whole
  -- Names out of scope: eliminated from the linear facts, then dropped.
  let out := want.fold (fun acc n => if table.contains n then acc else n :: acc) []
  let indices := atoms.filterMap fun a => match a with | .index x => some x | _ => none
  let links := atoms.filterMap fun a => match a with | .link g => some g | _ => none
  let derived := if out.isEmpty || indices.isEmpty then [] else
    -- A term rooted at a name out of scope is restated through a read from
    -- a name in scope, where a read link gives one, then eliminated.
    let isOut := fun s => !table.contains s
    let restated := indices ++ HeapKnowledge.restateReads links isOut indices ++
      HeapKnowledge.restateSpines links isOut indices
    (HeapKnowledge.eliminateIndices out restated).drop indices.length
  let f := fun n => table.get? n
  let pairs := atoms.filterMap fun a => (a.rename f).map (a, ·)
  let extra := derived.filterMap fun x => (Atom.index x).rename f
  -- Each slot holding a name of the table that a slot before it holds is
  -- related to it by an alias link: a rule reads a value's type at any slot
  -- holding it, as a positional state's alias links relate them.
  let _ := slots
  let aliasLinks : List Atom := Id.run do
    let mut out := []
    let mut i := 0
    for n in st.names do
      if i ≥ d then break
      if let some first := table.get? n then
        if first != i then out := Atom.link { cell := first, value := i, alias := true } :: out
      i := i + 1
    return out
  (ofAtoms (pairs.map (·.2) ++ extra ++ aliasLinks) d, pairs, table)

/-- Restate an added linear fact over a read's path (`HeapKnowledge.restateReads`). -/
def restateAddedReads (s : Store) (x : HeapKnowledge.IndexAtom) (v : Nat) : Store := Id.run do
  let reads := (s.about v).filterMap fun b => match b with
    | .link g => if !g.alias && g.value == v then some g else none
    | _ => none
  if reads.isEmpty then return s
  let mut s := s
  for y in HeapKnowledge.restateReads reads (· == v) [x] do s := s.add (.index y)
  return s

/-- Whether an unconditional linear or singly guarded linear fact accesses a
projection (a length, view, bitmask or field) on `r`, or a length/mask slot of `r`. -/
def mentionsElemProj (r : Nat) (lens masks : List HeapKnowledge.IndexAtom) (F : HeapKnowledge.IndexFact) : Bool :=
  let lenSlots := lens.filterMap fun a => match a.fact with | .length _ n => some n | _ => none
  let maskSlots := masks.filterMap fun a => (HeapKnowledge.matchMaskLe r a.fact).map Prod.fst
  let hit (t : HeapKnowledge.Term) : Bool :=
    (!t.atEntry && t.slot == r && (t.kind != .value || !t.path.isEmpty)) ||
    (!t.atEntry && t.kind == .value && t.path.isEmpty && (lenSlots.contains t.slot || maskSlots.contains t.slot))
  match F with
  | .linear L => L.vars.any hit
  | .guarded s [] _ (.linear L) => s == r && L.vars.any hit
  | _ => false

/-- Source element slot of a mask equality `v - (r & mask) ≤ 0`. -/
def maskSourceOf (v : Nat) : HeapKnowledge.IndexFact → Option Nat
  | .linear (.le [(t1, 1), (t2, -1)] 0) =>
    if !t1.atEntry && t1.kind == .value && t1.path.isEmpty && t1.slot == v &&
       !t2.atEntry && t2.path.isEmpty then
      match t2.kind with
      | .bitMask _ => some t2.slot
      | _ => none
    else none
  | _ => none

/-- Restate an added linear or singly guarded linear fact over an element read's
projection (or length/bitmask slot), or an integer element read over a field-read
array, as `atIndex` (`HeapKnowledge.restateAtIndex`). -/
def restateAddedAtIndex (s : Store) (x : HeapKnowledge.IndexAtom) (v : Nat) : Store := Id.run do
  if !x.cond.isNone then
    match x.fact with
    | .linear _ =>
      let atEqs := (s.about v).filterMap fun b => match b with
        | .index a => if a.cond.isNone then match a.fact with
            | .atIndex _ _ _ none _ => some a
            | _ => none
          else none
        | _ => none
      if atEqs.isEmpty then return s
      let mut s := s
      for y in HeapKnowledge.restateAtIndex [] (· == v) (x :: atEqs) do
        s := s.add (.index y)
      return s
    | _ => return s
  match x.fact with
  | .linear _ | .guarded _ [] _ (.linear _) =>
    let elemSlots := v :: (s.about v).filterMap fun b => match b with
      | .index ⟨.length r n, none, _⟩ => if n == v then some r else none
      | .index ⟨F, none, _⟩ => maskSourceOf v F
      | _ => none
    let mut s := s
    for r in elemSlots do
      let elems := (s.about r).filterMap fun b => match b with
        | .index a => if a.cond.isNone then match a.fact with
            | .element r' _ _ => if r' == r then some a else none
            | _ => none
          else none
        | _ => none
      if !elems.isEmpty then
        let lens := (s.about r).filterMap fun b => match b with
          | .index a => if a.cond.isNone then match a.fact with
              | .length r' _ => if r' == r then some a else none
              | _ => none
            else none
          | _ => none
        let masks := (s.about r).filterMap fun b => match b with
          | .index a => if a.cond.isNone then match a.fact with
              | .linear _ => some a
              | _ => none
            else none
          | _ => none
        if mentionsElemProj r lens masks x.fact then
          let arrReads := elems.flatMap fun a => match a.fact with
            | .element _ arr _ => (s.about arr).filterMap fun b => match b with
                | .link g => if !g.alias && g.value == arr then some g else none
                | _ => none
            | _ => []
          let dropped : Nat → Bool := fun w =>
            w == r ||
            lens.any (fun a => match a.fact with | .length _ n => n == w | _ => false) ||
            masks.any (fun a => match HeapKnowledge.matchMaskLe r a.fact with | some (ms, _) => ms == w | none => false) ||
            arrReads.any (·.value == w)
          for y in HeapKnowledge.restateAtIndex arrReads dropped (elems ++ lens ++ masks ++ [x]) do
            s := s.add (.index y)
    let atEqs := (s.about v).filterMap fun b => match b with
      | .index a => if a.cond.isNone then match a.fact with
          | .atIndex _ _ _ none _ => some a
          | _ => none
        else none
      | _ => none
    if !atEqs.isEmpty then
      for y in HeapKnowledge.restateAtIndex [] (· == v) (x :: atEqs) do
        s := s.add (.index y)
    return s
  | .element r arr _ =>
    if r != v then return s
    let arrReads := (s.about arr).filterMap fun b => match b with
      | .link g => if !g.alias && g.value == arr then some g else none
      | _ => none
    if arrReads.isEmpty then return s
    let ints := (s.about r).filterMap fun b => match b with
      | .index a => if a.cond.isNone then match a.fact with
          | .int r' => if r' == r then some a else none
          | _ => none
        else none
      | _ => none
    if ints.isEmpty then return s
    let mut s := s
    for y in HeapKnowledge.restateAtIndex arrReads (fun w => arrReads.any (·.value == w)) (x :: ints) do
      s := s.add (.index y)
    return s
  | _ => return s

/-- A step's delta applied: the facts of `pairs` (store fact, image) whose
image `out` lost removed, `out`'s facts not already images added, renamed
by `back`. `shift`: `out` is over the pushed slots. -/
def applyDelta (s : Store) (pairs : List (Atom × Atom)) (out : Knowledge) (shift : Bool)
    (back : Nat → Option Nat) : Store := timedKind "delta" fun _ => Id.run do
  let outs := atomsOf out
  let outSet : Std.HashSet Atom := outs.foldl (·.insert ·) {}
  let image := fun (a : Atom) => if shift then (a.rename fun i => some (i + 1)).getD a else a
  let inSet : Std.HashSet Atom := pairs.foldl (fun acc (_, b) => acc.insert (image b)) {}
  let mut s := s
  for (a, b) in pairs do
    if !outSet.contains (image b) then s := s.remove a
  let mut added : List IndexAtom := []
  for o in outs do
    if !inSet.contains o then
      if let some a := o.rename back then
        -- A link of a name to itself states nothing.
        let trivial := match a with | .link g => g.alias && g.cell == g.value | _ => false
        if !trivial then s := s.add a
        if let .index x := a then added := x :: added
  -- A linear fact over a name a read gives, also stated over the read's
  -- path (`restateAddedReads`), and a linear or singly guarded linear fact
  -- over an element read's projection, also stated as `atIndex`
  -- (`restateAddedAtIndex`): the forms a later step keeps where it drops
  -- the read's name.
  for x in added do
    for v in x.fact.slots do
      s := restateAddedAtIndex (restateAddedReads s x v) x v
  return s

instance : Inhabited Node := ⟨⟨.nul, .ret, none⟩⟩

/-- `a == b`, answered at once where they are one object (`sameObjectOr`,
justified by the equality's reflexivity). -/
def same {α : Type} [BEq α] [ReflBEq α] (a b : α) : Bool :=
  sameObjectOr a b (fun _ => a == b) (fun h => by subst h; exact BEq.rfl)

/-- A list read at indices that mostly increase: the suffix at `pos`. -/
structure Cursor (α : Type) where
  all : List α
  rest : List α
  pos : Nat

def Cursor.of (l : List α) : Cursor α := ⟨l, l, 0⟩

/-- The element at `i`, and the cursor moved there. -/
def Cursor.get (c : Cursor α) (i : Nat) : Option α × Cursor α :=
  if i ≥ c.pos then
    let rest := c.rest.drop (i - c.pos)
    (rest.head?, { c with rest, pos := i })
  else
    let rest := c.all.drop i
    (rest.head?, { c with rest, pos := i })

/-- Where a mapping's last run starts: the longest suffix of `slots` that
reads a source of `n` slots in order to its end begins at the result. -/
def orderedSuffix (slots : List Nat) (n : Nat) : Nat :=
  let arr := slots.toArray
  -- From `k`, down while the slot before it reads the source in order to
  -- its end: structural on `k`.
  let rec down : Nat → Nat
    | 0 => 0
    | k + 1 => if arr[k]! + (arr.size - (k + 1)) + 1 == n then down k else k + 1
  down arr.size

/-- The names of a target's slots: the mapping applied to the source's. -/
def mapNames (names : List Nat) (m : PointClaims.Mapping) : List Nat :=
  match m with
  | none => names
  | some slots =>
    -- The longest suffix of `slots` reading the source's slots in order to
    -- its end: those target slots share the source's names.
    let arr := slots.toArray
    let k := orderedSuffix slots names.length
    let tail := if k < arr.size then names.drop arr[k]! else []
    let (_, out) := (slots.take k).foldl (fun ((cur : Cursor Nat), (out : Array Nat)) s =>
      let (x, c) := cur.get s
      (c, out.push (x.getD 0))) (Cursor.of names, Array.mkEmpty k)
    out.toList ++ tail

/-- The source names an edge's mapping leaves out of its target's slots:
the names of the source slots it skips that no target slot holds. -/
def droppedBy (names : List Nat) (m : PointClaims.Mapping) (target : List Nat) : List Nat := Id.run do
  match m with
  | none => return []
  | some slots =>
    -- Source slots read in increasing order skip the gaps; a slot read
    -- before the previous one leaves the gaps as they are.
    let mut skipped : List Nat := []
    let mut next := 0
    let mut rest := names
    for s in slots do
      if s ≥ next then
        for x in rest.take (s - next) do skipped := x :: skipped
        rest := rest.drop (s - next + 1)
        next := s + 1
    for x in rest do skipped := x :: skipped
    if skipped.isEmpty then return []
    return (skipped.filter (!target.contains ·)).eraseDups

/-- The store without the names `D`, which no slot holds any longer: their
facts restated through read links and eliminated from the linear facts
(as an edge's projection does, `HeapKnowledge.project`), the facts naming
them removed. -/
def Store.drop (s : Store) (D : List Nat) : Store := timedKind "drop" fun _ => Id.run do
  if D.isEmpty then return s
  let dset : Std.HashSet Nat := D.foldl (·.insert ·) {}
  let atoms := (keepFirst {} (D.flatMap s.about)).2.toList
  if atoms.isEmpty then return s
  -- The facts an elimination of `D` may combine: those naming `D`, and the
  -- linear facts over the names they name.
  let others := (keepFirst {} ((atoms.flatMap Atom.names).filter (!dset.contains ·))).2.toList
  let near := (keepFirst {} (others.flatMap s.about)).2.toList.filter fun a => match a with
    | .index x => match x.fact with | .linear _ => true | _ => false
    | .link _ => true
    | _ => false
  let indices := (atoms ++ near).filterMap fun a => match a with | .index x => some x | _ => none
  let links := (atoms ++ near).filterMap fun a => match a with | .link g => some g | _ => none
  let isOut := fun n => dset.contains n
  let restated := indices ++ HeapKnowledge.restateReads links isOut indices ++
    HeapKnowledge.restateSpines links isOut indices
  let derived := (HeapKnowledge.eliminateIndices D restated).drop indices.length
  let mut s := atoms.foldl Store.remove s
  -- A separation fact keeps its subject's separation from the partners the
  -- edge keeps (as `HeapSeparation.project` keeps the mapped levels).
  for a in atoms do
    if let .sep f := a then
      if !dset.contains f.slot then
        let partners := f.partners.filter fun (p, _) => !dset.contains p
        if !partners.isEmpty then s := s.add (.sep { f with partners })
  -- A name the edge drops that an alias link relates to a kept name: its
  -- facts restated of that name (as `HeapKnowledge.dropIndices` restates a
  -- dropped slot's facts on a neighbour).
  let keptAlias : Std.HashMap Nat Nat := links.foldl (fun acc g =>
    if !g.alias then acc
    else if dset.contains g.cell && !dset.contains g.value && !acc.contains g.cell then acc.insert g.cell g.value
    else if dset.contains g.value && !dset.contains g.cell && !acc.contains g.value then acc.insert g.value g.cell
    else acc) {}
  if !keptAlias.isEmpty then
    for a in atoms do
      if let some b := a.rename (fun x => some (keptAlias.getD x x)) then
        if b.names.all (!dset.contains ·) then s := s.add b
  for x in derived do
    let a := Atom.index x
    if a.names.all (!dset.contains ·) then s := s.add a
  return s

/-- The index facts of `k` connected to the slots `seeds` through shared
slots (alias and read links included), transitively: a linear entailment
over the seeds' terms, their paths' reads included, reads only these. -/
def component (k : Knowledge) (seeds : List Nat) : Knowledge := Id.run do
  if k.indices.isEmpty then return k
  let mut seen : Std.HashSet Nat := {}
  let mut frontier := seeds
  for x in seeds do seen := seen.insert x
  let mut kept : Array Bool := Array.replicate k.indices.length false
  let arr := k.indices.toArray
  let slotsOf := arr.map fun a => a.fact.slots ++ a.cond.toList
  while !frontier.isEmpty do
    let mut next := []
    for x in frontier do
      -- Through alias links, and read links: a precondition over a path
      -- reads the facts of the value read along it.
      for g in k.links do
        if g.cell == x || g.value == x then
          for y in [g.cell, g.value] do
            if !seen.contains y then
              seen := seen.insert y
              next := y :: next
    for i in List.range arr.size do
      if !kept[i]! && slotsOf[i]!.any seen.contains then
        kept := kept.set! i true
        for y in slotsOf[i]! do
          if !seen.contains y then
            seen := seen.insert y
            next := y :: next
    frontier := next
  return { k with indices := (arr.toList.zip kept.toList).filterMap fun (a, b) => if b then some a else none }

/-- `PromiseCalls.preconditionHolds` over the index facts connected to the
call's slots. -/
def admitsNear (k : Knowledge) (eff : CallEffects.Effect) (t : Tm) : Bool := timedKind s!"admits pre {eff.pre.length} req {eff.requires.isSome}" fun _ =>
  if eff.pre.isEmpty then PromiseCalls.preconditionHolds k eff t else
  match PromiseCalls.callSlots t with
  | some (_, slots) => PromiseCalls.preconditionHolds (component k slots) eff t
  | none => PromiseCalls.preconditionHolds k eff t

/-- The atoms of an index fact: of `bound(x, k, st)` (`IndexFact.HoldsAt`:
`k` an array index, so below `maxArrayLength`, and
`k + (st ? 1 : 0) ≤ |x|`), the linear facts `0 ≤ k`,
`k + (st ? 1 : 0) ≤ |x|` and, where `st` is false, `k ≤ maxArrayLength - 1`
(which `|x| ≤ maxArrayLength` gives where it is true); together they give
the fact but where `k` is a negative zero, a safe integer and no index. Any
other fact is its own atom. -/
def factAtoms : HeapKnowledge.IndexFact → List HeapKnowledge.IndexFact
  | .bound x k st =>
    let value := HeapKnowledge.Term.value k
    [.linear (.le [(value, -1)] 0),
     .linear (.le [(value, 1), (HeapKnowledge.Term.length x, -1)] (if st then -1 else 0))] ++
    (if st then [] else [.linear (.le [(value, 1)] ((maxArrayLength : Int) - 1))])
  | F => [F]

/-- A signature's precondition at the call `t` over the facts `k`: its
elements precondition and each atom of its index facts (`factAtoms`; a fact
whose atoms all hold and which does not, the fact itself), each decided
alone by `admitsNear`, the check acceptance applies to the whole;
an atom at the call's slots where every position it names is one the call
holds (`PromiseCalls.callSlots`). None where it states none. -/
def statedAt (k : Knowledge) (eff : CallEffects.Effect) (t : Tm) : Option StatedPrecondition :=
  if eff.requires.isNone && eff.pre.isEmpty then none else
  let requires := eff.requires.bind fun R =>
    (PromiseCalls.receiverSlot t).map fun x => (x, R, admitsNear k { eff with pre := [] } t)
  let atSlots := fun (N : HeapKnowledge.IndexFact) => (PromiseCalls.callSlots t).bind fun (recv, slots) =>
    if N.slots.all (fun p => p < slots.length && (p != 0 || recv)) then N.mapM fun p => slots[p]? else none
  let holds := fun (N : HeapKnowledge.IndexFact) => admitsNear k { eff with requires := none, pre := [N] } t
  -- (a fact whose atoms all hold and which does not: the fact itself)
  let atoms := eff.pre.flatMap fun F =>
    let N := F.toNow
    let parts := (factAtoms N).map fun A => (atSlots A, holds A)
    if parts.length > 1 && parts.all (·.2) && !holds N then parts ++ [(atSlots N, false)] else parts
  some { requires, atoms }

section
variable {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]

instance : Inhabited (PointClaim ι) := ⟨⟨[], []⟩⟩

/-- The target slots whose type differs from the type of the edge context's
slot the mapping reads, with that slot. -/
def differing (Γ Δ : List (Ty ι)) (m : PointClaims.Mapping) : List (Nat × Nat) := Id.run do
  match m with
  | none =>
    let mut out := []
    let mut i := 0
    let mut as := Γ
    for B in Δ do
      match as with
      | A :: rest =>
        if !same A B then out := (i, i) :: out
        as := rest
      | [] => out := (i, i) :: out
      i := i + 1
    return out
  | some slots =>
    let src := Γ.toArray
    let mut out := []
    let mut i := 0
    let mut ss := slots
    for B in Δ do
      match ss with
      | s :: rest =>
        match src[s]? with
        | some A => if !same A B then out := (i, s) :: out
        | none => out := (i, s) :: out
        ss := rest
      | [] => out := (i, 0) :: out
      i := i + 1
    return out

/-- **An edge's evidence checked** as the certificate checker checks a
target's slots (`ControlFlow.checkTargetResult`, `checkBranchTargetResult`;
`checkMapped_sound`, `checkObserved_sound`): from a context `Γ` no
environment meets, or each target slot of `Δ` covered by the source slot the
mapping reads, under the observation where the edge observes the result (at
slot 0, with the read fields, optional fields and cells the search read). -/
def edgeEvidenceChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ Δ : List (Ty ι)) (t : Target)
    (observed : Option BranchRefinement.Observation) (fields optionals : List (Nat × PropKey))
    (cells : HeapFacts.Facts) (p : PointClaims.EdgeEvidence ι) : Bool :=
  ControlFlow.unsatisfiable G Γ || match observed with
  | some o => BranchRefinement.checkObservedUsing G images Γ Δ 0 o t.mapping p fields optionals cells
  | none => PointClaims.checkMappedUsing G images Γ Δ t.mapping p

/-- The edge search (`edgeUsing`) from `Γ` over the facts `k`, its evidence
kept only where `edgeEvidenceChecked` accepts it. -/
def checkedEdge (G : NormalGraph ι) (images : InstanceImageCheck G) (claimed : Array (PointClaim ι))
    (Δ Γ : List (Ty ι)) (t : Target) (observed : Option BranchRefinement.Observation) (k : Knowledge)
    (answers : Answered G) : Bool × Answered G :=
  let fields := readFields k 0
  let optionals := optionalFields k 0
  let cells := match observed with
    | some o => HeapKnowledge.aliasCells (HeapKnowledge.observeTyped G Γ k 0 o)
    | none => []
  let (r, a) := edgeUsing G images claimed Γ t (observed.map (0, ·)) fields optionals cells answers
  (r.value.any (edgeEvidenceChecked G images Γ Δ t observed fields optionals cells), a)

/-- **A step's yields checked** as the certificate checker checks a node's
(`ControlFlow.checkYields`), at the node's context `Γ`, its claim's type
`A`, its implications at slots `xs`, its step's input facts `k` and output
`out` and its derivation `e`: of a call at a promise signature whose
derivation `promiseChecked` accepts (`promiseDerivChecked`), the yields
where the promise states them (`PromiseCalls.promiseYields`) at an output
the promise keeps; otherwise each yield `PromiseCalls.yieldFollows` accepts
of the node's term `t`. -/
def checkedYields (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι)) (A : Ty ι)
    (xs : List (PromiseCalls.Implication ι)) (k out : Knowledge) (e : ProgramCertificates.Evidence ι) (t : Tm)
    (promiseChecked : Unit → Bool) (ys : List (PromiseCalls.Yield ι)) : List (PromiseCalls.Yield ι) :=
  if ys.isEmpty then [] else
  match PromiseCalls.promiseOf G e with
  | some (effect, a, T) =>
    if PromiseCalls.promiseYields G A effect a T ys && promiseChecked () &&
        [HeapExpressionRules.ordinaryOutput k, PromiseCalls.promiseOutput effect k].any fun o =>
          out == o || out == HeapExpressionRules.withStable G Γ k o then ys
    else []
  | none => ys.filter (PromiseCalls.yieldFollows G images Γ xs k.links t)

/-- A call's derivation read off its callee's signatures (the direct form
of `CertificateProducer.expressionWithUsing`'s `direct`): the callee a slot,
its type's signatures in the same order (those promising elements first;
those stating a precondition `admits` holds of, then those stating none),
the first whose receiver, actuals and result the slots' types meet, each
by identity or a subtype proof (`subtypeUsing`, answered once). Untrusted:
none where the call is not of this form. -/
def directCall (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ : List (Ty ι)) (t : Tm) (A : Ty ι)
    (admits : CallEffects.Effect → Tm → Bool) (undefTy : Option (Ty ι)) (answers : Answered G) :
    Option (ProgramCertificates.Evidence ι × Bool) × Answered G := Id.run do
  let .invoke (.var f) recv args := t | return timedKind "direct: callee" fun _ => (none, answers)
  let some F := Γ[f]? | return (none, answers)
  if Γ.any List.isEmpty then return timedKind "direct: empty" fun _ => (none, answers)
  let (L, r) ← match PositiveRules.expand G F with
    | [PositiveNormalization.Clause.arrs L _] => pure (L, ProgramCertificates.Rule.app)
    | [PositiveNormalization.Clause.callable _ _ L _ _] => pure (L, ProgramCertificates.Rule.callCallable)
    | cs => return timedKind s!"direct: clauses {cs.length}" fun _ => (none, answers)
  let some argSlots := args.mapM (fun (a : Tm) => match a with | Tm.var i => some i | _ => none) | return timedKind "direct: args" fun _ => (none, answers)
  let mut answers := answers
  -- A slot read at `D`: its leaf, coerced where its type is not `D`.
  let leaf := fun (i : Nat) (B : Ty ι) => ProgramCertificates.Evidence.node ⟨Γ, Tm.var i, B⟩ ProgramCertificates.Rule.var []
  let L : List (CallEffects.Arrow (Ty ι)) := L
  let ordered := L.filter (fun (p : CallEffects.Arrow (Ty ι)) => !p.effect.schema.normal.elementsWhenTrue.isEmpty) ++
    L.filter (fun (p : CallEffects.Arrow (Ty ι)) => p.effect.schema.normal.elementsWhenTrue.isEmpty)
  let stating := fun (p : CallEffects.Arrow (Ty ι)) => p.effect.requires.isSome || !p.effect.pre.isEmpty
  for phase in [true, false] do
    for p in ordered do
      if phase != stating p then continue
      if phase && !admits p.effect t then continue
      if args.length != p.arguments.length then
        let _ := timedKind s!"direct: arity {args.length} vs {p.arguments.length}" fun _ => ()
        continue
      -- Each operand at its parameter.
      let mut parts : Array (ProgramCertificates.Evidence ι) := #[]
      let mut ok := true
      let operands := (recv, p.receiver) :: (args.zip p.arguments)
      for (a, D) in operands do
        match a with
        | .var i =>
          let some B := Γ[i]? | ok := false; break
          if same B D then parts := parts.push (leaf i B)
          else
            let (res, a') := subtypeUsing G images B D answers
            answers := a'
            match res.value with
            | some pr => parts := parts.push (coerceBy pr (leaf i B) D)
            | none =>
              ok := timedKind s!"direct: operand subtype" fun _ => false
              break
        | .undef =>
          -- `undefined` at its own type, coerced to `D`, as the search finds it.
          let e := ProgramCertificates.Evidence.node ⟨Γ, Tm.undef, D⟩ ProgramCertificates.Rule.undef []
          if (ProgramCertificates.checkTreeUsing G images e (fun _ => false) []) then parts := parts.push e
          else
            let U := undefTy.getD []
            let (res, a') := subtypeUsing G images U D answers
            answers := a'
            match res.value with
            | some pr => parts := parts.push (coerceBy pr (ProgramCertificates.Evidence.node ⟨Γ, Tm.undef, U⟩ ProgramCertificates.Rule.undef []) D)
            | none =>
              ok := timedKind s!"direct: undefined operand" fun _ => false
              break
        | _ =>
          ok := timedKind s!"direct: operand term" fun _ => false
          break
      if !ok then continue
      let _ := argSlots
      let ef := leaf f F
      let (res, a') := if same p.result A then (CheckResult.ofBool true |>.map fun _ => ({} : PositiveCertificates.SubtypeChoices ι), answers)
        else subtypeUsing G images p.result A answers
      answers := a'
      let some sub := res.value | continue
      return (some (coerceBy sub (.node ⟨Γ, t, p.result⟩ (r p.effect) (ef :: parts.toList)) A, phase), answers)
  return timedKind s!"direct: no signature of {L.length}" fun _ => (none, answers)

/-- Whether slot `f` in `Γ` is a callable declaring a signature with a fresh
array result (`ExitSchema.freshResult`). -/
def freshCallee (G : NormalGraph ι) (Γ : List (Ty ι)) (f : Nat) : Bool :=
  match Γ[f]? with
  | some F => match PositiveRules.expand G F with
    | [PositiveNormalization.Clause.arrs L _] | [PositiveNormalization.Clause.callable _ _ L _ _] =>
        L.any fun p => p.effect.schema.normal.freshResult
    | _ => false
  | none => false

/-- Whether a step reads every fact in the store: constructions (whose view
lengths may follow from facts their operands do not reach), calls to a
fresh-array-returning callee (`PromiseCalls.freshCallSpineApart`), and array
object allocations (whose fresh spine is separated from existing field paths
named in the store's index facts, `IndexWrites.freshSpineApart`). -/
def wholeStepOf (G : NormalGraph ι) (Γ : List (Ty ι)) : Tm → Bool
  | .construct .. => true
  | .invoke (.var f) _ _ => freshCallee G Γ f
  | .makeAt .absent [s, p] [.var 0, .var _] => s == arraySpineKey && p == CallArguments.protoField
  | .letE (.arrLit _) (.makeAt .absent [s, p] [.var 0, .var _]) =>
      s == arraySpineKey && p == CallArguments.protoField
  | _ => false

/-- **A refused step's preconditions** at node `l`'s step from the state
`entry` (its claim `c`, the slots `ms` its expression reads), over the
facts the step reads (`materialize` and `expandLinks`, as `checkedStep`
reads them): of a write of an element at a run-time index
(`IndexWrites.boundedSlots`), the bound its rule requires
(`IndexWrites.boundedWriteCheck`), decided by `IndexWrites.bounded`; of a
call or a construction of a slot, each distinct precondition its callee's
signatures state (`statedAt`); with the facts connected to the step's
slots. None for another term or a callee stating none. Read only where the
refusal is printed. -/
def stepPreconditionsAt (G : NormalGraph ι) (c : PointClaim ι) (node : Node) (entry : State) (ms : List Nat) :
    Option StepPreconditions := do
  let t := node.expression
  let whole := wholeStepOf G c.context t
  let facts := fun (_ : Unit) =>
    let (k, _, _) := materialize entry c.context.length ms whole
    KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G c.context) k
  if let some (a, i, v) := IndexWrites.boundedSlots t then
    let kE := facts ()
    return { step := .write, known := component kE [a, i, v],
             signatures := [{ atoms := [(some (.bound a i false), IndexWrites.bounded kE a i false)] }] }
  let (f, step) ← match t with
    | .invoke (.var f) _ _ => some (f, StepForm.call)
    | .construct (.var f) _ => some (f, StepForm.construction)
    | _ => none
  let F ← c.context[f]?
  let L : List (CallEffects.Arrow (Ty ι)) ← match PositiveRules.expand G F with
    | [PositiveNormalization.Clause.arrs L _] | [PositiveNormalization.Clause.callable _ _ L _ _] => some L
    | _ => none
  let effects := L.foldl (fun (acc : List CallEffects.Effect) p =>
    if acc.any fun e => e.requires == p.effect.requires && e.pre == p.effect.pre then acc else acc ++ [p.effect]) []
  if effects.all fun e => e.requires.isNone && e.pre.isEmpty then none
  let kE := facts ()
  let signatures := effects.filterMap fun e => statedAt kE e t
  let slots := ((PromiseCalls.callSlots t).map (·.2)).getD []
  pure { step, signatures, known := component kE slots }

/-- The facts one store holds and the other does not, each way. -/
def Store.diff (s t : Store) : List Atom × List Atom :=
  (s.toList.filter fun a => !t.live.contains a, t.toList.filter fun a => !s.live.contains a)

/-- The near-facts search's state: the names seen, the next frontier, the
facts kept and the facts listed. -/
structure NearState where
  seen : Std.HashSet Nat
  next : List Nat
  kept : Std.HashSet Atom
  out : Array IndexAtom

/-- Whether an index fact contributes to linear entailment (`HeapKnowledge.knownOf`,
`HeapKnowledge.termDefined`): linear inequalities, safe-integer atoms, and
length atoms. Non-linear atoms (disjunctions, guarded facts, quantified facts,
separations) are ignored by linear entailment and must not consume the
`linearNear` budget. -/
def isLinearRelevant : HeapKnowledge.IndexFact → Bool
  | .linear _ | .int _ | .length _ _ => true
  | _ => false

/-- One fact read at a frontier name: kept where it is an unconditional
linear-relevant index fact not kept yet and fewer than `limit` are listed; its
names put on the next frontier, where it is linear, if not seen yet. -/
def nearStep (limit : Nat) (st : NearState) (a : Atom) : NearState :=
  match a with
  | .index i =>
    if i.cond.isNone && isLinearRelevant i.fact && !st.kept.contains a && st.out.size < limit then
      let st := { st with kept := st.kept.insert a, out := st.out.push i }
      match i.fact with
      | .linear _ => a.names.foldl (fun (st : NearState) y =>
          if !st.seen.contains y then { st with seen := st.seen.insert y, next := y :: st.next } else st) st
      | _ => st
    else st
  | _ => st

/-- One round over the frontier `frontier`, from an empty next frontier. -/
def nearRound (s : Store) (limit : Nat) (frontier : List Nat) (st : NearState) : NearState :=
  frontier.foldl (fun st x => (s.about x).foldl (nearStep limit) st) { st with next := [] }

/-- The search on fuel: rounds while the frontier is non-empty and fewer than
`limit` facts are listed. -/
def nearLoop (s : Store) (limit : Nat) : Nat → List Nat → NearState → NearState
  | 0, _, st => st
  | n + 1, frontier, st =>
    if !frontier.isEmpty && st.out.size < limit then
      let st' := nearRound s limit frontier st
      nearLoop s limit n st'.next st'
    else st

/-- The facts the search lists from `names`, at most `limit`, in `fuel`
rounds: a round that leaves the frontier non-empty keeps a fact not kept
before, so the store's size and one rounds reach the search's end. -/
def linearNearFuel (s : Store) (names : List Nat) (limit : Nat := 40) (fuel : Nat := s.size + 1) :
    List IndexAtom :=
  (nearLoop s limit fuel names { seen := Std.HashSet.ofList names, next := [], kept := {}, out := #[] }).out.toList

/-- The unconditional index facts connected to the names through linear
facts, at most `limit`: what a linear entailment over those names reads. -/
def Store.linearNear (s : Store) (names : List Nat) (limit : Nat := 40) : List IndexAtom :=
  linearNearFuel s names limit

/-- Whether a store holds a fact: as it is, or a linear bound as a bound
of the same form at least as strong. -/
def Store.holds (s : Store) (a : Atom) : Bool :=
  let a := a.canon
  s.live.contains a || match a.linearKey with
    | some (key, d) => (s.about (a.names.headD 0)).any fun b => match b.linearKey with
      | some (key', d') => key' == key && d' ≤ d
      | none => false
    | none => false

/-- What an observing run keeps of the walk, to say where a fact was lost:
each node's state on entry and after its step, a merge's predecessors
(each's state renamed to the merge's names, and the renaming), a node's one
predecessor; and at a refusal its node, its edge's target, the facts it
lacks over names, and the names at the node's slots after its step. -/
structure Trace where
  entries : Array (Option State) := #[]
  afters : Array (Option State) := #[]
  merges : Array (List (Nat × State × Std.HashMap Nat (List Nat))) := #[]
  single : Array (Option Nat) := #[]
  heads : Array Bool := #[]
  start : Nat := 0
  node : Nat := 0
  edge : Option Nat := none
  missing : List Atom := []
  names : List Nat := []
  focus : List Nat := []

/-- Implications over names, at the slots holding them: one per pair of
slots holding the test's and the target's names. -/
def slotImplOf (names : List Nat) (xs : List (PromiseCalls.Implication ι)) : List (PromiseCalls.Implication ι) :=
  if xs.isEmpty then [] else
  -- The slots of the names the implications mention, in one scan.
  let wanted : Std.HashSet Nat := xs.foldl (fun acc x => (acc.insert x.test).insert x.target) {}
  let slotsOf : Std.HashMap Nat (List Nat) := names.zipIdx.foldl (fun acc (x, i) =>
    if wanted.contains x then acc.insert x (i :: acc.getD x []) else acc) {}
  xs.flatMap fun x => (slotsOf.getD x.test []).flatMap fun i => (slotsOf.getD x.target []).map fun j =>
    (⟨i, j, x.type⟩ : PromiseCalls.Implication ι)

/-- A label's regional facts (`GraphCode.ArgumentRegionGraph.checkNode`'s
tables at it): the slots holding entry argument paths, the fresh values and
cells, the fresh fields. -/
structure RegionState where
  facts : List GraphCode.ArgumentPathTracking.Fact := []
  values : List Nat := []
  cells : List Nat := []
  fields : List (Nat × String) := []
  deriving Inhabited

/-- A regional check (`regionalChecked`) made in the walk: the bound, the
spine regions, whether it bounds a throw, the field names fresh fields
range over, and each loop head's given regional facts. -/
structure Regional where
  Φ : Footprints.Closed
  regions : List Footprints.ArgumentSpineRegion
  exc : Bool
  names : List String := []
  heads : Array (Option RegionState) := #[]

/-- The regional facts every predecessor's edge establishes. -/
def RegionState.meet : List RegionState → RegionState
  | [] => {}
  | r :: rs => ⟨r.facts.filter fun x => rs.all (·.facts.contains x),
      r.values.filter fun x => rs.all (·.values.contains x),
      r.cells.filter fun x => rs.all (·.cells.contains x),
      r.fields.filter fun x => rs.all (·.fields.contains x)⟩

/-- A function updated at one point. -/
def upd {α : Type} (f : Nat → α) (a : Nat) (b : α) : Nat → α := fun x => if x = a then b else f x

/-- The depth-first walk's state: the marked heads, each node's state (0
new, 1 on the stack, 2 done), the frames (a node and its successors not yet
examined), the top first. -/
structure Dfs where
  heads : Nat → Bool
  state : Nat → Nat
  stack : List (Nat × List Nat)

/-- **One round of the depth-first walk**, over the successors `succ` and the
bound `n`: a frame with no successor left is done; otherwise its next
successor `w` below `n` is pushed where new, marked a head where on the
stack, passed where done; none where the stack is empty. -/
def dfsStep (succ : Nat → List Nat) (n : Nat) (σ : Dfs) : Option Dfs :=
  match σ.stack with
  | [] => none
  | (v, []) :: rest => some ⟨σ.heads, upd σ.state v 2, rest⟩
  | (v, w :: ws) :: rest =>
    if w < n then
      if σ.state w = 0 then some ⟨σ.heads, upd σ.state w 1, (w, succ w) :: (v, ws) :: rest⟩
      else if σ.state w = 1 then some ⟨upd σ.heads w true, σ.state, (v, ws) :: rest⟩
      else some ⟨σ.heads, σ.state, (v, ws) :: rest⟩
    else some ⟨σ.heads, σ.state, (v, ws) :: rest⟩

/-- The rounds on fuel, until the stack is empty. -/
def dfsLoop (succ : Nat → List Nat) (n : Nat) : Nat → Dfs → Dfs
  | 0, σ => σ
  | k + 1, σ => match dfsStep succ n σ with
    | none => σ
    | some σ' => dfsLoop succ n k σ'

/-- The walk's start: the start on the stack with all its successors to
examine, where it is below the bound. -/
def dfsInit (succ : Nat → List Nat) (n start : Nat) : Dfs :=
  if start < n then ⟨fun _ => false, upd (fun _ => 0) start 1, [(start, succ start)]⟩
  else ⟨fun _ => false, fun _ => 0, []⟩

/-- A graph's successors: the continuation's targets and the handler. -/
def nodeSucc (nodes : Array ControlFlow.Node) (w : Nat) : List Nat :=
  (successors nodes[w]!.continuation ++ nodes[w]!.handler.toList).map (·.label)

/-- The walk's fuel: each round pops a frame (each node is pushed at most
once) or examines one successor of a pushed node, and one more round finds
the stack empty. -/
def dfsFuel (nodes : Array ControlFlow.Node) : Nat :=
  2 * nodes.size + nodes.foldl (fun acc node => acc + (successors node.continuation).length + node.handler.toList.length) 0 + 1

/-- A walk's marks and states as arrays of `n` labels: the heads, and the
nodes it reached. -/
def Dfs.marks (σ : Dfs) (n : Nat) : Array Bool × Array Bool :=
  (Array.ofFn (n := n) fun i => σ.heads i, Array.ofFn (n := n) fun i => σ.state i != 0)

/-- The depth-first walk from the start, on `dfsFuel` (`dfsLoop`). -/
def loopHeadsWalk (nodes : Array ControlFlow.Node) (start : Nat) : Dfs :=
  dfsLoop (nodeSucc nodes) nodes.size (dfsFuel nodes) (dfsInit (nodeSucc nodes) nodes.size start)

/-- The loop heads of a graph: each target of a retreating edge of a
depth-first walk from the start (handlers' edges included); and the nodes
the walk reaches (`loopHeadsWalk`'s marks and states, by label). -/
def loopHeads (nodes : Array ControlFlow.Node) (start : Nat) : Array Bool × Array Bool :=
  Dfs.marks (loopHeadsWalk nodes start) nodes.size

/-- The loop heads' walk as the setup reads it: whether it ended within its
fuel (its stack empty), and its marks (`loopHeads`). -/
def loopHeadsRun (nodes : Array ControlFlow.Node) (start : Nat) : Bool × Array Bool × Array Bool :=
  ((loopHeadsWalk nodes start).stack.isEmpty, loopHeads nodes start)

/-- The depth-first walk's state over arrays of the `n` labels (`Dfs`). -/
structure DfsA where
  heads : Array Bool
  state : Array Nat
  stack : List (Nat × List Nat)

/-- `dfsStep` over arrays. -/
def dfsStepA (succ : Nat → List Nat) (n : Nat) (σ : DfsA) : Option DfsA :=
  match σ.stack with
  | [] => none
  | (v, []) :: rest => some ⟨σ.heads, σ.state.set! v 2, rest⟩
  | (v, w :: ws) :: rest =>
    if w < n then
      if σ.state[w]! = 0 then some ⟨σ.heads, σ.state.set! w 1, (w, succ w) :: (v, ws) :: rest⟩
      else if σ.state[w]! = 1 then some ⟨σ.heads.set! w true, σ.state, (v, ws) :: rest⟩
      else some ⟨σ.heads, σ.state, (v, ws) :: rest⟩
    else some ⟨σ.heads, σ.state, (v, ws) :: rest⟩

/-- `dfsLoop` over arrays. -/
def dfsLoopA (succ : Nat → List Nat) (n : Nat) : Nat → DfsA → DfsA
  | 0, σ => σ
  | k + 1, σ => match dfsStepA succ n σ with
    | none => σ
    | some σ' => dfsLoopA succ n k σ'

/-- `dfsInit` over arrays. -/
def dfsInitA (succ : Nat → List Nat) (n start : Nat) : DfsA :=
  if start < n then ⟨Array.replicate n false, (Array.replicate n 0).set! start 1, [(start, succ start)]⟩
  else ⟨Array.replicate n false, Array.replicate n 0, []⟩

/-- An array walk agrees with a walk: the same stack, arrays of `n` labels
holding the walk's marks and states, every frame's node below `n`. -/
structure DfsA.Agrees (n : Nat) (a : DfsA) (σ : Dfs) : Prop where
  stack : a.stack = σ.stack
  hsize : a.heads.size = n
  ssize : a.state.size = n
  heads : ∀ t, t < n → a.heads[t]! = σ.heads t
  state : ∀ t, t < n → a.state[t]! = σ.state t
  below : ∀ p ∈ σ.stack, p.1 < n

theorem getElem!_set!_self {α : Type} [Inhabited α] (a : Array α) (i : Nat) (x : α) (h : i < a.size) :
    (a.set! i x)[i]! = x := by
  simp [Array.set!_eq_setIfInBounds, h]

theorem getElem!_set!_ne {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (x : α) (h : j ≠ i) :
    (a.set! i x)[j]! = a[j]! := by
  simp [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne (Ne.symm h)]

theorem agrees_upd {α : Type} [Inhabited α] (n : Nat) (a : Array α) (f : Nat → α) (i : Nat) (x : α)
    (hs : a.size = n) (hi : i < n) (h : ∀ t, t < n → a[t]! = f t) :
    ∀ t, t < n → (a.set! i x)[t]! = upd f i x t := by
  intro t ht
  unfold upd
  by_cases e : t = i
  · subst e; rw [getElem!_set!_self a t x (hs ▸ hi)]; simp
  · rw [getElem!_set!_ne a i t x e, h t ht]; simp [e]

theorem dfsStepA_agrees (succ : Nat → List Nat) (n : Nat) (a : DfsA) (σ : Dfs) (h : a.Agrees n σ) :
    match dfsStepA succ n a, dfsStep succ n σ with
    | none, none => True
    | some a', some σ' => a'.Agrees n σ'
    | _, _ => False := by
  obtain ⟨hst, hhs, hss, hh, hs, hb⟩ := h
  unfold dfsStepA dfsStep
  rw [hst]
  match hσ : σ.stack with
  | [] => simp
  | (v, []) :: rest =>
    have hv : v < n := hb (v, []) (by rw [hσ]; simp)
    refine ⟨rfl, hhs, by simp [hss], hh, agrees_upd n a.state σ.state v 2 hss hv hs, ?_⟩
    intro p hp; exact hb p (by rw [hσ]; exact List.mem_cons_of_mem _ hp)
  | (v, w :: ws) :: rest =>
    have hbs : ∀ p ∈ (v, ws) :: rest, p.1 < n := by
      intro p hp
      rcases List.mem_cons.mp hp with e | hp
      · rw [e]; exact hb (v, w :: ws) (by rw [hσ]; simp)
      · exact hb p (by rw [hσ]; exact List.mem_cons_of_mem _ hp)
    by_cases hw : w < n
    · simp only [hw, ite_true, hs w hw]
      by_cases h0 : σ.state w = 0
      · simp only [h0, ite_true]
        refine ⟨rfl, hhs, by simp [hss], hh, agrees_upd n a.state σ.state w 1 hss hw hs, ?_⟩
        intro p hp
        rcases List.mem_cons.mp hp with e | hp
        · subst e; exact hw
        · exact hbs p hp
      · simp only [h0, ite_false]
        by_cases h1 : σ.state w = 1
        · simp only [h1, ite_true]
          exact ⟨rfl, by simp [hhs], hss, agrees_upd n a.heads σ.heads w true hhs hw hh, hs, hbs⟩
        · simp only [h1, ite_false]
          exact ⟨rfl, hhs, hss, hh, hs, hbs⟩
    · simp only [hw, ite_false]
      exact ⟨rfl, hhs, hss, hh, hs, hbs⟩

theorem dfsLoopA_agrees (succ : Nat → List Nat) (n : Nat) :
    ∀ (k : Nat) (a : DfsA) (σ : Dfs), a.Agrees n σ → (dfsLoopA succ n k a).Agrees n (dfsLoop succ n k σ)
  | 0, _, _, h => h
  | k + 1, a, σ, h => by
    have hs := dfsStepA_agrees succ n a σ h
    unfold dfsLoopA dfsLoop
    split at hs <;> rename_i ha hσ
    · rw [ha, hσ]; exact h
    · rw [ha, hσ]; exact dfsLoopA_agrees succ n k _ _ hs
    · exact hs.elim

theorem dfsInitA_agrees (succ : Nat → List Nat) (n start : Nat) :
    (dfsInitA succ n start).Agrees n (dfsInit succ n start) := by
  unfold dfsInitA dfsInit
  by_cases h : start < n
  · simp only [h, ite_true]
    refine ⟨rfl, by simp, by simp, fun t ht => by simp [ht], ?_, fun p hp => by simp at hp; rw [hp]; exact h⟩
    intro t ht
    unfold upd
    by_cases e : t = start
    · subst e; simp [Array.set!_eq_setIfInBounds, ht]
    · rw [getElem!_set!_ne _ start t 1 e]; simp [e, ht]
  · simp only [h, ite_false]
    exact ⟨rfl, by simp, by simp, fun t ht => by simp [ht], fun t ht => by simp [ht], fun p hp => by simp at hp⟩

/-- `dfsStepA` returning the state it was given where the stack is empty,
with whether it took a round: the state is taken apart once, so its arrays
are updated in place. -/
def dfsStepB (succ : Nat → List Nat) (n : Nat) (σ : DfsA) : DfsA × Bool :=
  let ⟨heads, state, stack⟩ := σ
  match stack with
  | [] => (⟨heads, state, []⟩, false)
  | (v, []) :: rest => (⟨heads, state.set! v 2, rest⟩, true)
  | (v, w :: ws) :: rest =>
    if w < n then
      if state[w]! = 0 then (⟨heads, state.set! w 1, (w, succ w) :: (v, ws) :: rest⟩, true)
      else if state[w]! = 1 then (⟨heads.set! w true, state, (v, ws) :: rest⟩, true)
      else (⟨heads, state, (v, ws) :: rest⟩, true)
    else (⟨heads, state, (v, ws) :: rest⟩, true)

theorem dfsStepB_eq (succ : Nat → List Nat) (n : Nat) (σ : DfsA) :
    dfsStepB succ n σ = (match dfsStepA succ n σ with | none => (σ, false) | some σ' => (σ', true)) := by
  obtain ⟨heads, state, stack⟩ := σ
  unfold dfsStepB dfsStepA
  match stack with
  | [] => rfl
  | (v, []) :: rest => rfl
  | (v, w :: ws) :: rest =>
    by_cases hw : w < n
    · by_cases h0 : state[w]! = 0
      · simp [hw, h0]
      · by_cases h1 : state[w]! = 1
        · simp [hw, h1]
        · simp [hw, h0, h1]
    · simp [hw]

/-- `dfsLoopA` over `dfsStepB`: the state is not held across a round. -/
def dfsLoopB (succ : Nat → List Nat) (n : Nat) : Nat → DfsA → DfsA
  | 0, σ => σ
  | k + 1, σ => match dfsStepB succ n σ with
    | (σ', true) => dfsLoopB succ n k σ'
    | (σ', false) => σ'

theorem dfsLoopB_eq (succ : Nat → List Nat) (n : Nat) :
    ∀ (k : Nat) (σ : DfsA), dfsLoopB succ n k σ = dfsLoopA succ n k σ
  | 0, _ => rfl
  | k + 1, σ => by
    unfold dfsLoopB dfsLoopA
    rw [dfsStepB_eq]
    cases dfsStepA succ n σ with
    | none => rfl
    | some σ' => exact dfsLoopB_eq succ n k σ'

/-- `loopHeadsRun` over the array walk, which the compiled verifier runs
(`loopHeadsRun_eq_A`). -/
def loopHeadsRunA (nodes : Array ControlFlow.Node) (start : Nat) : Bool × Array Bool × Array Bool :=
  let a := dfsLoopB (nodeSucc nodes) nodes.size (dfsFuel nodes) (dfsInitA (nodeSucc nodes) nodes.size start)
  (a.stack.isEmpty, a.heads, a.state.map (· != 0))

/-- **The array walk computes the loop heads' walk**: the same stack, and
by label the same marks and reached nodes (`DfsA.Agrees`). -/
@[csimp] theorem loopHeadsRun_eq_A : @loopHeadsRun = @loopHeadsRunA := by
  funext nodes start
  have h := dfsLoopA_agrees (nodeSucc nodes) nodes.size (dfsFuel nodes) _ _
    (dfsInitA_agrees (nodeSucc nodes) nodes.size start)
  obtain ⟨hst, hhs, hss, hh, hs, -⟩ := h
  unfold loopHeadsRun loopHeadsRunA loopHeads Dfs.marks loopHeadsWalk
  simp only [dfsLoopB_eq, hst, Prod.mk.injEq, true_and]
  constructor
  · apply Array.ext
    · simp [hhs]
    · intro i h1 h2
      simp only [Array.size_ofFn] at h1
      rw [Array.getElem_ofFn, ← hh i h1, getElem!_pos _ _ (by omega)]
  · apply Array.ext
    · simp [hss]
    · intro i h1 h2
      simp only [Array.size_ofFn] at h1
      rw [Array.getElem_ofFn, Array.getElem_map, ← hs i h1, getElem!_pos _ _ (by omega)]

/-- A list of `n` labels' tables, empty but at the given labels. -/
def sparse {α : Type} (n : Nat) (empty : α) (at_ : List (Nat × α)) : List α :=
  at_.foldl (fun acc (l, x) => acc.set l x) (List.replicate n empty)

/-- The checker the pass runs: the proved layers (`Checker.ordinary`),
whose `select` takes a derivation as given, so the pass checks the step's
tree; or a qualified body's (`Checker.withSubtyping`), whose `select` is its
`run` (`select_eq_run`); or a caller-supplied checker (`extended`), whose
`select` is its `run`. The verifier never constructs `extended`: the
experimental prototype of `docs/drafts/paper-rules-mode.md` does, and no
soundness theorem covers a run with it (`CheckerScope` has no case for it). -/
inductive PassChecker (G : NormalGraph ι) (images : InstanceImageCheck G) where
  | ordinary
  | qualified (subtyping : BodySubtyping G)
      (ord : ∀ {A B p}, PositiveCertificates.checkUsing G images A B p = true → subtyping.check A B p = true)
  | extended (checker : HeapExpressionRules.Checker G images)

def PassChecker.checker {G : NormalGraph ι} {images : InstanceImageCheck G} :
    PassChecker G images → HeapExpressionRules.Checker G images
  | .ordinary => HeapExpressionRules.Checker.ordinary G images
  | .qualified s o => HeapExpressionRules.Checker.withSubtyping G images s o
  | .extended c => { c with select := c.run }

/-- Whether the checker's `select` checks the step itself. -/
def PassChecker.selectChecks {G : NormalGraph ι} {images : InstanceImageCheck G} : PassChecker G images → Bool
  | .ordinary => false
  | .qualified .. => true
  | .extended _ => true

/-- A node of a unit's graph as a supplied layer sees it: its expression,
the width of its claim's context, and the source span its source map gives
it, where it gives one. -/
abbrev LayerSite := Tm × Nat × Option (Nat × Nat)

/-- A scoped closure site inside a unit's graph, as a supplied layer sees it:
the enclosing unit's name and input count, the spans of the closure creation
and enclosing call, the call's term and context types, the caller's entry
knowledge right before the call, the caller slots holding each capture at the
call, the closure's argument index in the call, and the first capture slot in
the closure's entry frame. -/
structure ClosureSite (ι : Type) where
  unitName : String
  unitInputs : Nat
  closureSpan : Option (Nat × Nat)
  callSpan : Option (Nat × Nat)
  callTerm : Tm
  callContext : List (Ty ι)
  callKnowledge : Knowledge
  captureSlots : List (Option Nat)
  argIndex : Nat
  captureOffset : Nat

/-- A checker a caller supplies for a unit, by the unit's name, the number
of its graph's inputs and its nodes' sites, over the ordinary checker: what
`PassChecker.extended` runs; plus optional hooks for deriving scoped closure
entry facts from the enclosing call site. -/
structure PassLayer where
  checker : String → Nat → List LayerSite → ∀ {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι]
    (G : NormalGraph ι) (images : InstanceImageCheck G), HeapExpressionRules.Checker G images →
    HeapExpressionRules.Checker G images
  wantsClosure : String → Option (Nat × Nat) → Option (Nat × Nat) → Bool := fun _ _ _ => false
  closureFacts : ∀ {ι : Type} [DecidableEq ι] [Hashable ι] [Instantiates ι],
    NormalGraph ι → ClosureSite ι → List HeapKnowledge.IndexAtom := fun _ _ => []

/-- The pass checker of a unit: the ordinary one, or a supplied layer over it. -/
def PassChecker.ofLayer {G : NormalGraph ι} {images : InstanceImageCheck G} (layer : Option PassLayer) (name : String)
    (inputs : Nat) (sites : List LayerSite := []) : PassChecker G images :=
  match layer with
  | none => .ordinary
  | some L => .extended (L.checker name inputs sites G images (HeapExpressionRules.Checker.ordinary G images))

/-- **The start's written separation kept** in its given state
(`startWritten`, `HeapSeparation.union`): each of its facts has a partner,
and where it and the entry separation `entrySeparation` both state facts,
they are at one depth. -/
def startSeparationKept (written : Option Knowledge) (entrySeparation : HeapSeparation.Separation) : Bool :=
  let ws := (written.getD {}).separation
  ws.facts.all (!·.partners.isEmpty) &&
    (ws.facts.isEmpty || entrySeparation.facts.isEmpty || ws.depth == entrySeparation.depth)

/-- The unit's entry checked as `ControlFlow.checkEntryResult` checks a
certificate's (no edge enters the start on the first invocation): the start's
context is the request's inputs; the promised input's slot is one of them;
the start's given state states no implication, names a slot after the
promised input only at that input's own slot and after an input's entry value
only at that input's slot; its written separation states each fact with a
partner and, where it and the entry's separation both state facts, is at
the entry separation's depth, so the start's given state
(`startWritten`) keeps every fact of it; and its written and supplied facts
are entailed by the request's entry facts (`ControlFlow.entryKnows`). The
refusal where one fails. -/
def entryRefusal (G : NormalGraph ι) (inputs : List (Ty ι)) (claims : List (PointClaim ι)) (start : Nat)
    (goal : Goal ι) (written : Option Knowledge) (supplied : List HeapKnowledge.Candidate)
    (givenImplies : List (PromiseCalls.Implication ι)) (givenArgs : List Nat) (givenInputs : List (Nat × Nat))
    (entryIndices : List IndexAtom) (entrySeparation : HeapSeparation.Separation) : Option String :=
  match claims[start]? with
  | none => some "the entry: no claim at the start"
  | some c =>
    if !(c.context == inputs) then some "the entry: its context is not the inputs'"
    else if !goal.slot.all (· < inputs.length) then some "the entry: the promised input's slot"
    else if !givenImplies.isEmpty then some "the entry: a given implication"
    else if !givenArgs.all (some · == goal.slot) then some "the entry: a slot given the promised input"
    else if !givenInputs.all (fun (j, q) => j == q) then some "the entry: a slot given an input's value"
    else if !startSeparationKept written entrySeparation then some "the entry: its written separation"
    else
      let k := HeapKnowledge.withCandidates (written.getD {}) supplied
      if !ControlFlow.entryKnows G inputs entrySeparation entryIndices k then
        some "the entry: a given fact the entry facts do not entail"
      else none

/-- The start's written facts as `run` assumes them at its given state: its
written assertion with the request's entry index facts and the separation
of its inputs (`Request.entryIndices`, `entrySeparation`). -/
def startWritten (written : Option Knowledge) (entryIndices : List IndexAtom)
    (entrySeparation : HeapSeparation.Separation) : Knowledge :=
  let w := written.getD {}
  { w with indices := w.indices ++ entryIndices, separation := HeapSeparation.union w.separation entrySeparation }

/-- **The start's identities a post fact reads** (the note "Tolerant
frames", section 6, "Triples": at the start the current state is the entry
state, where `old(t)` and `t` denote the same wherever `t` is defined,
`IndexFact.identity_holds`), by structural recursion over every form of
fact. Each occurrence of an entry term `old(t)` gives each fact of its
identity (`IndexFact.identity`) as a list of statements, strongest first:
the fact itself, then the fact under each guard the occurrence is read
beneath, the innermost first, a guard on an input read at that input's slot
at the start (the post's slot `s + 1` is the start's `s`). With each, whether
every state the post fact holds in reads the occurrence: one in a
disjunction's arm is read where that arm holds, and one beneath a guard on
the result where the result fails it, neither a condition of the start's
state. -/
def startIdentities : HeapKnowledge.IndexFact → List (List HeapKnowledge.IndexFact × Bool)
  | F@(.linear _) | F@(.every _ _ _ _ _) | F@(.atIndex _ _ _ _ _) =>
    F.entryTerms.flatMap fun t => (HeapKnowledge.IndexFact.identity t).map fun I => ([I], true)
  | .either A B => (startIdentities A ++ startIdentities B).map fun (c, _) => (c, false)
  | .guarded 0 _ _ B => (startIdentities B).map fun (c, _) => (c, false)
  | .guarded (s + 1) p tag B =>
    (startIdentities B).map fun (c, r) => (c ++ (c.getLast?.map (.guarded s p tag ·)).toList, r)
  | .index _ | .length _ _ | .bound _ _ _ | .int _ | .pastSafe _ | .element _ _ _ | .fieldRead _ _ _ | .apart _ _ _ _
  | .spineApart _ _ _ _ | .elemSpineApart _ _ _ _ | .same _ _ => []

/-- The start's identity facts (`startIdentities`) for the postcondition
`ens`: of each statement list, the first the entry facts entail
(`ControlFlow.entryKnows`); where none is, the last of one every state of
the post reads, which the entry check then refuses, as a fact the post needs
and the entry does not establish. Each is a proposal the entry check reads
at the entry state (`entryRefusal`). -/
def startOldFacts (G : NormalGraph ι) (inputs : List (Ty ι)) (entryIndices : List IndexAtom)
    (entrySeparation : HeapSeparation.Separation) (ens : List HeapKnowledge.IndexFact) : List IndexAtom :=
  (ens.flatMap startIdentities).eraseDups.filterMap fun (cands, req) =>
    match cands.find? (fun I => ControlFlow.entryKnows G inputs entrySeparation entryIndices
        { indices := [{ fact := I }] }) with
    | some I => some { fact := I }
    | none => if req then cands.getLast?.map ({ fact := · }) else none

/-- The claims' facts with the start's identity facts (`startOldFacts`)
among the start's. -/
def withStartOld (G : NormalGraph ι) (inputs : List (Ty ι)) (entryIndices : List IndexAtom)
    (entrySeparation : HeapSeparation.Separation) (start : Nat) (ens : List HeapKnowledge.IndexFact)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) : List (Nat × List HeapKnowledge.Candidate) :=
  match startOldFacts G inputs entryIndices entrySeparation ens with
  | [] => candidates
  | extra => (start, ((candidates.find? (·.1 == start)).map (·.2)).getD [] ++ extra.map .index) :: candidates

/-- The start's given state as `run` builds it: `startWritten`, with the
claims' facts there (`supplied`). -/
def startGiven (written : Option Knowledge) (entryIndices : List IndexAtom)
    (entrySeparation : HeapSeparation.Separation) (supplied : List HeapKnowledge.Candidate) : Knowledge :=
  HeapKnowledge.withCandidates (startWritten written entryIndices entrySeparation) supplied

/-- **A step's derivation checked** where a footprint or a fresh result
reads it (`GraphCode.nodeChecked`'s conjuncts beside `selectedWithinAt`):
claimed at the node's term and context, its tree accepted
(`ProgramCertificates.checkTreeUsing`, or `PromiseCalls.requiresTree` at the
step's facts `stepK`). -/
def derivChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (stepK : Knowledge)
    (deriv : ProgramCertificates.Evidence ι) : Bool :=
  (ProgramCertificates.claim deriv).term == node.expression &&
    (ProgramCertificates.claim deriv).context == c.context &&
    (ProgramCertificates.checkTreeUsing G images deriv codes sums ||
      PromiseCalls.requiresTree G images stepK codes sums deriv)

/-- **A step's derivation checked where its call's signature bounds the
step** (`footprintCheck`, `stepGrades`, `stepCertificate`, `outFreshOf`):
`derivChecked`, its context the claim's refined by the step's facts' safe
integers (`PromiseCalls.intRefines`), as the step was checked at
(`checkedStep`). -/
def stepDerivChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (stepK : Knowledge)
    (deriv : ProgramCertificates.Evidence ι) : Bool :=
  (ProgramCertificates.claim deriv).term == node.expression &&
    PromiseCalls.intRefines G c.context (ProgramCertificates.claim deriv).context stepK.indices &&
    (ProgramCertificates.checkTreeUsing G images deriv codes sums ||
      PromiseCalls.requiresTree G images stepK codes sums deriv)

/-- **A promise call's derivation checked** where its yields are kept
(`checkedYields`): `stepDerivChecked`, and its claim's type the node's. -/
def promiseDerivChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (stepK : Knowledge)
    (deriv : ProgramCertificates.Evidence ι) : Bool :=
  stepDerivChecked G images codes sums c node stepK deriv && decide ((ProgramCertificates.claim deriv).type = c.type)

/-- **A node's shape** as the certificate checker checks a `branch`: its
claim type the Boolean (`expand G A = [.bool]`); a return, a bind or an
effect any. -/
def passShapeCheck (G : NormalGraph ι) (A : Ty ι) : Continuation → Bool
  | .branch _ _ => decide (PositiveRules.expand G A = [.bool])
  | .ret | .bind _ | .effect _ => true
  | _ => false

/-- **A node's shape at every continuation**: `passShapeCheck`, and at a
`branchBind` the checker's test (`ControlFlow.checkNodeResult`,
`BranchRefinement.onlyBoolean`); a `tagBind` needs none. -/
def passShapeCheck' (G : NormalGraph ι) (A : Ty ι) : Continuation → Bool
  | .branchBind _ _ => BranchRefinement.onlyBoolean G A
  | .tagBind _ _ _ => true
  | k => passShapeCheck G A k

/-- **The derivation a regional check reads** checked as `footprintCheck`
checks it (`stepDerivChecked`), where the step has one. -/
def regionalDerivChecked (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (stepK : Knowledge)
    (deriv : Option (ProgramCertificates.Evidence ι)) : Bool :=
  match deriv with
  | some d => stepDerivChecked G images codes sums c node stepK d
  | none => true

/-- **The step evidence's header** where the regional evidence is typed by
the step's proof (no derivation, a proof `p` in the step evidence): `p`'s
claim at the node's context and type. -/
def regionalHeaderChecked (c : PointClaim ι) (deriv : Option (ProgramCertificates.Evidence ι))
    (effect : Option (HeapExpressionRules.StepEvidence ι)) : Bool :=
  match deriv, effect.bind HeapExpressionRules.StepEvidence.proof? with
  | none, some p => decide ((ProgramCertificates.claim p).context = c.context ∧ (ProgramCertificates.claim p).type = c.type)
  | _, _ => true

/-- **A node's step within a footprint bound** (`GraphCode.nodeChecked`),
at a node outside the region from which no normal return is possible: the
step within `Φ` (`ExpressionEffects.check`, `writeWithin`, `initWriteWithin`,
the step's derivation `deriv` within it at the fresh receivers `F`
(`selectedWithinAt`), claimed at the node's term and context and its tree
accepted, an empty type); its throw within `Φ` where a live handler
catches it, and, where none does, within the exceptional bound `Ψ` with
`Φ` within `Ψ` (the escaping throw completes a run whose prefix is within
`Φ`), unless `Ψ` is `⊤`; a return under a fresh result (`ret`) returning a
fresh value (`outFresh`); the term in scope. -/
def footprintCheck (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (Φ Ψ : Footprints.Closed) (F : List Nat) (c : PointClaim ι) (node : Node)
    (stepK : Knowledge) (deriv : ProgramCertificates.Evidence ι) (liveHandler ret outFresh : Bool) : Bool :=
  -- The step's derivation, where its signature bounds the step: claimed
  -- at the node's term and context, its tree accepted (`GraphCode.nodeChecked`'s
  -- conjuncts beside `selectedWithinAt`).
  let derivChecked : Thunk Bool := Thunk.mk fun _ => SinglePass.stepDerivChecked G images codes sums c node stepK deriv
  let writes := fun (B : Footprints.Closed) => ExpressionEffects.writeWithin G c.context B node.expression ||
    ExpressionEffects.initWriteWithin G c.context stepK B node.expression ||
    ExpressionEffects.denseWriteWithin G c.context stepK B node.expression
  let within := ExpressionEffects.check G c.context node.expression || writes Φ ||
    (GraphCode.selectedWithinAt Φ F deriv && derivChecked.get) || ExpressionEffects.emptyType G c.type ||
    c.context.any (ExpressionEffects.emptyType G ·)
  -- A throw within a bound: a call's throw by its signature's exceptional
  -- exit (`GraphCode.selectedThrowsWithinAt`).
  let throwsAt := fun (B : Footprints.Closed) => ExpressionEffects.check G c.context node.expression || writes B ||
    (GraphCode.selectedThrowsWithinAt B F deriv && derivChecked.get) ||
    c.context.any (ExpressionEffects.emptyType G ·)
  -- A throw a live handler catches continues within the normal bound; one
  -- that escapes completes the run exceptionally, its prefix within the
  -- normal bound, so within the exceptional bound where that is not `⊤`
  -- (which every run meets), the normal bound inside it.
  let throws := (!liveHandler || throwsAt Φ) && (liveHandler || Ψ == .top || (Φ.le Ψ && throwsAt Ψ))
  let returns := match node.continuation with
    | .ret => !ret || outFresh
    | _ => true
  within && throws && returns && ProgramCertificates.checkScope c.context.length node.expression

/-- A step's local effect (`StepGrades`), at its claim `c`, node, facts
`stepK` and derivation `deriv`, its fresh receiver slots `F`; the
derivation checked once, where a call's grade needs it. -/
def stepGrades (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (F : List Nat) (c : PointClaim ι) (node : Node)
    (stepK : Knowledge) (deriv : ProgramCertificates.Evidence ι) : StepGrades :=
  let writes := ExpressionEffects.writeGrades G c.context node.expression ++
    ExpressionEffects.initWriteGrades G c.context stepK node.expression ++
    ExpressionEffects.denseWriteGrades G c.context stepK node.expression
  let selected := GraphCode.selectedGrades F deriv
  let inspection := ExpressionEffects.check G c.context node.expression
  let emptyContext := c.context.any (ExpressionEffects.emptyType G ·)
  let selectedT := GraphCode.selectedThrowGrades F deriv
  let checked : Thunk (List Footprints.Closed) := Thunk.mk fun _ =>
    if selected.isEmpty then [] else if stepDerivChecked G images codes sums c node stepK deriv then selected else []
  let checkedT : Thunk (List Footprints.Closed) := Thunk.mk fun _ =>
    if selectedT.isEmpty then [] else if stepDerivChecked G images codes sums c node stepK deriv then selectedT else []
  { within := if inspection || ExpressionEffects.emptyType G c.type || emptyContext then [⟨.keep, .keep, .keep⟩]
      else writes ++ checked.get
    throws := if inspection || emptyContext then [⟨.keep, .keep, .keep⟩]
      else writes ++ checkedT.get
    scope := ProgramCertificates.checkScope c.context.length node.expression }

/-- Whether a step's local effect `g` is within the bounds `Φ` (normal) and
`Ψ` (exceptional): a grade on normal return below `Φ`; where a live handler
catches its throw, a throw's grade below `Φ`; where none does and `Ψ` is not
`⊤`, `Φ` within `Ψ` and a throw's grade below `Ψ`; a return under a fresh
result (`ret`) returning a fresh value; the term in scope. -/
def StepGrades.admits (g : StepGrades) (Φ Ψ : Footprints.Closed) (liveHandler ret outFresh : Bool)
    (k : Continuation) : Bool :=
  g.within.any (·.le Φ) && ((!liveHandler || g.throws.any (·.le Φ)) &&
    (liveHandler || Ψ == .top || (Φ.le Ψ && g.throws.any (·.le Ψ)))) &&
    (match k with
      | .ret => !ret || outFresh
      | _ => true) && g.scope

omit [Hashable ι] [Instantiates ι] in
/-- **The footprint check is the step's local effect within the bounds**
(proved): every disjunct of `footprintCheck` reading a bound is a rule's
grade below it, so the check at any bounds is `admits` of the grades
`stepGrades` reads off the step once. -/
theorem footprintCheck_eq_admits (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (Φ Ψ : Footprints.Closed) (F : List Nat) (c : PointClaim ι) (node : Node)
    (stepK : Knowledge) (deriv : ProgramCertificates.Evidence ι) (liveHandler ret outFresh : Bool) :
    footprintCheck G images codes sums Φ Ψ F c node stepK deriv liveHandler ret outFresh =
      (stepGrades G images codes sums F c node stepK deriv).admits Φ Ψ liveHandler ret outFresh
        node.continuation := by
  simp only [footprintCheck, stepGrades, StepGrades.admits, Thunk.get, ExpressionEffects.writeWithin_eq_grades,
    ExpressionEffects.initWriteWithin_eq_grades, ExpressionEffects.denseWriteWithin_eq_grades,
    GraphCode.selectedWithinAt_eq_grades, GraphCode.selectedThrowsWithinAt_eq_grades]
  have hk : ∀ Φ : Footprints.Closed, (⟨.keep, .keep, .keep⟩ : Footprints.Closed).le Φ = true :=
    Footprints.Closed.empty_le
  generalize ExpressionEffects.check G c.context node.expression = a
  generalize ExpressionEffects.emptyType G c.type = b
  generalize c.context.any (ExpressionEffects.emptyType G ·) = d
  generalize stepDerivChecked G images codes sums c node stepK deriv = dc
  generalize GraphCode.selectedGrades F deriv = sel
  generalize GraphCode.selectedThrowGrades F deriv = selT
  generalize (Ψ == Footprints.Closed.top) = t
  generalize Φ.le Ψ = n
  cases a <;> cases b <;> cases d <;> cases dc <;> cases hsel : sel.isEmpty <;> cases hselT : selT.isEmpty <;>
    cases liveHandler <;> cases t <;> cases n <;>
    simp_all [List.any_append, List.isEmpty_iff, Bool.and_assoc, Bool.or_assoc]

/-- A selected call's exit summary (`Effect.summary`) at its actuals'
number, where its operands are values. -/
def selectedSummaries (e : ProgramCertificates.Evidence ι) : List (CallEffects.Exits CallEffects.ExitSpec) :=
  if ExpressionEffects.selectedOperands e then match ExpressionEffects.selectedEffect e with
    | some eff => [eff.summary (ExpressionEffects.actualsOf (ProgramCertificates.claim e).term).length]
    | none => []
  else []

/-- **A step's local certificate** (`StepCertificate`), at its claim `c`,
node, facts `stepK` and derivation `deriv`, its fresh slots `F`: an
inspection or an empty type keeps everything (the empty frame); a typed
write and an initializing write state their closed footprints' entries; a
call at its selected signature, its derivation checked, states the
signature's exit summary on both exits. -/
def stepCertificate (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (F : List Nat) (c : PointClaim ι) (node : Node)
    (stepK : Knowledge) (deriv : ProgramCertificates.Evidence ι) : StepCertificate :=
  let writes := (ExpressionEffects.writeGrades G c.context node.expression ++
    ExpressionEffects.initWriteGrades G c.context stepK node.expression ++
    ExpressionEffects.denseWriteGrades G c.context stepK node.expression).map
      fun g => ({ frame := g.fp, ensures := [] } : CallEffects.ExitSpec)
  let selected := selectedSummaries deriv
  let inspection := ExpressionEffects.check G c.context node.expression
  let emptyContext := c.context.any (ExpressionEffects.emptyType G ·)
  let checked : Thunk (List (CallEffects.Exits CallEffects.ExitSpec)) := Thunk.mk fun _ =>
    if selected.isEmpty then [] else if stepDerivChecked G images codes sums c node stepK deriv then selected else []
  let keepsAll : CallEffects.ExitSpec := { frame := [], ensures := [] }
  { normal := if inspection || ExpressionEffects.emptyType G c.type || emptyContext then [keepsAll]
      else writes ++ checked.get.map (·.normal)
    exceptional := if inspection || emptyContext then [keepsAll]
      else writes ++ checked.get.map (·.exceptional)
    fresh := GraphCode.freshPositions F (ProgramCertificates.claim deriv).term
    scope := ProgramCertificates.checkScope c.context.length node.expression }

omit [Hashable ι] [Instantiates ι] in
private theorem checked_map {α β : Type} (f : α → β) (xs : List α) (dc : Bool) :
    (if xs.isEmpty then [] else if dc then xs else []).map f =
      (if (xs.map f).isEmpty then [] else if dc then xs.map f else []) := by
  cases xs <;> cases dc <;> rfl

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
private theorem summaries_normal (F : List Nat) (deriv : ProgramCertificates.Evidence ι) :
    (selectedSummaries deriv).map (fun s => Footprints.Footprint.boundBelow
      (GraphCode.freshPositions F (ProgramCertificates.claim deriv).term) s.normal.frame) =
      GraphCode.selectedGrades F deriv := by
  unfold selectedSummaries GraphCode.selectedGrades
  cases ExpressionEffects.selectedOperands deriv <;> cases ExpressionEffects.selectedEffect deriv <;> rfl

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
private theorem summaries_exceptional (F : List Nat) (deriv : ProgramCertificates.Evidence ι) :
    (selectedSummaries deriv).map
      (fun s => Footprints.Footprint.boundBelow
        (GraphCode.freshPositions F (ProgramCertificates.claim deriv).term) s.exceptional.frame) =
      GraphCode.selectedThrowGrades F deriv := by
  unfold selectedSummaries GraphCode.selectedThrowGrades
  cases ExpressionEffects.selectedOperands deriv <;> cases ExpressionEffects.selectedEffect deriv <;> rfl

omit [Hashable ι] [Instantiates ι] in
/-- **The grades are the certificate's projection** (proved): each exit
specification's frame, closed below the invocation's mark, is the grade its
rule grants (`stepGrades`). -/
theorem stepCertificate_grades (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (F : List Nat) (c : PointClaim ι) (node : Node)
    (stepK : Knowledge) (deriv : ProgramCertificates.Evidence ι) :
    (stepCertificate G images codes sums F c node stepK deriv).grades =
      stepGrades G images codes sums F c node stepK deriv := by
  have hw : ∀ gs : List Footprints.Closed,
      (gs.map fun g => ({ frame := g.fp, ensures := [] } : CallEffects.ExitSpec)).map
        (fun x => Footprints.Footprint.boundBelow (GraphCode.freshPositions F (ProgramCertificates.claim deriv).term)
          x.frame) = gs := by
    intro gs
    simp only [List.map_map, Function.comp_def, Footprints.Footprint.boundBelow_fp, List.map_id']
  simp only [stepCertificate, stepGrades, StepCertificate.grades, Thunk.get]
  generalize stepDerivChecked G images codes sums c node stepK deriv = dc
  congr 1
  · split
    · rfl
    · rw [List.map_append, hw, List.map_map, checked_map]
      simp only [Function.comp_def]
      rw [summaries_normal]
  · split
    · rfl
    · rw [List.map_append, hw]
      congr 1
      rw [List.map_map, checked_map]
      simp only [Function.comp_def]
      rw [summaries_exceptional F deriv]

/-- **A return's checks** (`GraphCode.returnOk`, `checkReturnResult`), at
node `l` returning its result's name `result` from `entry` with the output
store `store`: a postcondition (`ensures`) entailed by the output's facts
over the result and the inputs' entry values (`startNames`); the goal: a
plain result's type, or a promise about the input in the goal's slot (its
name `argName`), the answer right and the argument, as the step's yields
leave it, within the promise. The refusal where one fails, the answers
after the subtyping searches, and the postcondition query's atom count
where it is made. -/
def returnCheck (G : NormalGraph ι) (images : InstanceImageCheck G) (goal : Goal ι)
    («ensures» : List HeapKnowledge.IndexFact) (c : PointClaim ι) (l : Nat) (entry : State) (store : Store)
    (result start : Nat) (startNames : List Nat) (argName : Option Nat) (yields : List (PromiseCalls.Yield ι))
    (debugNode : Nat) (answers : Answered G) : Option String × Answered G × Option Nat :=
  let width := c.context.length
  let pushedNames := result :: entry.names
  -- A postcondition at a return (`GraphCode.returnOk`): the output's facts
  -- over the result and the inputs' entry values entail it.
  let post : Option (Option String × Nat) :=
    if !ensures.isEmpty && !(ExpressionEffects.emptyType G c.type || c.context.any (ExpressionEffects.emptyType G ·)) then
      let wanted := GraphCode.namedInputs ensures
      let tracked : GraphCode.Tracked := wanted.filterMap fun (_, q) => do
        let nm ← startNames[q]?
        let j ← entry.names.idxOf? nm
        pure (j, q)
      let (k, _, _) := materialize { names := pushedNames, store } (width + 1) (0 :: tracked.map (·.1 + 1)) false
      let kOut := KnowledgeExpand.expandLinks (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G c.context) 1) k
      some (if !GraphCode.returnEntails kOut tracked ensures then
          some s!"return at node {l}: the postcondition{if l == debugNode then s!" tracked {tracked} k {reprStr kOut.indices}" else ""}"
        else none, (atomsOf k).length)
    else none
  let queried := post.map (·.2)
  match post with
  | some (some why, _) => (some why, answers, queried)
  | _ =>
    match goal with
    | .plain R => (if !(c.type == R || c.type.isEmpty) then some s!"return at node {l}" else none, answers, queried)
    | .guards T _ | .asserts T _ =>
      -- A promise about the input in the goal's slot (`checkReturnResult`):
      -- the answer right, and the argument, as the yields leave it, within
      -- the promise, at a slot holding the input's name.
      let answered := match goal with | .guards .. => true | _ => false
      let answerOk := if answered then BranchRefinement.onlyBoolean G c.type
        else PromiseCalls.onlyUndef G c.type
      let vacuous := if answered then BranchRefinement.impossible G c.type (.boolean true) else c.type.isEmpty
      let ys := yields.flatMap fun y => match entry.names[y.target]? with
        | some nm => (entry.names.zipIdx.filter (·.1 == nm)).map fun (_, j) => { y with target := j }
        | none => [y]
      let refined := PromiseCalls.refineBy G c.context (PromiseCalls.yieldFacts ys answered) 0
      let held := match argName with
        | some a => (entry.names.zipIdx.filter fun (x : Nat × Nat) => x.1 == a).map fun (x : Nat × Nat) => x.2
        | none => []
      let (within, answers) := held.foldl (fun (within, answers) p =>
        if within then (within, answers) else match refined[p]? with
          | some B => let (res, a') := subtypeUsing G images B T answers; (res.value.isSome, a')
          | none => (false, answers)) (false, answers)
      (if !(answerOk && (vacuous || within)) then
        some s!"return at node {l}: the promise{if l == debugNode then s!" answer {answerOk} vacuous {vacuous} held {held} arg {argName} start {start} slot {goal.slot} names {entry.names} yields {ys.length}" else ""}"
       else none, answers, queried)

/-- The store without its facts reading the heap (a cell, an element, a
read link, an index fact reading the heap) that `keep` does not hold: the
facts a throw keeps (`ControlFlow.handlerFacts`), or a writing step's facts
its rule does not read. -/
def Store.dropHeap (s : Store) (keep : Atom → Bool) : Store :=
  s.toList.foldl (fun (acc : Store) a => if keep a then acc else match a with
    | .cell _ | .elem _ => acc.remove a
    | .link g => if g.alias then acc else acc.remove a
    | .index x => if x.fact.envOnly then acc else acc.remove a
    | _ => acc) s

/-- An edge's store before its target's names: a handler's, the entry
store's heap-free facts; an edge observing the result, the output store with
the observation's facts (an alternative it contradicts released,
`HeapKnowledge.withElements`); a truthy promotion's likewise; else the
output store. -/
def edgeStoreOf (G : NormalGraph ι) (Γ : List (Ty ι)) (entryStore store : Store) (names pushedNames : List Nat)
    (width : Nat) (pushed isHandler : Bool) (observed : Option BranchRefinement.Observation) (promote : Option Bool) :
    Store :=
  if isHandler then entryStore.dropHeap fun _ => false else
  match observed, promote with
  | some o, _ =>
    let (k, pairs, table) := materialize { names, store } (if pushed then width + 1 else width) [0] false
      (observeElements := true)
    let k' := HeapKnowledge.withElements (HeapKnowledge.observeTyped G Γ k 0 o)
    let inverse : Std.HashMap Nat Nat := table.fold (fun acc nm s => acc.insert s nm) {}
    applyDelta store pairs k' false fun i => (inverse.get? i).orElse fun _ => names[i]?
  | none, some q =>
    let (k, pairs, table) := materialize { names := pushedNames, store } (width + 1) [0] false
      (observeElements := true)
    let k' := HeapKnowledge.withElements (HeapKnowledge.promoteTruthy k 0 q)
    let inverse : Std.HashMap Nat Nat := table.fold (fun acc nm s => acc.insert s nm) {}
    applyDelta store pairs k' false fun i => (inverse.get? i).orElse fun _ => pushedNames[i]?
  | none, none => store

/-- What a node or a later node reads of a state at the node's entry: the
slots (`none`, every slot; `liveSlots`), and the names it reads whatever
slot holds them (the inputs' entry values, which a return's postcondition
and promise read). -/
structure LiveSlots where
  slots : Option (Std.HashSet Nat) := none
  keep : List Nat := []
  deriving Inhabited

/-- The names the store `s` connects to the names `roots`, transitively,
the roots included, through every fact over two or more names that
`Store.drop` does not restate on the names it keeps. `Store.drop` restates
an unconditional linear or length fact (eliminating the dropped names), an
alias link (on the kept name it relates) and a separation fact (on the kept
partners); every other fact naming a dropped name leaves with it: a read
link (`o.f ↦ y` states the facts of the path `o.f` over `y`, and those of
`y` over the path), a conditional fact (`[if c] F`), an index fact of
another kind (an `every` fact bounded by a name, an element fact) and an
element fact. -/
def Store.connectedNames (s : Store) (roots : List Nat) : Std.HashSet Nat := Id.run do
  let mut seen : Std.HashSet Nat := roots.foldl (·.insert ·) {}
  let mut frontier := roots
  for _ in [0:s.size + 1] do
    if frontier.isEmpty then break
    let mut next := []
    for o in frontier do
      for a in s.about o do
        let reached : List Nat := match a with
          | .link g => if g.alias then [] else a.names
          | .index x => match x.cond, x.fact with
            | none, .linear _ | none, .length .. => []
            | _, _ => a.names
          | .elem _ => a.names
          | .cell _ | .value _ | .sep _ => []
        for x in reached do
          if !seen.contains x then
            seen := seen.insert x
            next := x :: next
    frontier := next
  return seen

/-- The names a target's slots `targetNames` hold that the target does not
read (`live`): connected to no slot it reads, nor to the names it keeps,
through the facts of the store `s` that `Store.drop` does not restate
(`Store.connectedNames`). -/
def deadNames (targetNames : List Nat) (live : LiveSlots) (s : Store) : List Nat :=
  match live.slots with
  | none => []
  | some L =>
    let roots := live.keep ++ (targetNames.zipIdx.filter fun (_, j) => L.contains j).map (·.1)
    let held := s.connectedNames roots
    (targetNames.filter (!held.contains ·)).eraseDups

/-- What an edge into a node other than a loop head carries, from the
source's names `names` on the edge and its store: the target's names (the
mapping applied), the store without the names the edge drops
(`droppedBy`, an unpushed result no slot holds, and the names no slot the
target reads holds, `deadNames` of its slots read `live`), the fresh names
it keeps (the result where pushed and fresh), and the implications naming
no dropped name. -/
def edgeTransfer (names : List Nat) (m : PointClaims.Mapping) (pushed isHandler outFresh : Bool) (entry : State)
    (result : Nat) (edgeStore : Store) (implies : List (PromiseCalls.Implication ι))
    (live : LiveSlots) : State × List (PromiseCalls.Implication ι) :=
  let targetNames := timedKind "edge names" fun _ => mapNames names m
  let gone := timedKind "edge dropped" fun _ => droppedBy names m targetNames ++
    (if !pushed && !entry.names.contains result then [result] else []) ++ deadNames targetNames live edgeStore
  let freshOut := (if pushed && !isHandler && outFresh && !entry.fresh.contains result then result :: entry.fresh
    else entry.fresh).filter (!gone.contains ·)
  let carried := timedKind "edge implications" fun _ => (keepFirst {} (implies.filter fun x =>
    !gone.contains x.test && !gone.contains x.target)).2.toList
  ({ names := targetNames, store := edgeStore.drop gone, fresh := freshOut }, carried)

/-- **An entailed bound's terms defined** in a predecessor's view `q` of a
merge, for the bound's atom `a` and its linear fact `F`: the view holds the
atom, or each term of `F` is an integer by the facts near the atom's names
(`HeapKnowledge.termDefined` over `Store.linearNear`): an entailment reads
an undefined term as 0. -/
def entailDefinedCheck (q : State) (a : Atom) (F : Linear.Fact HeapKnowledge.Term) : Bool :=
  q.store.live.contains a.canon || F.vars.all (HeapKnowledge.termDefined (q.store.linearNear a.names) ·)

/-- What a merge computes: the meet state, its implications, the next
fresh name, the facts its predecessors state that the met store lacks
(counted), each predecessor's state at the merge's names and its renaming. -/
structure Merged (ι : Type) where
  state : State
  implies : List (PromiseCalls.Implication ι)
  fresh : Nat
  diffCount : Nat
  views : List State
  renames : List (Std.HashMap Nat (List Nat))

/-- The linear negation of a linear fact, as atoms whose conjunction
contradicts it over integers. -/
def negLinear : Linear.Fact HeapKnowledge.Term → List HeapKnowledge.IndexAtom
  | .le F d => [{ fact := .linear (.le (F.map fun (t, c) => (t, -c)) (-d - 1)) }]
  | .ne F d => [{ fact := .linear (.le F d) }, { fact := .linear (.le (F.map fun (t, c) => (t, -c)) (-d)) }]

/-- Candidate disjunctive facts at a merge, at the merge's names: any
unconditional `.either` atom in `diffs` over live names not in `met`, and
`either (.linear G) F` for any differing unconditional linear path-condition
`G` over unchanged live names (`!phiNames`) and any differing unconditional
non-disjunctive fact `F` over live names mentioning a changed name (`phiNames`)
not in `met` such that every predecessor entails `G` or `F` (skipping pairs
already entailed by `met`). -/
def mergeDisjCandidates (live phiNames : Std.HashSet Nat) (met : Store)
    (diffs : List (List Atom)) (views : List State) : List HeapKnowledge.IndexAtom := Id.run do
  let mut seen : Std.HashSet Atom := {}
  let mut existing : List HeapKnowledge.IndexAtom := []
  let mut rawGuards : List (Atom × Linear.Fact HeapKnowledge.Term) := []
  let mut phiGuards : List (Atom × Linear.Fact HeapKnowledge.Term) := []
  let mut rawBodies : List (Atom × HeapKnowledge.IndexFact) := []
  for d in diffs do
    for a in d do
      if !seen.contains a && a.names.all live.contains && !met.holds a then
        seen := seen.insert a
        if let .index ⟨F, none, _⟩ := a then
          match F with
          | .either _ (.pastSafe _) => pure ()
          | .either .. => existing := { fact := F } :: existing
          | .guarded .. => pure ()
          | .linear L =>
            if a.names.any phiNames.contains then
              rawBodies := (a, F) :: rawBodies
              let singlePhi := a.names.all phiNames.contains &&
                match L with | .le [(_, _)] _ | .ne [(_, _)] _ => true | _ => false
              if singlePhi then phiGuards := (a, L) :: phiGuards
            else
              rawGuards := (a, L) :: rawGuards
          | .atIndex .. =>
            rawBodies := (a, F) :: rawBodies
          | _ =>
            if a.names.any phiNames.contains then
              rawBodies := (a, F) :: rawBodies
  if (rawGuards.isEmpty && phiGuards.isEmpty) || rawBodies.isEmpty then return existing
  let twoViews := views.length ≤ 2
  let linMask (a : Atom) (L : Linear.Fact HeapKnowledge.Term) : List Bool :=
    views.map fun (qs : State) =>
      if qs.store.holds a then entailDefinedCheck qs a L
      else if twoViews then false
      else entailDefinedCheck qs a L &&
        (Linear.Known.build (HeapKnowledge.linearRaw (qs.store.linearNear a.names)) []).entails L
  let guards := rawGuards.filterMap fun (a, L) =>
    let m := linMask a L
    if m.all id || m.all (!·) then none else some (a, L, m)
  let hasPhiAtIndex := rawBodies.any fun (ba, F) =>
    (match F with | .atIndex .. => true | _ => false) && ba.names.any phiNames.contains
  let pGuards := if !hasPhiAtIndex then [] else
    phiGuards.filterMap fun (a, L) =>
      if rawBodies.any (fun (ba, F) => (match F with | .atIndex .. => true | _ => false) &&
          ba.names.any phiNames.contains && a.names.any ba.names.contains) then
        let m := linMask a L
        if m.all id || m.all (!·) then none else some (a, L, m)
      else none
  if guards.isEmpty && pGuards.isEmpty then return existing
  let bodies := rawBodies.filterMap fun (a, F) =>
    let m := match F with
      | .linear L => linMask a L
      | _ => views.map fun (qs : State) => qs.store.holds a
    if m.all id || m.all (!·) then none else some (a, F, m)
  if bodies.isEmpty then return existing
  let mut out : List HeapKnowledge.IndexAtom := existing
  for (ga, gL, gM) in guards do
    for (ba, bF, bM) in bodies do
      if (gM.zip bM).all (fun (x, y) => x || y) then
        let taut := match bF with
          | .linear bL =>
            let near := met.linearNear (ga.names ++ ba.names)
            let nearK := Linear.Known.build (HeapKnowledge.linearRaw near) []
            ((HeapKnowledge.linearRaw (negLinear gL)).foldl Linear.Known.add nearK).entails bL ||
            ((HeapKnowledge.linearRaw (negLinear bL)).foldl Linear.Known.add nearK).entails gL
          | _ => false
        if !taut then
          out := { fact := .either (.linear gL) bF } :: out
  for (ga, gL, gM) in pGuards do
    for (ba, bF, bM) in bodies do
      if (match bF with | .atIndex .. => true | _ => false) &&
          ba.names.any phiNames.contains && ga.names.any ba.names.contains then
        if (gM.zip bM).all (fun (x, y) => x || y) then
          out := { fact := .either (.linear gL) bF } :: out
  return out

/-- The merge of the states `preds` entering a node of context `context`
through the edges `edgesIn` (each as the search's merge reads it), its
fresh names from `fresh`: the names, the facts every predecessor holds and
those a join keeps, the fresh spines, the implications. -/
def mergeState (G : NormalGraph ι) (context : List (Ty ι)) (preds : List State)
    (edgesIn : List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) (fresh : Nat) :
    Merged ι := Id.run do
  let s := preds.headD { names := [] }
  let rest := preds.tail
  -- Names: a slot whose predecessors' names differ takes a fresh one.
  let width := context.length
  let mut fresh := fresh
  let arrs := preds.map (·.names.toArray)
  let mut names : Array Nat := Array.mkEmpty width
  -- A name a predecessor holds at several slots that take different
  -- fresh names is renamed to each; slots whose predecessors' names
  -- agree take one fresh name.
  let mut renames : List (Std.HashMap Nat (List Nat)) := arrs.map fun _ => {}
  let mut phis : Std.HashMap (List Nat) Nat := {}
  for i in List.range width do
    let ns := arrs.map (·.getD i 0)
    let n0 := ns.headD 0
    if ns.all (· == n0) then names := names.push n0
    else match phis.get? ns with
      | some φ => names := names.push φ
      | none =>
        names := names.push fresh
        phis := phis.insert ns fresh
        renames := (renames.zip ns).map fun (m, x) => m.insert x (fresh :: m.getD x [])
        fresh := fresh + 1
  let mergedNames := names.toList
  let live := Std.HashSet.ofList mergedNames
  -- Each predecessor's facts about the names it renames, restated at
  -- the fresh names (a name a slot keeps that another slot's fresh name
  -- renames is stated equal to it, as are one name's fresh names).
  -- The alias link always; the equality of their numbers only where
  -- the predecessor's facts make `x` an integer (`Store.integral`): a
  -- linear fact holds only where its terms denote integers.
  let eqAtoms := fun (int : Bool) (φ x : Nat) => Atom.link { cell := φ, value := x, alias := true } ::
    (if !int then [] else
    [.index ⟨.linear (.le [(HeapKnowledge.Term.value φ, 1), (HeapKnowledge.Term.value x, -1)] 0), none, false⟩,
    .index ⟨.linear (.le [(HeapKnowledge.Term.value φ, -1), (HeapKnowledge.Term.value x, 1)] 0), none, false⟩])
  let variants : List (Std.HashSet Atom) := (preds.zip renames).map fun ((st : State), (m : Std.HashMap Nat (List Nat))) =>
    let equal := m.fold (fun (acc : List Atom) x φs =>
      let int := st.store.integral x
      (if names.contains x then φs.flatMap (eqAtoms int · x) else []) ++
      (φs.zip φs.tail).flatMap (fun (φ, ψ) => eqAtoms int ψ φ) ++ acc) []
    let about := m.fold (fun (acc : List Atom) x _ => st.store.about x ++ acc) []
    (about.foldl (fun (acc : Std.HashSet Atom) a => acc.insertMany (Atom.renameEach m a)) {}).insertMany equal
  -- The facts every predecessor holds: the first's store less each fact
  -- another lacks, found by what differs between the stores
  -- (`Store.diff`), and the restated facts every one
  -- states.
  let mut met := s.store
  for q in rest do
    for a in (timedKind "merge diff" fun _ => Store.diff met q.store).1 do met := met.remove a
  let firstV := variants.headD {}
  met := timedKind "meet" fun _ => firstV.fold (fun (acc : Store) a =>
    if variants.tail.all (·.contains a) then acc.add a else acc) met
  -- The names a predecessor renames that no slot of the merge holds
  -- leave the store once (`Store.drop`).
  let renamedAway := (keepFirst {} (renames.flatMap fun (m : Std.HashMap Nat (List Nat)) =>
    m.fold (fun acc x _ => if live.contains x then acc else x :: acc) [])).2.toList
  met := met.drop renamedAway
  let met0 := met
  -- What each predecessor states that the merge does not, at the merge's
  -- names: its facts the met store lacks, a fact over a name it renames
  -- by its restatements.
  let diffs : List (List Atom) := ((preds.zip renames).zip variants).map
    fun (((st : State), (m : Std.HashMap Nat (List Nat))), (v : Std.HashSet Atom)) =>
      ((timedKind "merge diff" fun _ => Store.diff met0 st.store).2.filter fun a =>
        !a.names.any fun x => m.contains x && !live.contains x) ++
        v.fold (fun acc a => if met0.live.contains a.canon then acc else a :: acc) []
  let diffCount := diffs.foldl (fun acc d => acc + d.length) 0
  -- A linear bound every predecessor states of one form (under one
  -- condition), at the weakest of their bounds.
  let bounds : List (Std.HashMap (Linear.Form HeapKnowledge.Term × Option Nat × Bool) Int) := diffs.map fun d =>
    d.foldl (fun acc a => match a with
      | .index ⟨.linear (.le F d), c, neg⟩ =>
        let F := Linear.normalize F
        acc.insert (F, c, neg) (match acc.get? (F, c, neg) with | some d' => min d d' | none => d)
      | _ => acc) {}
  met := match bounds with
    | b0 :: bs => b0.fold (fun (acc : Store) key d => Id.run do
        let mut weakest := d
        for b in bs do
          match b.get? key with
          | some d' => weakest := max weakest d'
          | none => return acc
        let (F, c, neg) := key
        return acc.add (.index ⟨.linear (.le F weakest), c, neg⟩)) met
    | [] => met
  -- Each predecessor's state at the merge's names: the met facts and its
  -- own differences, sharing the met store.
  let views : List State := diffs.map fun d =>
    { names := mergedNames, store := d.foldl Store.add met0 }
  -- A linear bound over the merge's names one predecessor states and
  -- every other entails over its linear facts near the bound's names
  -- (`HeapKnowledge.entailsKnown`), as an edge's entailment establishes a
  -- fact at a statement entry.
  met := timedKind "meet entailed" fun _ => Id.run do
    let mut acc := met
    let mut seen : Std.HashSet Atom := {}
    for d in diffs do
      for a in d do
        if let .index ⟨.linear F, none, _⟩ := a then
          if !seen.contains a && a.names.all live.contains && !acc.holds a then
            seen := seen.insert a
            if views.all fun (qs : State) => qs.store.holds a ||
                HeapKnowledge.entailsKnown (qs.store.linearNear a.names) F then
              -- Its terms defined in every view (`entailDefinedCheck`).
              if views.all fun (qs : State) => entailDefinedCheck qs a F then
                acc := acc.add a
    return acc
  -- The guarded facts a join keeps, over the facts that differ: the
  -- search's join (`CertificateProducer.joinGuarded`) over each
  -- predecessor's facts near the differing guarded facts, read links and
  -- separations, each predecessor's guards first also lowered once
  -- through its read links (`HeapKnowledge.lowerGuards`): a guard on a
  -- path two reads long reaches the value the second read gives; and a
  -- fact one predecessor states of a slot another holds a tag's value
  -- in, guarded by that tag (`x === null || F`), as the join guards a
  -- spine separation; each kept where every predecessor's facts entail it.
  let tags : List HeapKnowledge.GuardTag := [.null, .undef, .tru, .fls]
  let tagged := diffs.flatMap fun d => d.filterMap fun a => match a with
    | .value f => if f.contents != {} && tags.any (fun g => HeapKnowledge.onlyTag f.contents g) then some f.slot else none
    | _ => none
  let seeds := (diffs.flatMap fun d => d.flatMap fun a => match a with
    | .index ⟨.guarded .., _, _⟩ | .index ⟨.spineApart .., _, _⟩ | .index ⟨.atIndex .., _, _⟩
    | .index ⟨.every .., _, _⟩ | .index ⟨.apart .., _, _⟩ | .link _ => a.names
    | _ => [])
  let seeds := if tagged.isEmpty then seeds else seeds ++ tagged ++
    (diffs.flatMap fun d => d.flatMap fun a => match a with
      | .index _ => a.names
      | _ => if a.names.any tagged.contains then a.names else [])
  let seedSlots := (keepFirst {} (seeds.filterMap mergedNames.idxOf?)).2.toList
  let guarded0 : List HeapKnowledge.IndexAtom := if seedSlots.isEmpty then [] else Id.run do
    let projections := views.map fun ps => (materialize ps width seedSlots false).1
    let common := (materialize { names := mergedNames, store := met0 } width seedSlots false).1
    let flat := projections.map fun (p : Knowledge) =>
      { p with indices := p.indices.filter fun a => match a.fact with | .either _ _ => false | _ => true }
    let lowered := flat.map fun (p : Knowledge) =>
      { p with indices := p.indices ++ ((HeapKnowledge.lowerGuards p.links p.indices).filter (!p.indices.contains ·)) }
    let joined := timedKind "meet guarded" fun _ => CertificateProducer.joinGuarded lowered common
    let tagged := timedKind "meet tagged" fun _ =>
      let taggedSlots := tagged.filterMap mergedNames.idxOf?
      let nullishPos := ((projections.flatMap fun (o : Knowledge) => o.values.flatMap fun f =>
        if f.contents == {} then [] else
        let cls := HeapLinks.aliases o.links f.slot
        if !cls.any taggedSlots.contains then [] else
        (tags.filter fun g => HeapKnowledge.onlyTag f.contents g).flatMap fun g =>
          cls.map (·, g))).eraseDups.filter fun (z, g) =>
            !projections.all (fun o => HeapKnowledge.guardTags o z [] g)
      let nullish := (nullishPos ++ nullishPos.filterMap fun (z, g) =>
        if (g == .null || g == .undef) && projections.any (fun o => HeapKnowledge.guardTags o z [] g.complement) then
          some (z, g.complement)
        else none).eraseDups
      if nullish.isEmpty then [] else
      let commonSet : Std.HashSet HeapKnowledge.IndexAtom := common.indices.foldl (·.insert ·) {}
      let indexCands := projections.flatMap fun (p : Knowledge) => p.indices.flatMap fun a =>
        if a.cond.isSome || commonSet.contains a then [] else match a.fact with
        | .either .. => []
        | .guarded s [] t B =>
            let cls := HeapLinks.aliases p.links s
            nullish.filterMap fun (z, g) =>
              if cls.contains z then
                if !g.isPositive || g == t.complement then none
                else if t == g then some ({ fact := .guarded z [] t B } : HeapKnowledge.IndexAtom)
                else match B with
                  | .guarded s' [] t' _ =>
                    if (HeapLinks.aliases p.links s').contains z && t' == g then some a else none
                  | .guarded .. => none
                  | _ => some ({ fact := .guarded z [] g (.guarded s [] t B) } : HeapKnowledge.IndexAtom)
              else match B with
                | .guarded .. => none
                | _ =>
                  if HeapKnowledge.guardTags p z [] g then none
                  else some ({ fact := .guarded z [] g (.guarded s [] t B) } : HeapKnowledge.IndexAtom)
        | .guarded .. => []
        | F =>
            let single := nullish.filterMap fun (z, g) =>
              if HeapKnowledge.guardTags p z [] g then none
              else some ({ fact := .guarded z [] g F } : HeapKnowledge.IndexAtom)
            let pair := match F with
              | .element .. | .linear .. =>
                nullishPos.flatMap fun (z1, g1) =>
                  if HeapKnowledge.guardTags p z1 [] g1 then []
                  else nullishPos.filterMap fun (z2, g2) =>
                    if z1 < z2 && !HeapKnowledge.guardTags p z2 [] g2 then
                      some ({ fact := .guarded z1 [] g1 (.guarded z2 [] g2 F) } : HeapKnowledge.IndexAtom)
                    else none
              | _ => []
            single ++ pair
      let linkCands := projections.flatMap fun (p : Knowledge) => p.links.flatMap fun l =>
        if l.alias || l.optional then [] else match l.field with
        | .str f =>
          let cls := HeapLinks.aliases p.links l.value
          nullish.filterMap fun (z, g) =>
            if g.isPositive && cls.contains z && !HeapKnowledge.guardTags p z [] g then some ({ fact := .guarded z [] g (.fieldRead z l.cell f) } : HeapKnowledge.IndexAtom)
            else none
        | .sym _ => []
      let candidates := (keepFirst {} (indexCands ++ linkCands)).2.toList
      flat.foldl (fun cs p => HeapKnowledge.indicesFilter p cs) candidates
    return joined ++ tagged
  let phiNames : Std.HashSet Nat := renames.foldl (fun acc m =>
    m.fold (fun acc _ φs => φs.foldl (·.insert ·) acc) acc) {}
  let disjoined : List HeapKnowledge.IndexAtom := timedKind "meet disjoined" fun _ =>
    let disjNameCands := mergeDisjCandidates live phiNames met diffs views
    if disjNameCands.isEmpty then [] else
    let candidates := (keepFirst {} (disjNameCands.filterMap fun a => match (Atom.index a).rename mergedNames.idxOf? with
      | some (.index x) => some x
      | _ => none)).2.toList
    if candidates.isEmpty then [] else
    let slots := (candidates.flatMap (·.fact.slots)).eraseDups
    let (withAt, plain) := candidates.partition (·.fact.hasAtIndex)
    let viewsK := views.map fun ps => (materialize ps width slots false).1
    let keptPlain := if plain.isEmpty then [] else
      let plainSet : Std.HashSet HeapKnowledge.IndexAtom := Std.HashSet.ofList plain
      let plainViews := viewsK.map fun p =>
        { p with indices := p.indices.filter fun x =>
          plainSet.contains x || match x.fact with | .either _ _ => false | _ => true }
      plainViews.foldl (fun cs p => HeapKnowledge.indicesFilter p cs false) plain
    let keptAt := if withAt.isEmpty then [] else
      let atViews := viewsK.map fun p =>
        { p with indices := p.indices.filter fun x =>
          withAt.contains x || match x.fact with | .either _ _ => x.fact.hasAtIndex | _ => true }
      atViews.foldl (fun cs p => HeapKnowledge.indicesFilter p cs) withAt
    keptPlain ++ keptAt
  let guarded := guarded0 ++ disjoined
  met := guarded.foldl (fun (acc : Store) x => match (Atom.index x).rename (mergedNames[·]?) with
    | some a => acc.add a
    | none => acc) met
  -- A name holds a fresh spine where every predecessor's does.
  let freshLists := (preds.zip renames).map fun ((st : State), (m : Std.HashMap Nat (List Nat))) =>
    st.fresh.flatMap fun x => x :: m.getD x []
  let met' := match freshLists with
    | f0 :: fs => f0.filter fun x => fs.all (·.contains x)
    | [] => []
  let state : State := { names := mergedNames, store := met, fresh := met' }
  -- The implications the merge establishes, as the search's merge
  -- finds them (`CertificateProducer.meetImplications`), at its names;
  -- none where no edge carries one and no slot an edge's type differs
  -- at is a test some edge's type answers `false`.
  let some_ := edgesIn.any (fun (_, xs, _) => !xs.isEmpty) || Id.run do
    let some (Γ0, _, m0) := edgesIn.head? | return false
    for t in List.range width do
      let A0 := Γ0[PointClaims.slot m0 t]?
      let differs := edgesIn.any fun (Γ, _, m) => match Γ[PointClaims.slot m t]?, A0 with
        | some A, some B => !same A B
        | _, _ => true
      if differs && edgesIn.any (fun (Γ, _, m) => (Γ[PointClaims.slot m t]?).any (BranchRefinement.impossible G · (.boolean true))) then
        return true
    return false
  let implies := if !some_ then [] else
    let joinedImpl := timedKind "meet implications" fun _ =>
      CertificateProducer.meetImplications G edgesIn width context
    -- Each kept where every incoming edge establishes it
    -- (`PromiseCalls.impliesCheck`, as an edge into a target carries it).
    let joinedImpl := timedKind "meet implications checked" fun _ => joinedImpl.filter fun x =>
      edgesIn.all fun (Γ, xs, m) => PromiseCalls.impliesCheck G Γ xs m [x]
    (keepFirst {} (joinedImpl.filterMap fun (x : PromiseCalls.Implication ι) => do
      pure (⟨← mergedNames[x.test]?, ← mergedNames[x.target]?, x.type⟩ : PromiseCalls.Implication ι))).2.toList
  return { state, implies, fresh, diffCount, views, renames }

/-- What a node's step counts: its rule applications (over every fact
among them), its calls read off their signature, its copies. -/
structure StepStats where
  rules : Nat := 0
  fullRules : Nat := 0
  directCalls : Nat := 0
  copies : Nat := 0
  /-- Whether the step was refused for having no derivation, the search
  having found none. -/
  underivable : Bool := false

/-- **The name of a step's result** and the next fresh name, from the
names at the slots `names`, the store `s` and the next fresh name `fresh`:
a read of a slot gives the slot's value, so its result keeps the slot's
name; a read of the field `f` of a slot holding the name `o`, where the
store holds a read link `o.f ↦ y`, gives the value that link states (the
link holds in the current heap, and a read of `f` there gives `y`), so its
result is `y`; any other result is the fresh name. -/
def resultName (t : Tm) (names : List Nat) (s : Store) (fresh : Nat) : Nat × Nat :=
  match t with
  | .var i => match names[i]? with
    | some x => (x, fresh)
    | none => (fresh, fresh + 1)
  | .readAt f (.var j) => match names[j]?.bind (s.readName · f) with
    | some y => (y, fresh)
    | none => (fresh, fresh + 1)
  | _ => (fresh, fresh + 1)

/-- A node's checked step: the result's name, the store after the step, the
next fresh name, whether it is a copy, and the step's input and output
knowledge at slots, its derivation and its evidence, read where an edge or a
footprint needs them. -/
structure Stepped (ι : Type) where
  result : Nat
  store : Store
  fresh : Nat
  copied : Bool
  stepK : Knowledge := {}
  stepOut : Knowledge := {}
  stepDeriv : Option (ProgramCertificates.Evidence ι) := none
  stepEffect : Option (HeapExpressionRules.StepEvidence ι) := none

/-- Whether every entry of `T` is covered by some support spec in `Ss`
(`Confinement.FrameSpec.covers`). -/
def footprintSupportedIn (Ss : List Confinement.FrameSpec) (T : Footprints.Footprint) : Bool :=
  Ss.any fun S => S.covers T

/-- A fact's produced support (`IndexFact.support?`, no stable key) is covered
by one of the support specs `Ss`. -/
def supportedIn (Ss : List Confinement.FrameSpec) (F : HeapKnowledge.IndexFact) : Bool :=
  match F.support? {} with
  | some T => footprintSupportedIn Ss T
  | none => false

/-- **The facts a framed node's return keeps** (the draft "Framed
acceptance", "The graph at framed returns"): the heap facts of its entry's
knowledge (cells, links, elements, and index atoms) whose support is covered
by a support spec it keeps (`footprintSupportedIn`, `supportedIn`), renamed past
the node's result. -/
def framedKept (Ss : List Confinement.FrameSpec) (k : Knowledge) : List Atom :=
  (HeapFacts.shift (k.cells.filter fun f => footprintSupportedIn Ss (Footprints.FactKind.cell f).support)).map Atom.cell ++
  (HeapLinks.pull (k.links.filter fun g => footprintSupportedIn Ss (Footprints.FactKind.link g).support)
    (fun i => [i + 1])).map Atom.link ++
  (HeapKnowledge.shiftElems (k.elems.filter fun a =>
    footprintSupportedIn Ss (Footprints.FactKind.elems a.slot a.pred).support)).map Atom.elem ++
  (HeapKnowledge.shiftIndices (k.indices.filter fun a => supportedIn Ss a.fact)).map Atom.index

/-- The support specs a framed node keeps, among the framed nodes `framed`
with their support specs; none at a node no entry names. -/
def framedAt (framed : List (Nat × List Confinement.FrameSpec)) (l : Nat) : Option (List Confinement.FrameSpec) :=
  (framed.find? (·.1 == l)).map (·.2)

/-- The store `s` with the atoms `kept`, at slots, added over the
names `names` hold (slot `i` the name `names[i]`). -/
def keepStore (names : List Nat) (kept : List Atom) (s : Store) : Store :=
  kept.foldl (fun s a => match a.rename (names[·]?) with
    | some b => s.add b
    | none => s) s

/-- **The step a framed node's exits read**: the step `st` from the entry
`entry`, its store holding, at a framed node keeping the support specs `kept`,
the facts of the step's input those support specs keep (`framedKept`) over the
names after the step; the step itself at another node. -/
def keptStep (kept : Option (List Confinement.FrameSpec)) (entry : State) (st : Stepped ι) : Stepped ι :=
  let keep := (kept.map (fun Ss => framedKept Ss st.stepK)).getD []
  { st with store := keepStore (st.result :: entry.names) keep st.store }

/-- `b`'s answers with `a`'s read-summary table as their table's prefix:
`a`'s table, then `b`'s entries past `a`'s length (`b` itself where `a`'s
table is a prefix of `b`'s). -/
def keepSummaries {G : NormalGraph ι} (a b : Answered G) : Answered G :=
  { b with summaries := a.summaries ++ b.summaries.extract a.summaries.size b.summaries.size }

/-- The step of node `l` (its claim `c`, the slots `ms` its expression
reads) from the state `entry`: a copy of a slot at the claim's type, a call
read off its callee's signatures (`directCall`), else the search's evidence;
its output the checker's `select` of that evidence, its tree checked where
`select` does not check it (`PassChecker.selectChecks`), a step that may
write selected again over every fact; the store after it by its delta. The
refusal where a check fails. -/
def checkedStep (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (suggestions : List (Sequent ι)) (index : KnownIndex ι) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images) (undefTy : Option (Ty ι))
    (l : Nat) (node : Node) (c : PointClaim ι) (entry : State) (ms : List Nat) (fresh : Nat) (answers : Answered G) :
    Except String (Stepped ι) × StepStats × Answered G := Id.run do
  let checker := passChecker.checker
  -- Whether `select` checks the step (`PassChecker.select_eq_run`).
  let selectChecks := passChecker.selectChecks
  let width := c.context.length
  let mut fresh := fresh
  let mut answers := answers
  let mut stats : StepStats := {}
  -- A read of a slot whose type is the claim's: the result is that slot's
  -- value, named as it (`HeapExpressionRules.copy`).
  let copied : Option Nat := timedKind "node copied" fun _ => match node.expression with
    | .var i => if (c.context[i]?).any (· == c.type) && (IndexWrites.typeInt G c.context i).isNone then
        entry.names[i]? else none
    | _ => none
  let mut store := entry.store
  let mut result : Nat := 0
  -- The step's input and output at slots and its derivation, read where an
  -- edge needs the step's yields.
  let mut stepK : Knowledge := {}
  let mut stepOut : Knowledge := {}
  let mut stepDeriv : Option (ProgramCertificates.Evidence ι) := none
  let mut stepEffect : Option (HeapExpressionRules.StepEvidence ι) := none
  match copied with
  | some x =>
    stats := { stats with copies := stats.copies + 1 }
    result := x
  | none =>
    -- A construction, fresh-returning call, or array object allocation reads every fact (`wholeStepOf`).
    let wholeStep := wholeStepOf G c.context node.expression
    -- A test, a conditional or a read of a slot reads the facts over its
    -- names and their aliases; a step that may need an entailment over
    -- them also reads the linear facts they chain through.
    let (k, pairs, table) := materialize entry width ms wholeStep
    let kE := IndexWrites.typedKnowledge G c.context (KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G c.context) k) ms
    -- The step is checked at its context refined by its facts' safe
    -- integers (`PromiseCalls.intRefine`).
    let Γr := PromiseCalls.intRefine G c.context kE.indices
    let own := (keepFirst {} (c.type :: ms.filterMap fun i => Γr[i]?)).2.toList
    let j : Sequent ι := ⟨Γr, node.expression, c.type⟩
    let kindKey := SinglePassStats.termKind node.expression
    -- Each precondition the call's signatures state, decided once, where the
    -- search first asks it (`admitsNear`).
    let kPre := Thunk.mk fun _ => HeapKnowledge.unguardedByTypes G Γr kE
    let stated : List ((Option CallEffects.ElemPred × List HeapKnowledge.IndexFact) × Thunk Bool) :=
      own.foldl (fun acc F => match PositiveRules.expand G F with
        | [PositiveNormalization.Clause.arrs L _] | [PositiveNormalization.Clause.callable _ _ L _ _] => L.foldl (fun acc p =>
            let key := (p.effect.requires, p.effect.pre)
            if acc.any (·.1 == key) then acc
            else acc ++ [(key, Thunk.mk fun _ => admitsNear kPre.get p.effect node.expression)]) acc
        | _ => acc) []
    let admits := fun (eff : CallEffects.Effect) (t : Tm) =>
      if t == node.expression then
        match stated.find? (·.1 == (eff.requires, eff.pre)) with
        | some (_, v) => v.get
        | none => admitsNear kPre.get eff t
      else admitsNear kPre.get eff t
    -- A call of a slot: its derivation read off the callee's signatures
    -- (`directCall`), its step `ordinary`; otherwise the search.
    let (direct, a0) := match node.expression with
      | .invoke .. => timedKind "direct call" fun _ => directCall G images Γr node.expression c.type admits undefTy answers
      | _ => (none, answers)
    answers := keepSummaries answers a0
    let sums := answers.summaries.toList
    let (r, a) := match direct with
      | some (e, _) =>
        -- The proved layers' output (`Checker.ordinary`) at the call's
        -- `ordinary` step over the facts it names.
        let step : HeapExpressionRules.StepEvidence ι := .ordinary e
        (timedKind "direct call output" fun _ => (checker.select j kE step codes sums).map fun out =>
          (some e, step, out), answers)
      | none => timedKind (if kindKey == "invoke" then s!"invoke facts {(atomsOf k).length / 10 * 10}" else kindKey) fun _ =>
        expressionEffectUsing G images pool fuel j kE suggestions index codes aliases checker (some own)
          (some admits) answers
    answers := keepSummaries answers a
    stats := { stats with rules := stats.rules + 1, directCalls := stats.directCalls + (if direct.isSome then 1 else 0) }
    let some (deriv, effect, searched) := r.value | return (.error s!"expression at node {l}: {(reprStr node.expression).take 300}", { stats with underivable := direct.isNone }, answers)
    -- The output the checker selects for the step the search returned,
    -- computed here: the search's own output is not applied.
    let out? : Option Knowledge := if direct.isSome then some searched
      else (checker.select j kE effect codes answers.summaries.toList).value
    let some out := out? | return (.error s!"expression at node {l}: the selected step", stats, answers)
    -- The step's derivation checked as the checker's `run` checks it
    -- (`checkStepResult`'s tree check): the search's `select` takes it as
    -- given.
    let tree := match effect with
      | .slicedRead _ _ _ e _ => some e
      | _ => effect.proof?
    -- A checker whose `select` is its `run` (a qualified body's) has
    -- checked the derivation already.
    -- The tree `requiresTree` alone accepted, at the step's facts: a
    -- `select` over other facts checks it again there.
    let mut preconditioned : Option (ProgramCertificates.Evidence ι) := none
    if let some p := (if selectChecks then none else tree) then
      -- A call at a precondition the step's facts establish is checked as
      -- `requiringCalls` checks it (`PromiseCalls.requiresTree`).
      -- The read summaries the step's search added included.
      let sums := answers.summaries.toList
      if !(timedKind "tree check" fun _ => ProgramCertificates.checkTreeUsing G images p codes sums) then
        if PromiseCalls.requiresTree G images kE codes sums p then preconditioned := some p
        else return (.error s!"expression at node {l}: its derivation", stats, answers)
    -- The step's normal effect, as the checker's rule deciding it states it
    -- (`Checker.normal`), at the summaries the step is selected and checked
    -- with: where it is empty, the tolerant frame at the support `all` keeps
    -- every fact the step is not handed, and the step's delta is applied to
    -- the whole store.
    let preserving := checker.normal j kE effect codes answers.summaries.toList == Footprints.Closed.empty
    -- A slot's read keeps the slot's name; a field's read the name its
    -- read link gives (`resultName`).
    let named := resultName node.expression entry.names entry.store fresh
    result := named.1
    fresh := named.2
    stepK := kE
    stepOut := out
    stepDeriv := deriv
    stepEffect := some effect
    if preserving then
      let inverse : Std.HashMap Nat Nat := table.fold (fun acc nm s => acc.insert s nm) {}
      store := applyDelta store pairs out true fun i => if i == 0 then some result else (inverse.get? (i - 1)).orElse fun _ => entry.names[i - 1]?
    else
      -- A step that may write: its rule reads every fact.
      let (k, pairs, table) := materialize entry width ms true
      -- A heap fact over a name no slot holds is not among the facts the
      -- rule reads, so its output does not say whether the step keeps it:
      -- it is dropped (the handler's filter's heap facts); a heap-free
      -- fact stays.
      let renamed : Std.HashSet Atom := pairs.foldl (fun acc (a, _) => acc.insert a) {}
      store := store.dropHeap renamed.contains
      let kE := IndexWrites.typedKnowledge G c.context (KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G c.context) k) ms
      -- The step the search selected over the facts the expression names,
      -- its output over every fact.
      let sums := answers.summaries.toList
      -- A tree only its precondition accepted, checked at every fact.
      if let some p := preconditioned then
        if !PromiseCalls.requiresTree G images kE codes sums p then
          return (.error s!"expression at node {l} over every fact: its derivation", stats, answers)
      let r := timedKind ("whole " ++ kindKey) fun _ =>
        checker.select j kE effect codes sums
      stats := { stats with rules := stats.rules + 1, fullRules := stats.fullRules + 1 }
      let some out := r.value | return (.error s!"expression at node {l} over every fact", stats, answers)
      -- With the integer facts the step's context was refined by, where
      -- they refined it.
      stepK := if Γr == c.context then kE else PromiseCalls.withInts kE stepK
      stepOut := out
      let inverse : Std.HashMap Nat Nat := table.fold (fun acc nm s => acc.insert s nm) {}
      store := applyDelta store pairs out true fun i => if i == 0 then some result else (inverse.get? (i - 1)).orElse fun _ => entry.names[i - 1]?
  return (.ok { result, store, fresh, copied := copied.isSome, stepK, stepOut, stepDeriv, stepEffect }, stats, answers)

/-- A head's entry state: its given invariant `g` over fresh names from
`fresh` (the start's own names at the start), a slot its given invariant
states holds an input's entry value (`inputSlots`, `GraphCode.trackTable`'s
pairs) or the promised input (`argSlots`) keeping that input's name; the
implications it states, over those names; the next fresh name. -/
def headEntry (g : Knowledge) (isStart : Bool) (width fresh : Nat) (startNames : List Nat) (argName : Option Nat)
    (argSlots : List Nat) (inputSlots : List (Nat × Nat)) (implies : List (PromiseCalls.Implication ι))
    (freshSlots : List Nat := []) :
    State × List (PromiseCalls.Implication ι) × Nat :=
  let base := if isStart then startNames.headD 0 else fresh
  let next := if isStart then fresh else fresh + width
  let names := (List.range width).map fun i =>
    match (inputSlots.find? (·.1 == i)).bind fun (_, q) => startNames[q]? with
    | some x => x
    | none => match argName with
      | some a => if argSlots.contains i then a else i + base
      | none => i + base
  let f := fun (i : Nat) => names[i]?
  let store := timedKind "head state" fun _ => (atomsOf g).foldl (fun s a => match a.rename f with
    | some b => s.add b | none => s) {}
  let freshNames := if isStart then [] else freshSlots.filterMap f
  ({ names, store, fresh := freshNames }, implies.filterMap (fun x => do pure ⟨← f x.test, ← f x.target, x.type⟩), next)

/-- What the walk records of one label: whether it was visited; the fresh
counter on entry; its entry state and implications (after the head entry,
the single state or the merge, and a written assertion's facts at a node
other than a head); the fresh counter its step starts from, the length of
the read-summary table it starts from, the step's result and the state
after it; whether its footprint check and
its return check passed (each `true` where it makes none); at a merge its
context and the fresh counter the merge started from; under a regional
check, the regional facts that check used at the label itself. -/
structure LabelWalk (ι : Type) where
  visited : Bool := false
  entryFresh : Nat := 0
  entry : Option State := none
  implies : List (PromiseCalls.Implication ι) := []
  stepFresh : Nat := 0
  stepSummaries : Nat := 0
  stepped : Option (Stepped ι) := none
  after : Option State := none
  bounded : Bool := false
  returned : Bool := false
  merge : Option (List (Ty ι) × Nat) := none
  region : Option RegionState := none

/-- An edge the walk processed: its source, its target with the mapping,
whether it pushes the result, the implications it carries (into a node
other than a head, those naming no name it drops), and whether some
environment may meet its context (its context satisfiable and its
observation possible). -/
structure EdgeWalk (ι : Type) where
  source : Nat
  target : Target
  pushed : Bool
  carried : List (PromiseCalls.Implication ι) := []
  meets : Bool := true

/-- The walk's record: per label what `LabelWalk` states, the states and
implications every processed edge carried into it, the edges into a merge
as the merge reads them; the processed edges in order; the nodes visited;
under `grading`, each visit's record of its step's local effect, in the
order of the visits (`VisitRecord`). -/
structure Walk (ι : Type) where
  labels : Array (LabelWalk ι)
  incoming : Array (List State)
  incomingImpl : Array (List (List (PromiseCalls.Implication ι)))
  incomingEdges : Array (List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
  edges : Array (EdgeWalk ι) := #[]
  visited : Nat := 0
  visits : Array VisitRecord := #[]

/-- The walk's state between two nodes: its record, and what it threads. -/
structure WalkState (ι : Type) [BEq ι] [Hashable ι] (G : NormalGraph ι) where
  walk : Walk ι
  answers : Answered G
  counts : Counts
  trace : Trace
  indeg : Array Nat
  fresh : Nat
  regionIn : Array (List RegionState)
  incomingFrom : Array (List Nat)
  queue : List Nat
  unsat : Array (Option Bool)
  lastStamp : Nat
  lastKind : String

/-- The outcomes a walk stops with: a refusal (with the entry and the given
facts an edge into it lacks, where it is that refusal), a refusal at a
footprint, a construct not handled, an observation. -/
inductive StopOutcome (ι : Type) where
  | refused (why : String) (lacks : Option (Nat × List HeapKnowledge.Candidate) := none)
      (detail : Option (Thunk (Option (RefusalDetail ι))) := none)
  | outsideBound (l : Nat)
  | notHandled (what : String)
  | observed (o : Observation ι)

/-- A stop's outcome as a verdict. -/
def StopOutcome.outcome : StopOutcome ι → Outcome ι
  | .refused why lacks pre => .refused why lacks pre
  | .outsideBound l => .outsideBound l
  | .notHandled what => .notHandled what
  | .observed o => .observed o

omit [DecidableEq ι] [Hashable ι] [Instantiates ι] in
/-- **A stopped walk is never accepted.** -/
theorem StopOutcome.outcome_ne_accepted (s : StopOutcome ι) : s.outcome ≠ .accepted := by
  cases s <;> simp [StopOutcome.outcome]

/-- Where a walk stopped: its outcome, counts, answers and trace. -/
structure WalkStop (ι : Type) [BEq ι] [Hashable ι] (G : NormalGraph ι) where
  outcome : StopOutcome ι
  counts : Counts
  answers : Answered G
  trace : Trace

/-- The walk on fuel: the queue's first node visited, then the rest; a fuel
that runs out before the queue does is a refusal. -/
def drive {G : NormalGraph ι} (visit : WalkState ι G → Nat → Except (WalkStop ι G) (WalkState ι G)) :
    Nat → WalkState ι G → Except (WalkStop ι G) (WalkState ι G)
  | 0, σ => match σ.queue with
    | [] => .ok σ
    | _ => .error (WalkStop.mk (.refused "the walk's fuel") σ.counts σ.answers σ.trace)
  | fuel + 1, σ => match σ.queue with
    | [] => .ok σ
    | l :: rest => match visit { σ with queue := rest } l with
      | .ok σ' => drive visit fuel σ'
      | .error stop => .error stop

/-- The verdict of a walk that ran out of queue, from its record: accepted
where it visited every node the start reaches. -/
def Walk.outcome (w : Walk ι) (reachable : Nat) : Outcome ι :=
  if w.visited < reachable then .notHandled s!"{reachable - w.visited} nodes not reached" else .accepted

/-- What every visit reads and none changes: the call's arguments and what
the setup computes from them (the nodes and claims, the loop heads
`isHead`, the nodes the start reaches, each head's given state, the merges,
the start's names). -/
structure WalkEnv (ι : Type) [DecidableEq ι] [Hashable ι] (G : NormalGraph ι) (images : InstanceImageCheck G) where
  pool : List (Ty ι)
  fuel : Nat
  suggestions : List (Sequent ι)
  index : KnownIndex ι
  codes : CodeEntry ι → Bool
  aliases : List (ι × ι)
  passChecker : PassChecker G images
  undefTy : Option (Ty ι)
  nodes : Array Node
  claimed : Array (PointClaim ι)
  n : Nat
  start : Nat
  goal : Goal ι
  «ensures» : List HeapKnowledge.IndexFact
  reference : Array Knowledge
  debugNode : Nat
  bound : Option RunBound
  givenImplies : Array (List (PromiseCalls.Implication ι))
  givenArgs : Array (List Nat)
  givenInputs : Array (List (Nat × Nat))
  observe : Option Nat
  tracing : Bool
  observeEntry : Bool
  regional : Option Regional
  isHead : Array Bool
  reached : Array Bool
  startEntered : Bool
  stated : Array (Option Knowledge)
  «given» : Array (Option Knowledge)
  merging : Array Bool
  deadArr : Array Bool
  startNames : List Nat
  argName : Option Nat
  /-- Whether each visit records its step's local effect (`Walk.visits`). -/
  grading : Bool
  /-- The framed nodes with the supports their returns keep (`framedAt`). -/
  framed : List (Nat × List Confinement.FrameSpec)
  /-- What each label's node or a later node reads (`liveSlots`). -/
  live : Array LiveSlots
  /-- The slots stated fresh at each loop head other than the start. -/
  givenFresh : Array (List Nat) := #[]

/-- The fresh slots a head other than the start states (always empty at the start). -/
def headFreshAt {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat) : List Nat :=
  if l == env.start then [] else (env.givenFresh[l]?).getD []

/-- Under a bound whose exceptional exit is `⊤`, the region from which
no normal return is possible (`GraphCode.inferDead`), refined from every
node; empty otherwise. -/
def deadRegion (G : NormalGraph ι) (nodes : Array Node) (claimed : Array (PointClaim ι))
    (bound : Option RunBound) : Array Bool :=
  match bound with
  | some (b, _) =>
    if b.exceptional == .top then
      let flags := (nodes.zip claimed).map fun (node, c) => (node, ExpressionEffects.emptyType G c.type)
      GraphCode.deadIterate flags (nodes.size + 1) (Array.replicate nodes.size true)
    else #[]
  | none => #[]

/-- **The in-degrees** the walk starts from: at each label below
`nodes.size` that is no loop head, the count of the edges into it
(continuations and handlers) from the nodes the start reaches. -/
def inDegrees (nodes : Array Node) (reached isHead : Array Bool) : Array Nat :=
  nodes.zipIdx.foldl (fun (indeg : Array Nat) (node, l) =>
    if reached[l]! then
      (successors node.continuation ++ node.handler.toList).foldl (fun (indeg : Array Nat) t =>
        if t.label < nodes.size && !isHead[t.label]! then indeg.modify t.label (· + 1) else indeg) indeg
    else indeg) (Array.replicate nodes.size 0)

/-- **A topological order** of the labels below `nodes.size` the start
reaches, over the edges into no loop head (continuations and handlers):
the order the walk's queue visits them in, from the in-degrees `indeg`
(`inDegrees`); none where some label is not ordered. -/
def topoOrder (nodes : Array Node) (reached isHead : Array Bool) (indeg : Array Nat) : Option (Array Nat) := Id.run do
  let n := nodes.size
  let mut indeg := indeg
  let mut queue : Array Nat := ((List.range n).filter fun l => reached[l]! && indeg[l]! == 0).toArray
  let mut order : Array Nat := #[]
  let mut i := 0
  for _ in [0:n] do
    if h : i < queue.size then
      let l := queue[i]
      i := i + 1
      order := order.push l
      for t in successors nodes[l]!.continuation ++ nodes[l]!.handler.toList do
        if t.label < n && !isHead[t.label]! then
          indeg := indeg.modify t.label (· - 1)
          if indeg[t.label]! == 0 then queue := queue.push t.label
  let count := (List.range n).countP fun l => reached[l]!
  return if order.size == count then some order else none

/-- **The slots an edge into a loop head reads** at the head's slots: those
its given invariant `req` states facts of, the tests and targets of its
given implications, and the slots its given state holds the promised input
or an input's entry value at (`headExit` checks these on the edge; the
head's state is its given state, over fresh names). -/
def headReads (req : Option Knowledge) (implies : List (PromiseCalls.Implication ι)) (args : List Nat)
    (inputs : List (Nat × Nat)) : List Nat :=
  ((req.map fun g => (atomsOf g).flatMap Atom.names).getD []) ++ implies.flatMap (fun y => [y.test, y.target]) ++
    args ++ inputs.map (·.1)

/-- **The slots each node reads or a later node reads** (liveness over the
walk's graph), at each label below `nodes.size` the start reaches, at the
slots of its claim's context: `none` where every slot counts as read.
A node reads the slots its term mentions (`mentioned`) and those its
written assertion `stated` states facts of (checked on the edges into it);
every slot at a node with a handler (its edge carries the entry's facts),
at a construction (a view's length may follow from facts its operands do
not reach), at a node whose term lists no reads, and everywhere under
spine regions (the regional check reads the entry's facts). Every node
reads the inputs' entry values `startNames`, whatever slot holds them: a
return checks the postcondition and the promise over them. Across each
exit a node reads the source slot the mapping reads for each slot its
target reads (into a loop head, `headReads`), each slot whose type the
edge changes (`differing`, checked over the source's facts), and the
result an edge observes; a pushed exit's slot `i + 1` is the entry's slot
`i`. The graph without the edges into loop heads is acyclic: one pass in
reverse topological order (`topoOrder`) computes it. -/
def liveSlots (nodes : Array Node) (claimed : Array (PointClaim ι)) (reached isHead : Array Bool)
    (indeg : Array Nat) (stated «given» : Array (Option Knowledge))
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (givenInputs : Array (List (Nat × Nat))) (regional : Bool) (startNames : List Nat) :
    Array LiveSlots := Id.run do
  let n := nodes.size
  let all : Array LiveSlots := Array.replicate n {}
  if regional then return all
  let some order := topoOrder nodes reached isHead indeg | return all
  let mut live : Array (Option (Std.HashSet Nat)) := Array.replicate n none
  for l in order.reverse do
    let node := nodes[l]!
    let c := claimed[l]!
    let construction := match node.expression with | .construct .. => true | _ => false
    let reads? : Option (List Nat) :=
      if node.handler.isSome || construction then none
      else (mentioned 0 node.expression).map fun ms =>
        ms ++ ((stated[l]!).map fun g => (atomsOf g).flatMap Atom.names).getD []
    let some reads := reads? | continue
    let mut acc : Option (Std.HashSet Nat) := some (reads.foldl (·.insert ·) {})
    for ex in Exit.ofNode node do
      let t := ex.target
      let target? : Option (List Nat) :=
        if t.label ≥ n then none
        else if isHead[t.label]! then
          some (headReads «given»[t.label]! ((givenImplies[t.label]?).getD []) ((givenArgs[t.label]?).getD [])
            ((givenInputs[t.label]?).getD []))
        else (live[t.label]!).map (·.toList)
      match acc, target?, claimed[t.label]? with
      | some a, some L, some tc =>
        let Γ := if ex.pushed then c.type :: c.context else c.context
        let exitSlots := L.map (PointClaims.slot t.mapping) ++ (differing Γ tc.context t.mapping).map (·.2) ++
          (if ex.observed.isSome then [0] else [])
        acc := some (exitSlots.foldl (fun (a : Std.HashSet Nat) s =>
          if ex.pushed then (if s ≥ 1 then a.insert (s - 1) else a) else a.insert s) a)
      | _, _, _ => acc := none
    live := live.set! l acc
  return live.map fun slots => { slots, keep := startNames }

/-- **The queue** the walk starts from: the labels below `n` the start
reaches, in order, of in-degree 0 that are loop heads or the start. -/
def initialQueue (n : Nat) (reached : Array Bool) (indeg : Array Nat) (isHead : Array Bool) (start : Nat) :
    List Nat :=
  (List.range n).filter fun l => reached[l]! && indeg[l]! == 0 && (isHead[l]! || l == start)

/-- The given invariant of each head below `n`, at its slots: its written
assertion and the claims' facts there (`supplied`); at the start the
request's entry facts, its index facts and the separation of its inputs
(`startWritten`, `startGiven`); and the counters after them. -/
def setupGiven (n start : Nat) (isHead : Array Bool) (stated : Array (Option Knowledge))
    (supplied : Array (Option (List HeapKnowledge.Candidate))) (entryIndices : List IndexAtom)
    (entrySeparation : HeapSeparation.Separation) (counts : Counts) : Array (Option Knowledge) × Counts :=
  (List.range n).foldl (fun (acc : Array (Option Knowledge) × Counts) l =>
    if isHead[l]! then
      let written : Knowledge := if l == start then startWritten stated[l]! entryIndices entrySeparation
        else (stated[l]!).getD {}
      let claimsFacts := (supplied[l]!).getD []
      let counts := { acc.2 with
        givenWritten := acc.2.givenWritten + (atomsOf written).length
        givenClaims := acc.2.givenClaims + claimsFacts.length }
      (acc.1.set! l (some (if l == start then startGiven stated[l]! entryIndices entrySeparation claimsFacts
        else HeapKnowledge.withCandidates written claimsFacts)), counts)
    else acc) (Array.replicate n none, counts)

/-- **The state the first visit starts from**, over `n` labels: the empty
record, the answers, counters and trace given, the in-degrees, the queue and
the fresh counter given, and per label no regional facts, no origin and no
satisfiability answer. -/
def setupState {G : NormalGraph ι} (n : Nat) (answers : Answered G) (counts : Counts) (trace : Trace)
    (indeg : Array Nat) (queue : List Nat) (fresh : Nat) : WalkState ι G :=
  { walk := { labels := Array.replicate n {}, incoming := Array.replicate n [], incomingImpl := Array.replicate n [],
              incomingEdges := Array.replicate n [] },
    answers, counts, trace, indeg, fresh, regionIn := Array.replicate n [], incomingFrom := Array.replicate n [],
    queue, unsat := Array.replicate n none, lastStamp := 0, lastKind := "" }

/-- **What every visit reads** (`WalkEnv`), from the call's arguments and
what the setup computes from them. -/
def setupEnv (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (suggestions : List (Sequent ι)) (index : KnownIndex ι) (codes : CodeEntry ι → Bool) (aliases : List (ι × ι))
    (passChecker : PassChecker G images) (undefTy : Option (Ty ι)) (nodes : Array Node)
    (claimed : Array (PointClaim ι)) (start : Nat) (goal : Goal ι) («ensures» : List HeapKnowledge.IndexFact)
    (reference : Array Knowledge) (debugNode : Nat) (bound : Option RunBound)
    (givenImplies : Array (List (PromiseCalls.Implication ι))) (givenArgs : Array (List Nat))
    (givenInputs : Array (List (Nat × Nat))) (observe : Option Nat) (tracing observeEntry : Bool)
    (regional : Option Regional) (isHead reached : Array Bool) (startEntered : Bool)
    (stated «given» : Array (Option Knowledge)) (merging deadArr : Array Bool) (startNames : List Nat)
    (argName : Option Nat) (grading : Bool) (framed : List (Nat × List Confinement.FrameSpec))
    (live : Array LiveSlots) (givenFresh : Array (List Nat) := #[]) : WalkEnv ι G images :=
  { pool, fuel, suggestions, index, codes, aliases, passChecker, undefTy, nodes, claimed, n := nodes.size, start,
    goal, ensures, reference, debugNode, bound, givenImplies, givenArgs, givenInputs, observe, tracing,
    observeEntry, regional, isHead, reached, startEntered, stated, given, merging, deadArr, startNames, argName,
    grading, framed, live, givenFresh }

/-- The walk's setup over one graph: its checks (the claims' count, the
loop heads' fuel, spine regions with an edge into the start, the entry's
fields under spine regions, one written assertion per label, the entry),
then what every visit reads (`setupEnv`) and the state the first visit
starts from (`setupState`), or where it stopped. -/
def setup (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge := #[]) (debugNode : Nat := 1000000000)
    (bound : Option RunBound := none)
    (givenImplies : Array (List (PromiseCalls.Implication ι)) := #[])
    (givenArgs : Array (List Nat) := #[])
    («ensures» : List HeapKnowledge.IndexFact := []) (givenInputs : Array (List (Nat × Nat)) := #[])
    (entrySeparation : HeapSeparation.Separation := {}) (observe : Option Nat := none) (tracing : Bool := false) (observeEntry : Bool := false)
    (regional : Option Regional := none) (grading : Bool := false)
    (framed : List (Nat × List Confinement.FrameSpec) := [])
    (givenFresh : Array (List Nat) := #[]) :
    Except (WalkStop ι G) (WalkEnv ι G images × WalkState ι G) :=
  let nodes := P.toArray
  let claimed := claims.toArray
  let n := nodes.size
  let edgeCount := nodes.foldl (fun acc node => acc + (successors node.continuation).length + node.handler.toList.length) 0
  let counts : Counts := { nodes := n, edges := edgeCount }
  let trace0 : Trace := {}
  if claimed.size != n then .error (WalkStop.mk (.notHandled "claim count") counts answers trace0) else
  -- Program syntax holds no location (`ObjectCoherence.sourceTerm`): its
  -- references are then valid in every world (`ControlFlow.program_source_refsOk`).
  if !(P.all fun node => ObjectCoherence.sourceTerm node.expression) then
    .error (WalkStop.mk (.refused "a node expression holding a location") counts answers trace0) else
  let index := KnownIndex.of known
  -- The type of `undefined` alone, among the pool's: a call's omitted
  -- receiver is read at it.
  let undefTy := pool.find? fun B => match PositiveRules.expand G B with
    | [PositiveNormalization.Clause.undef] => true
    | _ => false
  -- The loop heads (`loopHeads`), from the walk that marks them, refused
  -- where its fuel ends before its stack does. A statement entry that is no
  -- loop head is an ordinary node.
  let (ended, loopHeads, reached) := loopHeadsRun nodes start
  if !ended then .error (WalkStop.mk (.refused "the loop heads' fuel") counts answers trace0) else
  let _ := cuts
  let isHead : Array Bool := if start < n then loopHeads.set! start true else loopHeads
  -- Whether an edge enters the start: the start is then entered as any
  -- head, over fresh names, its given state checked on every edge into it;
  -- otherwise its names are the inputs' entry values (`headEntry`).
  let startEntered := nodes.any fun node =>
    (successors node.continuation ++ node.handler.toList).any (·.label == start)
  -- A regional check assumes the regions' input facts at the start, which
  -- no edge into it establishes.
  if startEntered && regional.isSome then
    .error (WalkStop.mk (.notHandled "spine regions with an edge into the start") counts answers trace0) else
  -- Under spine regions, the entry's fields the regions read
  -- (`ArgumentPathTracking.checkEntryFields`, as `goto_bounded` checks them).
  if (match regional with
      | some rg => !GraphCode.ArgumentPathTracking.checkEntryFields G inputs rg.regions
      | none => false) then
    .error (WalkStop.mk (.refused "spine regions: the entry's fields") counts answers trace0) else
  -- One written assertion per label (`byLabel` reads the first).
  if (assertions.map (·.1)).eraseDups.length != assertions.length then
    .error (WalkStop.mk (.refused "a label with two written assertions") counts answers trace0) else
  let stated := byLabel n assertions
  let trace : Trace := if tracing then
      let e : Array (Option State) := Array.replicate n none
      let ms : Array (List (Nat × State × Std.HashMap Nat (List Nat))) := Array.replicate n []
      let sg : Array (Option Nat) := Array.replicate n none
      Trace.mk e e ms sg isHead start 0 none [] [] []
    else trace0
  let supplied := byLabel n (withStartOld G inputs entryIndices entrySeparation start ensures candidates)
  -- The entry, which no edge checks on the first invocation.
  match entryRefusal G inputs claims start goal (stated.getD start none) ((supplied.getD start none).getD [])
      ((givenImplies[start]?).getD []) ((givenArgs[start]?).getD []) ((givenInputs[start]?).getD [])
      entryIndices entrySeparation with
  | some why => .error (WalkStop.mk (.refused why) counts answers trace)
  | none =>
    -- In-degrees without the edges into heads, of the edges from nodes the
    -- start reaches: a node no path from the start reaches never runs.
    let indeg := inDegrees nodes reached isHead
    let merging : Array Bool := indeg.map (· > 1)
    let deadArr := deadRegion G nodes claimed bound
    let (given, counts) := setupGiven n start isHead stated supplied entryIndices entrySeparation counts
    let queue := initialQueue n reached indeg isHead start
    -- The start's names, fixed before any node is visited (a cut may be
    -- visited before it), and the name of the input a promise goal is about.
    let startWidth := ((claimed[start]?).map (·.context.length)).getD 0
    let startNames := List.range startWidth
    let argName : Option Nat := goal.slot.bind fun sl => startNames[sl]?
    .ok (setupEnv G images pool fuel suggestions index codes aliases passChecker undefTy nodes claimed start goal
        ensures reference debugNode bound givenImplies givenArgs givenInputs observe tracing observeEntry regional
        isHead reached startEntered stated given merging deadArr startNames argName grading framed
        (liveSlots nodes claimed reached isHead indeg stated given givenImplies givenArgs givenInputs regional.isSome
          startNames) givenFresh,
      setupState n answers counts trace indeg queue startWidth)

/-- A node's output facts as an edge reads them: the step's output `out`
with its links restated on every slot of their classes at the node's
context with its result. -/
def outAllOf (G : NormalGraph ι) (c : PointClaim ι) (out : Knowledge) : Knowledge :=
  KnowledgeExpand.expandLinks (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G c.context) 1) out

/-- **An exit's context as the step's yields refine it** (`produceNodeAt`),
at the node's claim `c` and continuation `k`, the yields `ysAll` (each at
every slot holding its target's name), the output facts `out`
(`outAllOf`) and whether the exit is the continuation's first (`first`, a
two-way dispatch's true arm): a pushed result's context refined by the
unconditional yields, a branch's arm by its arm's. -/
def refinedContext (G : NormalGraph ι) (c : PointClaim ι) (k : Continuation) (ysAll : List (PromiseCalls.Yield ι))
    (out : Knowledge) (first : Bool) : List (Ty ι) :=
  let pushedRefine := fun facts => PromiseCalls.refineBy G (c.type :: c.context)
    (PromiseCalls.aliasFacts out.links facts 1) 0
  let keptRefine := fun facts => PromiseCalls.refineBy G c.context
    (PromiseCalls.aliasFacts (HeapKnowledge.dropResult out).links facts 0) 0
  let unconditional := PromiseCalls.yieldFacts ysAll false
  let conditional := PromiseCalls.yieldFacts ysAll true
  match k with
  | .bind _ => pushedRefine unconditional
  | .effect _ => keptRefine unconditional
  | .branch .. => keptRefine (if first then conditional else unconditional)
  | .branchBind .. => pushedRefine (if first then conditional else PromiseCalls.yieldFacts ysAll false true)
  | .tagBind tg .. => pushedRefine (if first then PromiseCalls.yieldFacts ysAll (ControlFlow.truthyBoolean G tg c.type)
      else unconditional)
  | .ret => c.context

/-- A node's entry before a written assertion's facts join it: the state
given at a head, its one predecessor's, or the meet of its predecessors'
(`base`); its implications; the fresh counter after it; at a merge its
context and the fresh counter it started from, and the merge's result. -/
structure EntryStart (ι : Type) where
  base : State
  implies : List (PromiseCalls.Implication ι)
  fresh : Nat
  merge : Option (List (Ty ι) × Nat)
  merged : Option (Merged ι)

/-- **A node's entry** from the walk's state `σ`: at a head its given state
(`headEntry`), else its one predecessor's state, or the meet of its
predecessors' (`mergeState`). -/
def entryStart (G : NormalGraph ι) {images : InstanceImageCheck G} (env : WalkEnv ι G images) (σ : WalkState ι G)
    (l : Nat) : EntryStart ι :=
  let c := env.claimed[l]!
  let width := c.context.length
  match env.given[l]! with
  | some g =>
    let (st, imp, fr) := headEntry g (l == env.start && !env.startEntered) width σ.fresh env.startNames env.argName
      ((env.givenArgs[l]?).getD []) ((env.givenInputs[l]?).getD []) ((env.givenImplies[l]?).getD []) (headFreshAt env l)
    { base := st, implies := imp, fresh := fr, merge := none, merged := none }
  | none => match σ.walk.incoming[l]! with
    | [s] => { base := s, implies := (σ.walk.incomingImpl[l]!).headD [], fresh := σ.fresh, merge := none, merged := none }
    | [] => { base := { names := [] }, implies := [], fresh := σ.fresh, merge := none, merged := none }
    | s :: rest =>
      let mg := mergeState G c.context (s :: rest) σ.walk.incomingEdges[l]! σ.fresh
      { base := mg.state, implies := mg.implies, fresh := mg.fresh, merge := some (c.context, σ.fresh), merged := some mg }

/-- A written assertion, established on every edge into a node other than
a head, holds there: its facts join the state `entry` at `l`. -/
def withStated {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat) (entry : State) : State :=
  if !env.isHead[l]! then
    match env.stated[l]! with
    | some req =>
      let f := fun (i : Nat) => entry.names[i]?
      { entry with store := (atomsOf req).foldl (fun s a => match a.rename f with
        | some b => s.add b | none => s) entry.store }
    | none => entry
  else entry

/-- The counters after a node's entry `es`. -/
def entryCounts {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (counts : Counts) (l : Nat)
    (es : EntryStart ι) : Counts :=
  let counts := match env.given[l]! with
    | some _ => { counts with givenImplies := counts.givenImplies + es.implies.length }
    | none => match es.merged with
      | some mg => { counts with merges := counts.merges + 1, mergeDiffs := counts.mergeDiffs + mg.diffCount }
      | none => counts
  { counts with
    visited := counts.visited + 1, storeMax := max counts.storeMax es.base.store.size
    stateSum := counts.stateSum + es.base.store.size, heads := counts.heads + (if env.isHead[l]! then 1 else 0) }

/-- The trace after a node's entry `es`, where tracing. -/
def entryTrace {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (σ : WalkState ι G) (l : Nat)
    (es : EntryStart ι) : Trace :=
  if env.tracing then
    let trace := σ.trace
    let trace := match env.given[l]! with
      | some _ => trace
      | none => match σ.walk.incoming[l]! with
        | [_] => { trace with single := trace.single.set! l (σ.incomingFrom[l]!).head? }
        | _ => match es.merged with
          | some mg => { trace with merges := trace.merges.set! l ((σ.incomingFrom[l]!).zip (mg.views.zip mg.renames)) }
          | none => trace
    let node := env.nodes[l]!
    let focus := ((mentioned 0 node.expression).getD []).filterMap (es.base.names[·]?)
    { trace with entries := trace.entries.set! l (some es.base), node := l, edge := none, names := es.fresh :: es.base.names, focus }
  else σ.trace

/-- At a merge observed, each predecessor's state at the merge's slots and
the names. -/
def entryPreds {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (σ : WalkState ι G) (l : Nat)
    (es : EntryStart ι) : List (Nat × Knowledge) × List (List Nat) :=
  match es.merged with
  | some mg =>
    if env.observe == some l then
      let width := (env.claimed[l]!).context.length
      ((σ.incomingFrom[l]!).zip (mg.views.map fun ps => (materialize ps width (List.range width) true).1),
        mg.state.names :: (σ.walk.incoming[l]!).map (·.names))
    else ([], [])
  | none => ([], [])

/-- Debugging: the facts a reference certificate holds at `l` that the
state `entry` does not entail. -/
def referenceRefusal (G : NormalGraph ι) {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat)
    (entry : State) : Option String :=
  match env.reference[l]? with
  | some old =>
    if !env.isHead[l]! then
      let c := env.claimed[l]!
      let width := c.context.length
      let (k, _, _) := materialize entry width (List.range width) true
      let ctx := KnowledgeExpand.ctxOf G c.context
      let missingCells := old.cells.filter fun f => !KnowledgeExpand.checkIn ctx k { cells := [f] } none
      if !missingCells.isEmpty then some s!"reference: node {l} lacks cells {reprStr missingCells}"
      else
        let missing := old.indices.filter fun a => !KnowledgeExpand.checkIn ctx k { indices := [a] } none
        if !missing.isEmpty then some s!"reference: node {l} lacks {reprStr missing}" else none
    else none
  | none => none

/-- What a node's entry gives its step and its exits: the walk's counters,
trace, fresh counter and timer after it, whether no environment meets the
node's context, the entry state and implications (`entryOf`), at a merge
observed each predecessor's state and names, at a merge its context and the
fresh counter it started from. -/
structure Entered (ι : Type) where
  counts : Counts
  trace : Trace
  fresh : Nat
  lastStamp : Nat
  here : Bool
  entry : State
  implies : List (PromiseCalls.Implication ι)
  predViews : List (Nat × Knowledge)
  predNames : List (List Nat)
  merge : Option (List (Ty ι) × Nat)

/-- A node's entry (`visit`'s first part): `entryStart` and `withStated`;
the stop where a reference certificate's facts are missing or an
observation of its entry is asked. -/
def visitEntry (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (σ : WalkState ι G)
    (l : Nat) : Except (WalkStop ι G) (Entered ι) :=
  -- Measuring: the previous node's time, with its edges, by its kind.
  let lastStamp := clock σ.lastKind σ.lastStamp l
  let c := env.claimed[l]!
  let width := c.context.length
  -- Whether no environment meets the node's context.
  let here := match σ.unsat[l]! with
    | some u => u
    | none => ControlFlow.unsatisfiable G c.context
  let es := entryStart G env σ l
  let counts := entryCounts env σ.counts l es
  let trace := entryTrace env σ l es
  let (predViews, predNames) := entryPreds env σ l es
  match referenceRefusal G env l es.base with
  | some why => .error (WalkStop.mk (.refused why) counts σ.answers trace)
  | none =>
    let entry := withStated env l es.base
    -- Observing a node whose step is refused: its state on entry alone.
    if env.observeEntry && env.observe == some l then
      let before := (materialize entry width (List.range width) true).1
      let o : Observation ι := { label := l, before, after := before, preds := predViews, names := predNames, implies := slotImplOf entry.names es.implies }
      .error (WalkStop.mk (.observed o) counts σ.answers trace)
    else
      .ok { counts, trace, fresh := es.fresh, lastStamp, here, entry, implies := es.implies, predViews, predNames,
            merge := es.merge }

/-- The counters with a step's statistics added. -/
def addStats (counts : Counts) (stats : StepStats) : Counts :=
  { counts with
    rules := counts.rules + stats.rules, fullRules := counts.fullRules + stats.fullRules
    directCalls := counts.directCalls + stats.directCalls, copies := counts.copies + stats.copies }

/-- **A node's checked step** from its entry state `entry`, the fresh
counter `fresh` and the answers `answers`: the node's shape
(`passShapeCheck'`), the slots its expression reads, `checkedStep`; the
slots, the step, its statistics and the answers after it, or where it
stopped (at the counters `counts` and the trace `trace`). -/
def stepRun (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (l : Nat)
    (entry : State) (fresh : Nat) (answers : Answered G) (counts : Counts) (trace : Trace) :
    Except (WalkStop ι G) (List Nat × Stepped ι × StepStats × Answered G) :=
  let node := env.nodes[l]!
  let c := env.claimed[l]!
  if !passShapeCheck' G c.type node.continuation then
    .error (WalkStop.mk (.refused s!"the shape of node {l}") counts answers trace)
  else match timedKind "node mentioned" fun _ => mentioned 0 node.expression with
  | none => .error (WalkStop.mk (.notHandled s!"term at node {l}: {(reprStr node.expression).take 200}") counts answers trace)
  | some ms =>
    let ms := (keepFirst {} ms).2.toList
    let (stepped, stats, a) := checkedStep G images env.pool env.fuel env.suggestions env.index env.codes env.aliases
      env.passChecker env.undefTy l node c entry ms fresh answers
    match stepped with
    | .ok st => .ok (ms, st, stats, a)
    -- A step with no derivation: its preconditions, computed only where
    -- the refusal is printed (`stepPreconditionsAt`).
    | .error why => .error (WalkStop.mk (.refused why none
        (if stats.underivable then some (Thunk.mk fun _ => (stepPreconditionsAt G c node entry ms).map .step) else none))
        (addStats counts stats) a trace)

/-- The step's derivation as the checks after it read it: the step's, else
a variable read at the node's sequent. -/
def derivOf (c : PointClaim ι) (node : Node) (st : Stepped ι) : ProgramCertificates.Evidence ι :=
  st.stepDeriv.getD (.node ⟨c.context, node.expression, c.type⟩ .var [])

/-- The fresh receiver slots of the step: the receiver's slot where it holds
a fresh name. -/
def recvFresh (node : Node) (entry : State) : List Nat :=
  match PromiseCalls.receiverSlot node.expression with
  | some i => if (entry.names[i]?).any entry.fresh.contains then [i] else []
  | none => []

/-- The evidence `GraphCode.deadNode` reads at a node of the no-return
region. -/
def deadEvidence (c : PointClaim ι) (node : Node) : NodeEvidence ι :=
  ⟨none, some ⟨c.context, node.expression, c.type⟩, [], {}, none, {}, none, [], [], [], none⟩

/-- Whether the step's result holds a fresh spine: a copy of a fresh slot,
or a call at a selected signature stating a fresh result
(`GraphCode.varFresh`, `callFresh`) whose derivation `stepDerivChecked`
accepts at the step's facts `stepK`. -/
def outFreshOf (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (c : PointClaim ι) (node : Node) (entry : State)
    (stepK : Knowledge) (deriv : ProgramCertificates.Evidence ι) : Bool :=
  (match node.expression with
    | .var i => (entry.names[i]?).any entry.fresh.contains
    | _ => false) ||
    GraphCode.ArgumentRegionGraph.allocSpine node.expression ||
    ((match ExpressionEffects.selectedEffect deriv with | some eff => eff.schema.normal.freshResult | none => false) &&
      ExpressionEffects.selectedOperands deriv &&
      stepDerivChecked G images codes sums c node stepK deriv)

/-- **The footprint check at a node** (`GraphCode.nodeChecked`): under no
bound, it passes; under the bound $`(\Phi, \Psi, \mathit{ret})`$, at a
label of the no-return region `deadArr` it is `deadNode` with the
exceptional bound $`\Psi = \top`$, elsewhere `footprintCheck` at the fresh receiver slots, the live
handler and the result's freshness (`outFreshOf`), over the read summaries
`sums` after the step, its facts `stepK` and its derivation `deriv`. -/
def boundOk (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (bound : Option RunBound) (deadArr : Array Bool) (l : Nat) (node : Node)
    (c : PointClaim ι) (entry : State) (sums : List (ReadSummary ι)) (stepK : Knowledge)
    (deriv : ProgramCertificates.Evidence ι) : Bool :=
  match bound with
  | none => true
  | some (⟨Φ, Ψ⟩, ret) =>
    if deadArr.getD l false then
      GraphCode.deadNode G deadArr.toList node (deadEvidence c node) && Ψ == .top
    else
      footprintCheck G images codes sums Φ Ψ (recvFresh node entry) c node stepK deriv
        (match node.handler with
          | some t => !deadArr.getD t.label false
          | none => false) ret
        (outFreshOf G images codes sums c node entry stepK deriv)

/-- Input indices `q` whose entry value (`startNames[q]`) is aliased by the
returned value `result` in `store` at a return node (`node.continuation == .ret`),
using the same materialization and alias closure as `returnCheck`. -/
def returnAliasesAt (G : NormalGraph ι) (c : PointClaim ι) (node : Node)
    (entry : State) (store : Store) (result : Nat) (startNames : List Nat) : List Nat :=
  if node.continuation != .ret then []
  else if ExpressionEffects.emptyType G c.type || c.context.any (ExpressionEffects.emptyType G ·) then []
  else
    let width := c.context.length
    let tracked : List (Nat × Nat) := startNames.zipIdx.filterMap fun (nm, q) =>
      (entry.names.idxOf? nm).map (·, q)
    if tracked.isEmpty then [] else
    let (k, _, _) := materialize { names := result :: entry.names, store } (width + 1) (0 :: tracked.map (·.1 + 1)) false
    let al := HeapLinks.aliases k.links 0
    tracked.filterMap fun (j, q) => if al.contains (j + 1) then some q else none

/-- **A visit's record** at label `l`: its step's local certificate
(`stepCertificate`) at the fresh slots, over the read summaries `sums` the
step left, its facts `stepK` and its derivation `deriv`, the grades it
projects to, its result's freshness `outFresh`, and any input indices the
returned value aliases at a return node (`returnAliases`). -/
def VisitRecord.of (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (l : Nat) (node : Node) (c : PointClaim ι) (entry : State) (sums : List (ReadSummary ι)) (stepK : Knowledge)
    (deriv : ProgramCertificates.Evidence ι) (outFresh : Bool) (returnAliases : List Nat := []) : VisitRecord :=
  let q := stepCertificate G images codes sums (recvFresh node entry) c node stepK deriv
  { label := l, certificate := q, grades := q.grades, outFresh, returnAliases }

omit [Hashable ι] [Instantiates ι] in
/-- **A record's grades are its certificate's projection**, the grades the
step's rules grant (proved, `stepCertificate_grades`). -/
theorem VisitRecord.of_grades (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (l : Nat) (node : Node) (c : PointClaim ι) (entry : State) (sums : List (ReadSummary ι)) (stepK : Knowledge)
    (deriv : ProgramCertificates.Evidence ι) (outFresh : Bool) (returnAliases : List Nat := []) :
    (VisitRecord.of G images codes l node c entry sums stepK deriv outFresh returnAliases).grades =
        (VisitRecord.of G images codes l node c entry sums stepK deriv outFresh returnAliases).certificate.grades ∧
      (VisitRecord.of G images codes l node c entry sums stepK deriv outFresh returnAliases).grades =
        stepGrades G images codes sums (recvFresh node entry) c node stepK deriv :=
  ⟨rfl, stepCertificate_grades ..⟩

/-- **The footprint check read off a visit's record**, at its node `node`
and claim `c`, the bound $`(\Phi, \Psi, \mathit{ret})`$ and the
no-return region `deadArr`: at a label of the region `deadNode` with the
exceptional bound $`\Psi = \top`$, elsewhere the record's grades within the bound (`StepGrades.admits`)
at the live handler, the bound's throw and return conditions and the
record's freshness. -/
def VisitRecord.admitsAt (G : NormalGraph ι) (node : Node) (c : PointClaim ι)
    (B : RunBound) (deadArr : Array Bool) (r : VisitRecord) : Bool :=
  if deadArr.getD r.label false then
    GraphCode.deadNode G deadArr.toList node (deadEvidence c node) && B.1.exceptional == .top
  else
    r.grades.admits B.1.normal B.1.exceptional
      (match node.handler with
        | some t => !deadArr.getD t.label false
        | none => false) B.2 r.outFresh node.continuation

/-- `VisitRecord.admitsAt` at the record's node and claim in the graph's
nodes and claims. -/
def VisitRecord.admits (G : NormalGraph ι) (nodes : Array Node) (claimed : Array (PointClaim ι))
    (B : RunBound) (deadArr : Array Bool) (r : VisitRecord) : Bool :=
  r.admitsAt G nodes[r.label]! claimed[r.label]! B deadArr

/-- **The footprint checks read off a walk's records** (`VisitRecord.admits`
of every visit's record): the check that the bound `B` with its no-return
region `deadArr` admits every visit the records witness. -/
def recordsAdmit (G : NormalGraph ι) (nodes : Array Node) (claimed : Array (PointClaim ι))
    (B : RunBound) (deadArr : Array Bool) (visits : Array VisitRecord) : Bool :=
  visits.all (·.admits G nodes claimed B deadArr)

omit [Hashable ι] [Instantiates ι] in
/-- **The footprint check at a bound is its record's check** (proved): the
check `boundOk` makes at a visit of `l` under the bound `B` is
`VisitRecord.admits` of the record of that visit (`VisitRecord.of`, over the
same read summaries, at the freshness `outFreshOf` computes over them;
`footprintCheck_eq_admits`). -/
theorem boundOk_eq_admits (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (B : RunBound) (deadArr : Array Bool) (l : Nat) (node : Node) (c : PointClaim ι)
    (entry : State) (sums : List (ReadSummary ι)) (stepK : Knowledge) (deriv : ProgramCertificates.Evidence ι)
    (returnAliases : List Nat) :
    boundOk G images codes (some B) deadArr l node c entry sums stepK deriv =
      (VisitRecord.of G images codes l node c entry sums stepK deriv
        (outFreshOf G images codes sums c node entry stepK deriv) returnAliases).admitsAt G node c B deadArr := by
  obtain ⟨⟨Φ, Ψ⟩, ret⟩ := B
  simp only [boundOk, VisitRecord.admitsAt, (VisitRecord.of_grades (returnAliases := returnAliases) ..).2, footprintCheck_eq_admits]
  rfl

/-- A step's yields checked (`checkedYields`) at the node's claim, the
step's facts and derivation, the promise branch's derivation checked over
the read summaries of `answers`. -/
def checkYsAt (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (answers : Answered G) (c : PointClaim ι) (node : Node) (st : Stepped ι)
    (xs : List (PromiseCalls.Implication ι)) (ys : List (PromiseCalls.Yield ι)) : List (PromiseCalls.Yield ι) :=
  let deriv := derivOf c node st
  timedKind "yields checked" fun _ =>
    checkedYields G images c.context c.type xs st.stepK st.stepOut deriv node.expression
      (fun _ => promiseDerivChecked G images codes answers.summaries.toList c node st.stepK deriv) ys

/-- A read of a slot yields what the implications testing its name state,
at every slot holding a target's name, checked against the implications
testing the slot's name; none where no implication tests it. -/
def readYields (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (l : Nat)
    (entry : State) (implies : List (PromiseCalls.Implication ι)) (st : Stepped ι) (answers : Answered G) :
    Option (List (PromiseCalls.Yield ι)) :=
  let node := env.nodes[l]!
  let c := env.claimed[l]!
  match node.expression with
  | .var i => match entry.names[i]? with
    | some x =>
      let tested := implies.filter (·.test == x)
      if tested.isEmpty then none
      else
        let held := (entry.names.zipIdx).filter fun (nm, _) => tested.any (·.target == nm)
        some (checkYsAt G images env.codes answers c node st (slotImplOf entry.names tested)
          (tested.flatMap fun y => (held.filter (·.1 == y.target)).map fun (_, t) =>
            ({ conditional := true, target := t, type := y.type } : PromiseCalls.Yield ι)))
    | none => none
  | _ => none

/-- **The step's yields**, where an edge's types need them: a read's
(`readYields`), else another step's (a test's, a promise call's), computed
for the implications its pushed result carries (`nodeYields`), checked
(`checkYsAt` at the answers `answers`); and the answers after them. -/
def stepYields (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (l : Nat)
    (entry : State) (implies : List (PromiseCalls.Implication ι)) (st : Stepped ι) (answers : Answered G) :
    Option (List (PromiseCalls.Yield ι)) × Answered G :=
  match readYields G images env l entry implies st answers with
  | some ys => (some ys, answers)
  | none =>
    let node := env.nodes[l]!
    let c := env.claimed[l]!
    let isRead := match node.expression with | .var _ => true | _ => false
    if !isRead && !st.copied then
      let slotImpl := slotImplOf entry.names implies
      let (ys, a) := timedKind "yields" fun _ =>
        (nodeYields G images env.pool c.context slotImpl (derivOf c node st) st.stepOut st.stepK) answers
      (some (checkYsAt G images env.codes answers c node st slotImpl ys), keepSummaries answers a)
    else (none, answers)

/-- A handler receives the thrown value in a fresh name, at a type
admitting every value its target states for the slot it lands in, or the
pool's (`produceNodeAt`), under the facts a throw keeps
(`ControlFlow.handlerFacts`: no heap fact). -/
def thrownTyOf {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (node : Node) : Option (Ty ι) :=
  node.handler.bind fun t => do
    let tc ← env.claimed[t.label]?
    let landing := (List.range tc.context.length).filterMap fun i =>
      if PointClaims.slot t.mapping i == 0 then tc.context[i]? else none
    (landing ++ env.pool).find? (ControlFlow.admitsAll G)

/-- **A return's postcondition facts** (`ReturnFacts`) at node `l` (its
claim `c`) returning `result` from `entry` with the output store `store`:
the facts `returnCheck` reads (the output's facts over the result and the
slots holding the inputs' entry values), each fact of the postcondition
`ensures` at the return's pushed slots, decided alone by
`GraphCode.returnEntails`, and those facts, an input's entry value read at
the slot holding it. Read only where the refusal is printed. -/
def returnFactsAt (G : NormalGraph ι) («ensures» : List HeapKnowledge.IndexFact) (c : PointClaim ι) (entry : State)
    (store : Store) (result : Nat) (startNames : List Nat) : ReturnFacts :=
  let width := c.context.length
  let tracked : GraphCode.Tracked := (GraphCode.namedInputs ensures).filterMap fun (_, q) => do
    let nm ← startNames[q]?
    let j ← entry.names.idxOf? nm
    pure (j, q)
  let (k, _, _) := materialize { names := result :: entry.names, store } (width + 1) (0 :: tracked.map (·.1 + 1)) false
  let kOut := KnowledgeExpand.expandLinks (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G c.context) 1) k
  -- An input's entry value at the slot holding it (`old(x)`, input `q` at
  -- the return's slot `trackedSlot (q + 1)`).
  let entryAt := fun (q : Nat) => if tracked.any (·.2 == q) then some (GraphCode.trackedSlot tracked (q + 1)) else none
  { facts := ensures.map fun F =>
      ((if GraphCode.namesTracked tracked [F] then (F.mapM fun j => some (GraphCode.trackedSlot tracked j)).bind
          (·.mapEntry entryAt) else none),
       GraphCode.returnEntails kOut tracked [F]),
    known := { kOut with indices := kOut.indices.filterMap fun a => (a.fact.mapEntry entryAt).map ({ a with fact := · }) } }

/-- The return check at a return node (`returnCheck`, at the step's store
and result and the yields `yields`, from the answers `answers`); none at
another node. -/
def returnRun (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (l : Nat)
    (entry : State) (st : Stepped ι) (yields : List (PromiseCalls.Yield ι)) (answers : Answered G) :
    Option (Option String × Answered G × Option Nat) :=
  match (env.nodes[l]!).continuation with
  | .ret =>
    let (refusal, a, queried) := returnCheck G images env.goal env.ensures env.claimed[l]! l entry st.store st.result
      env.start env.startNames env.argName yields env.debugNode answers
    some (refusal, keepSummaries answers a, queried)
  | _ => none

/-- **Whether the return check passes** at `l` (`returnRun`): its refusal
none at a return, true at another node. -/
def returnOk (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (l : Nat)
    (entry : State) (st : Stepped ι) (yields : List (PromiseCalls.Yield ι)) (answers : Answered G) : Bool :=
  match returnRun G images env l entry st yields answers with
  | some (refusal, _, _) => refusal.isNone
  | none => true

/-- **A visit's footprint check and its record**, at label `l` from the
entry `entry`, over the read summaries `sums` the step left, its facts
`stepK`, its derivation `deriv` and its freshness `outFresh`. Under
`grading` the step's grades are computed once (`VisitRecord.of`) and that
one record both decides the check at the walk's bound
(`VisitRecord.admitsAt`; none passes) and is recorded; otherwise the check
is `boundOk` and nothing is recorded (`stepCheck_fst`: the check is
`boundOk` either way). -/
def stepCheck (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (l : Nat)
    (entry : State) (sums : List (ReadSummary ι)) (stepK : Knowledge) (deriv : ProgramCertificates.Evidence ι)
    (outFresh : Bool) (retAliases : Unit → List Nat) : Bool × Option VisitRecord :=
  if env.grading then
    let r := VisitRecord.of G images env.codes l env.nodes[l]! env.claimed[l]! entry sums stepK deriv outFresh (retAliases ())
    (match env.bound with
      | none => true
      | some B => r.admitsAt G env.nodes[l]! env.claimed[l]! B env.deadArr, some r)
  else (boundOk G images env.codes env.bound env.deadArr l env.nodes[l]! env.claimed[l]! entry sums stepK deriv, none)

omit [Instantiates ι] in
/-- **The check a visit makes is `boundOk`, grading or not** (proved, by
`boundOk_eq_admits`), where the freshness given is the step's. -/
theorem stepCheck_fst (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (l : Nat)
    (entry : State) (sums : List (ReadSummary ι)) (stepK : Knowledge) (deriv : ProgramCertificates.Evidence ι)
    (retAliases : Unit → List Nat) :
    (stepCheck G images env l entry sums stepK deriv
        (outFreshOf G images env.codes sums env.claimed[l]! env.nodes[l]! entry stepK deriv) retAliases).1 =
      boundOk G images env.codes env.bound env.deadArr l env.nodes[l]! env.claimed[l]! entry sums stepK deriv := by
  unfold stepCheck
  split
  · cases hb : env.bound with
    | none => rfl
    | some B => exact (boundOk_eq_admits G images env.codes B env.deadArr l env.nodes[l]! env.claimed[l]! entry sums stepK deriv (retAliases ())).symm
  · rfl

/-- What a node's step gives its exits and its record: the answers it
started from (`stepAnswers`), those after `checkedStep` (`steppedAnswers`,
which the footprint check reads), those the return check started from
(`yieldAnswers`) and those after the step (`answers`); the counters, trace,
fresh counter and timer kind after it; the slots it read, its result,
whether its result holds a fresh spine, whether its footprint and return
checks passed, its yields where computed, the handler's thrown value's type
and name, and under `grading` the visit's record (`stepCheck`). -/
structure StepDone (ι : Type) [BEq ι] [Hashable ι] (G : NormalGraph ι) where
  stepAnswers : Answered G
  steppedAnswers : Answered G
  yieldAnswers : Answered G
  answers : Answered G
  counts : Counts
  trace : Trace
  fresh : Nat
  lastKind : String
  ms : List Nat
  st : Stepped ι
  outFresh : Bool
  bounded : Bool
  returned : Bool
  yields : Option (List (PromiseCalls.Yield ι))
  thrownTy : Option (Ty ι)
  thrown : Nat
  record : Option VisitRecord

/-- A node's step (`visit`'s second part), from the walk's state `σ` and the
node's entry `en`: the checked step (`stepRun`), an observation of it, its
result's freshness (`outFreshOf`), its footprint check (`boundOk`), its
yields (`stepYields`), a handler's thrown value, its return check
(`returnRun`). -/
def visitStep (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (σ : WalkState ι G)
    (l : Nat) (en : Entered ι) : Except (WalkStop ι G) (StepDone ι G) :=
  match stepRun G images env l en.entry en.fresh σ.answers en.counts en.trace with
  | .error stop => .error stop
  | .ok (ms, st, stats, a) =>
    let node := env.nodes[l]!
    let c := env.claimed[l]!
    let width := c.context.length
    let entry := en.entry
    let counts := addStats en.counts stats
    let lastKind := if (env.given[l]!).isSome then "node: head" else if (σ.walk.incoming[l]!).length > 1 then "node: merge"
      else if st.copied then "node: copy" else "node: step"
    let pushedNames := st.result :: entry.names
    let trace := if env.tracing then
        let s : State := { entry with names := pushedNames, store := st.store }
        { en.trace with afters := en.trace.afters.set! l (some s), names := pushedNames, focus := st.result :: en.trace.focus }
      else en.trace
    if env.observe == some l then
      let before := (materialize entry width (List.range width) true).1
      let after := (materialize { entry with names := pushedNames, store := st.store } (width + 1) (List.range (width + 1)) true).1
      let o : Observation ι := { label := l, before, after, preds := en.predViews, names := en.predNames, implies := slotImplOf entry.names en.implies }
      .error (WalkStop.mk (.observed o) counts a trace)
    else
      let deriv := derivOf c node st
      let sums := a.summaries.toList
      let outFresh := outFreshOf G images env.codes sums c node entry st.stepK deriv
      let checked := stepCheck G images env l entry sums st.stepK deriv outFresh
        (fun _ => returnAliasesAt G c node entry st.store st.result env.startNames)
      let bounded := checked.1
      let record := checked.2
      if !bounded then .error (WalkStop.mk (.outsideBound l) counts a trace)
      else
        let (yields, a1) := stepYields G images env l entry en.implies st a
        let thrownTy := thrownTyOf env node
        if node.handler.isSome && thrownTy.isNone then
          .error (WalkStop.mk (.refused s!"handler of node {l}") counts a1 trace)
        else
          let thrown := st.fresh
          let fresh := if node.handler.isSome then st.fresh + 1 else st.fresh
          match returnRun G images env l entry st (yields.getD []) a1 with
          | none =>
            .ok { stepAnswers := σ.answers, steppedAnswers := a, yieldAnswers := a1, answers := a1, counts, trace,
                  fresh, lastKind, ms, st, outFresh, bounded, returned := true, yields, thrownTy, thrown,
                  record }
          | some (refusal, a2, queried) =>
            let counts := match queried with
              | some q => { counts with queries := counts.queries + 1, queryAtoms := counts.queryAtoms + q }
              | none => counts
            match refusal with
            | some why => .error (WalkStop.mk (.refused why none (if env.ensures.isEmpty then none else
                some (Thunk.mk fun _ => some (.postcondition (returnFactsAt G env.ensures env.claimed[l]! entry st.store
                  st.result env.startNames)))))
                counts a2 trace)
            | none =>
              .ok { stepAnswers := σ.answers, steppedAnswers := a, yieldAnswers := a1, answers := a2, counts, trace,
                    fresh, lastKind, ms, st, outFresh, bounded, returned := true, yields, thrownTy, thrown,
                    record }

/-- How an exit's types were established: its context met by no
environment (`vacuous`); every differing slot's type below the target's
(`subtypes`); the edge search over the edge's facts `ko` (`edge`); at the
context `Γ'` the step's yields `ys` refine (`refinedContext`) over the
node's output facts `out` (`refined`); at the mixed context `Γm` over `out`
(`mixed`). -/
inductive ExitTyped (ι : Type) where
  | vacuous
  | subtypes
  | edge (ko : Knowledge)
  | refined (Γ' : List (Ty ι)) (out : Knowledge) (ys : List (PromiseCalls.Yield ι))
  | mixed (Γm : List (Ty ι)) (out : Knowledge)

/-- One exit as the exits' fold took it: its position and target, its
context, names and edge facts, how its types were established, whether it
enters a head, the context `Γe` its target's assertion or merge read (where
read), and the state and implications it carried into a node other than a
head. -/
structure ExitRecord (ι : Type) where
  index : Nat
  target : Target
  Γ : List (Ty ι)
  names : List Nat
  edgeStore : Store
  typed : ExitTyped ι
  head : Bool
  Γe : Option (List (Ty ι))
  carried : Option (State × List (PromiseCalls.Implication ι))

/-- A node's regional check as `regionalAt` made it: the regional facts
carried into each label after it, those the check used at the node itself,
the tables and the evidence `checkNode` accepted. -/
structure RegionalDone (ι : Type) where
  regionIn : Array (List RegionState)
  state : RegionState
  table : List (List GraphCode.ArgumentPathTracking.Fact)
  ft : GraphCode.ArgumentRegionFresh.FreshTables
  cEv : NodeEvidence ι

/-- The walk's arrays and threaded values a node's exits change: the states,
implications and merge edges carried into each label, the processed edges,
the answers, counters and trace, the in-degrees, the regional facts carried
in, where each incoming state came from, the queue, each node's
satisfiability, the step's yields, the node's regional check, and each exit
as the fold took it. -/
structure ExitsDone (ι : Type) [BEq ι] [Hashable ι] (G : NormalGraph ι) where
  incoming : Array (List State)
  incomingImpl : Array (List (List (PromiseCalls.Implication ι)))
  incomingEdges : Array (List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping))
  edges : Array (EdgeWalk ι)
  answers : Answered G
  counts : Counts
  trace : Trace
  indeg : Array Nat
  regionIn : Array (List RegionState)
  incomingFrom : Array (List Nat)
  queue : List Nat
  unsat : Array (Option Bool)
  yields : Option (List (PromiseCalls.Yield ι))
  regional : Option (RegionalDone ι)
  exits : Array (ExitRecord ι) := #[]

/-- The step's yields the exits read: those the step kept; and the step's
final answers. -/
def exitsYields (G : NormalGraph ι) (images : InstanceImageCheck G) (_env : WalkEnv ι G images) (_l : Nat)
    (_en : Entered ι) (sd : StepDone ι G) : Option (List (PromiseCalls.Yield ι)) × Answered G :=
  (sd.yields, sd.answers)

/-- Each yield restated at every slot holding its target's name, as the
alias links of a positional state relate them. -/
def yieldsAtSlots (names : List Nat) (ys : List (PromiseCalls.Yield ι)) : List (PromiseCalls.Yield ι) :=
  ys.flatMap fun y => match names[y.target]? with
    | some nm => (names.zipIdx.filter (·.1 == nm)).map fun (_, j) => { y with target := j }
    | none => [y]

/-- **The regional evidence's entry facts**: the entry's whole
materialization `kHere` together with the step's facts `stepK`, each list
`kHere`'s then `stepK`'s others; the separations joined
(`HeapSeparation.union`): both where they are at one depth, the other where
one is empty, `stepK`'s otherwise, so every separation fact of the step's
derivation check is stated. -/
def regionalFacts (kHere stepK : Knowledge) : Knowledge :=
  { cells := kHere.cells ++ stepK.cells.filter (!kHere.cells.contains ·)
    values := kHere.values ++ stepK.values.filter (!kHere.values.contains ·)
    links := kHere.links ++ stepK.links.filter (!kHere.links.contains ·)
    separation := HeapSeparation.union kHere.separation stepK.separation
    elems := kHere.elems ++ stepK.elems.filter (!kHere.elems.contains ·)
    indices := kHere.indices ++ stepK.indices.filter (!kHere.indices.contains ·) }

/-- **A regional check at a node**, as `ArgumentRegionGraph.checkNode` makes
it: its regional facts on entry (the regions' input slots at the start, a
loop head's given ones, else what every edge into it establishes), the
cells and fields it keeps, and on each edge what the node establishes at the
target (a loop head's given facts there); the regional facts carried into
each label after it, those the check used at the node itself, its tables and
evidence, or the refusal. -/
def regionalAt (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (l : Nat)
    (en : Entered ι) (sd : StepDone ι G) (rg : Regional) (answers : Answered G)
    (regionIn : Array (List RegionState)) : Except String (RegionalDone ι) :=
  let node := env.nodes[l]!
  let c := env.claimed[l]!
  let width := c.context.length
  let st := sd.st
  let here : RegionState := if l == env.start then
      { facts := ((rg.regions.map fun (x : Footprints.ArgumentSpineRegion) =>
          ({ position := x.position, path := [] } : Footprints.ArgumentSpineRegion)).eraseDups).map fun x => ⟨x.position, x⟩ }
    else if env.isHead[l]! then ((rg.heads[l]?).join).getD {}
    else RegionState.meet (regionIn[l]!)
  let sums := answers.summaries.toList
  let ordinaryEv : Option (OrdinaryEvidence ι) := match st.stepDeriv, st.stepEffect with
    | some d, _ => some (.proof d)
    | none, some _ => some .effect
    | none, none => none
  let kHere := (materialize en.entry width (List.range width) true).1
  if !regionalDerivChecked G images env.codes sums c node st.stepK st.stepDeriv then
    .error s!"spine regions at node {l}: its derivation"
  else if !regionalHeaderChecked c st.stepDeriv st.stepEffect then
    .error s!"spine regions at node {l}: its step evidence"
  else
    let cEv : NodeEvidence ι := ⟨ordinaryEv, some ⟨c.context, node.expression, c.type⟩, [], regionalFacts kHere st.stepK, st.stepEffect, {}, none, [], [], [], none⟩
    let t0 := node.expression
    let F := here.values
    let C := if GraphCode.ArgumentRegionGraph.cellsKept G images sums rg.Φ F here.cells cEv t0 node.handler.isSome
      then here.cells else []
    let Fs := here.fields.filter fun p =>
      HeapExpressionRules.stableFirst G (ControlFlow.entry cEv) p.1 p.2 ||
        GraphCode.ArgumentRegionFresh.nullishSlot G (ControlFlow.entry cEv) p.1
    let origins := GraphCode.ArgumentRegionGraph.nodeOrigins rg.regions here.facts t0
    let pushes := GraphCode.pushes node.continuation
    let outR := if pushes then GraphCode.ArgumentPathTracking.afterPush here.facts origins else here.facts
    let outF := GraphCode.ArgumentRegionGraph.freshOut G images sums F C cEv t0
    let outC := GraphCode.ArgumentRegionGraph.cellOut F C t0
    let outFs := GraphCode.ArgumentRegionGraph.fieldOut rg.names F Fs t0
    let established := fun (t : Target) (handler : Bool) =>
      let w := ((env.claimed[t.label]?).map (·.context.length)).getD 0
      let src := fun (j : Nat) => PointClaims.slot t.mapping j
      let rfacts := if handler then GraphCode.ArgumentPathTracking.shift here.facts else outR
      let facts := (List.range w).flatMap fun j => (rfacts.filter (·.slot == src j)).map fun f => ⟨j, f.region⟩
      let values := (List.range w).filter fun j =>
        if handler then GraphCode.freshSlot F true false (src j) else GraphCode.freshSlot F pushes outF (src j)
      let cells := (List.range w).filter fun j =>
        if handler then GraphCode.freshSlot C true false (src j) else GraphCode.freshSlot C pushes outC (src j)
      let fields := (List.range w).flatMap fun j => (rg.names.filter fun f =>
        if handler then (match src j with | 0 => false | j' + 1 => Fs.contains (j', f))
        else GraphCode.ArgumentRegionGraph.fieldSlot Fs outFs pushes (src j) f).map (j, ·)
      ({ facts, values, cells, fields } : RegionState)
    let targets := (successors node.continuation).map (·, false) ++ node.handler.toList.map (·, true)
    let (at_, regionIn) := targets.foldl (fun (acc : List (Nat × RegionState) × Array (List RegionState)) (t, h) =>
      if env.isHead[t.label]! then (acc.1 ++ [(t.label, ((rg.heads[t.label]?).join).getD {})], acc.2)
      else
        let e := established t h
        (acc.1 ++ [(t.label, e)], acc.2.modify t.label (e :: ·)))
      ([(l, { here with cells := C, fields := Fs })], regionIn)
    let n := env.n
    let table := sparse n [] (at_.map fun (x, r) => (x, r.facts))
    let ft : GraphCode.ArgumentRegionFresh.FreshTables := ⟨sparse n [] (at_.map fun (x, r) => (x, r.values)),
      sparse n [] (at_.map fun (x, r) => (x, r.cells)), sparse n [] (at_.map fun (x, r) => (x, r.fields)), rg.names⟩
    if !(timedKind "regional node" fun _ => GraphCode.ArgumentRegionGraph.checkNode G images sums rg.Φ rg.regions table ft rg.exc l node cEv) then
      .error s!"spine regions at node {l}"
    else .ok { regionIn, state := { here with cells := C, fields := Fs }, table, ft, cEv }

/-- Whether each slot `diff` names has, in the edge's context `Γ`, a type
below the target's (`subtypeUsing`; the observed slot 0 never); and the
answers after them. -/
def diffSubtypes (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ Δ : List (Ty ι)) (diff : List (Nat × Nat))
    (observed : Option BranchRefinement.Observation) (answers : Answered G) : Bool × Answered G :=
  diff.foldl (fun (acc : Bool × Answered G) (i, s) => match Γ[s]?, Δ[i]? with
    | some A, some B =>
      if observed.isNone || s != 0 then
        let (r, a) := subtypeUsing G images A B acc.2
        (acc.1 && r.value.isSome, keepSummaries acc.2 a)
      else (false, acc.2)
    | _, _ => (false, acc.2)) (true, answers)

/-- A refined context `Γ'` where a slot whose refined type the target's
(`Δ`, through the mapping `m`) does not admit is read at its unrefined type
in `Γ`: both are types of its value (an alias refined through an array's
invariant element type); and the answers after it. -/
def mixedContext (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ Γ' Δ : List (Ty ι)) (m : PointClaims.Mapping)
    (answers : Answered G) : List (Ty ι) × Answered G :=
  let (mixed, answers) := Γ'.zipIdx.foldl (fun (acc : Array (Ty ι) × Answered G) (A', s) =>
    let A := (Γ[s]?).getD A'
    let reads := (List.range Δ.length).filter fun i => PointClaims.slot m i == s
    let (fits, answers) := reads.foldl (fun (fa : Bool × Answered G) i =>
      if fa.1 then
        match Δ[i]? with
        | some B =>
          if !same A' B then
            let (res, a') := subtypeUsing G images A' B fa.2
            (res.value.isSome, keepSummaries fa.2 a')
          else fa
        | none => fa
      else fa) (true, acc.2)
    (acc.1.push (if fits then A' else A), answers)) (#[], answers)
  (mixed.toList, answers)

/-- Whether a held implication `held` gives the given implication `x`: one
of the same type, or of a type below it (`subtypeUsing`); and the answers
after them. -/
def impliesHeld (G : NormalGraph ι) (images : InstanceImageCheck G) (x : PromiseCalls.Implication ι)
    (held : List (PromiseCalls.Implication ι)) (answers : Answered G) : Bool × Answered G :=
  held.foldl (fun (acc : Bool × Answered G) y =>
    if acc.1 then acc
    else if same y.type x.type then (true, acc.2)
    else
      let (res, a') := subtypeUsing G images y.type x.type acc.2
      (res.value.isSome, keepSummaries acc.2 a')) (false, answers)

/-- Whether a head's given implications (at `t`'s label) hold on an edge
into it carrying `carried` over the names `names`, the first that does not
stopping the check; and the answers after them. -/
def headImplies (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (t : Target)
    (names : List Nat) (carried : List (PromiseCalls.Implication ι)) (answers : Answered G) : Bool × Answered G :=
  ((env.givenImplies[t.label]?).getD []).foldl (fun (acc : Bool × Answered G) x =>
    if !acc.1 then acc
    else
      let nt := names[PointClaims.slot t.mapping x.test]?
      let na := names[PointClaims.slot t.mapping x.target]?
      let held := carried.filter fun y => some y.test == nt && some y.target == na
      impliesHeld G images x held acc.2) (true, answers)

/-- The first of a head's given implications (at `t`'s label) that does not
hold on an edge into it carrying `carried` (`headImplies`), by its tested and
narrowed slots: what a refusal names, each implication a proposal of its own. -/
def headImpliesFailing (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (t : Target)
    (names : List Nat) (carried : List (PromiseCalls.Implication ι)) (answers : Answered G) : Option (Nat × Nat) :=
  (((env.givenImplies[t.label]?).getD []).foldl (fun (acc : Option (Nat × Nat) × Answered G) x =>
    if acc.1.isSome then acc
    else
      let nt := names[PointClaims.slot t.mapping x.test]?
      let na := names[PointClaims.slot t.mapping x.target]?
      let held := carried.filter fun y => some y.test == nt && some y.target == na
      let (ok, a) := impliesHeld G images x held acc.2
      (if ok then none else some (x.test, x.target), a)) (none, answers)).1

/-- The edge's types (`visitExits`, where the edge's context is met): each
slot's type below the target's (`diffSubtypes`), else the edge search
(`checkedEdge`) over the edge's facts, else over the node's output facts at
the context the step's yields refine (`refinedContext`), else at the mixed
context (`mixedContext`); how they passed (`ExitTyped`), or the refusal where
none passes. -/
def exitTypes (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (l : Nat)
    (en : Entered ι) (_sd : StepDone ι G) (outAll : Thunk Knowledge) (t : Target) (tc : PointClaim ι)
    (Γ : List (Ty ι)) (names : List Nat) (edgeStore : Store) (pushed isHandler : Bool)
    (observed : Option BranchRefinement.Observation) (first : Bool) (diff : List (Nat × Nat))
    (acc : ExitsDone ι G) : Except (WalkStop ι G) (ExitsDone ι G × ExitTyped ι) :=
  let node := env.nodes[l]!
  let c := env.claimed[l]!
  let width := c.context.length
  let entry := en.entry
  let (ok, answers) := diffSubtypes G images Γ tc.context diff observed acc.answers
  if ok then .ok ({ acc with answers }, .subtypes)
  else
    -- The edge as the search reads it, its observation included.
    let counts := { acc.counts with edgeSearches := acc.counts.edgeSearches + 1 }
    let (ko, _, _) := materialize { names, store := edgeStore } (if pushed then width + 1 else width)
      (0 :: diff.map (·.2)) false
    -- Its links restated on every slot of their classes, as an edge reads
    -- a node's output (`ControlFlow.outFacts`).
    let ko := KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G Γ) ko
    -- The edge's context refined by its facts' safe integers
    -- (`PromiseCalls.intRefine`), as a step's is.
    let Γk := PromiseCalls.intRefine G Γ ko.indices
    let (found, a) := timedKind "edge search" fun _ => checkedEdge G images env.claimed tc.context Γk t observed ko answers
    let answers := keepSummaries answers a
    if !found && isHandler then
      .error (WalkStop.mk (.refused s!"handler edge from node {l} to node {t.label}") counts answers acc.trace)
    else if found then .ok ({ acc with answers, counts }, .edge ko)
    else
      -- The edge's context as the step's yields refine it
      -- (`produceNodeAt`): what a test or a promise establishes.
      let ys := acc.yields.getD []
      let outL := outAll.get
      let Γ' := refinedContext G c node.continuation (yieldsAtSlots entry.names ys) outL first
      let (found, a) := checkedEdge G images env.claimed tc.context Γ' t observed outL answers
      let answers := keepSummaries answers a
      let (found, answers, typed) := if found then (found, answers, ExitTyped.refined Γ' outL ys)
        else
          let (Γm, answers) := mixedContext G images Γ Γ' tc.context t.mapping answers
          if Γm != Γ' then
            let (found, a) := checkedEdge G images env.claimed tc.context Γm t observed outL answers
            (found, keepSummaries answers a, ExitTyped.mixed Γm outL)
          else (found, answers, ExitTyped.mixed Γm outL)
      if !found then
        .error (WalkStop.mk (.refused s!"edge from node {l} to node {t.label}{if l == env.debugNode then s!" fields {reprStr (readFields ko 0)} links {reprStr ko.links} diff {reprStr diff} implies {reprStr (en.implies.map fun x => (x.test, x.target))} names {reprStr (entry.names.take 6)} yields {reprStr (ys.map fun y => (y.target, y.conditional))}" else ""}") counts answers acc.trace)
      else .ok ({ acc with answers, counts }, typed)

/-- **A refused edge's facts** (`EdgeFacts`), from node `l` at its exit
`exit` to the target `t` (its claim `tc`), refused for `requirement`, the
exit's context `Γ` (its head the thrown value's type at the handler's
exit): of the requirement `req`, its atoms split by whether the check that
decides it (`KnowledgeExpand.checkIn`, from the edge's facts `src` through
the mapping) establishes each with the requirement's links; the edge's
facts restated at the target's slots as a step reads its predecessor's
(`materialize`): its index facts over a name no target slot reads restated
through the read links giving it (`HeapKnowledge.restateReads`), those
names eliminated (`HeapKnowledge.eliminateIndices`), each fact renamed to
every target slot reading each of its slots (`Atom.renameEach`), those over
the requirement's slots `slots` or a lacking fact's. Read only where the
refusal is printed. -/
def edgeFactsAt (G : NormalGraph ι) {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l exit : Nat) (t : Target) (tc : PointClaim ι)
    (Γ : List (Ty ι)) (requirement : EdgeRequirement) (req src : Knowledge) (slots : List Nat) : EdgeFacts ι :=
  let thrown := if ((Exit.ofNode env.nodes[l]!)[exit]?).any Exit.isHandler then Γ.head? else none
  let width := Γ.length
  let tw := tc.context.length
  let ctx := KnowledgeExpand.ctxOf G tc.context
  let held := fun (a : Atom) => KnowledgeExpand.checkIn ctx src (ofAtoms (a :: req.links.map .link) tw) t.mapping
  let (established, lacking) := (atomsOf req).partition held
  let targetsOf : Std.HashMap Nat (List Nat) := (List.range tw).foldl (fun m j =>
    let x := PointClaims.slot t.mapping j
    if x < width then m.insert x (m.getD x [] ++ [j]) else m) {}
  let read := fun (x : Nat) => targetsOf.contains x
  let dropped := ((atomsOf src).flatMap Atom.names).eraseDups.filter (!read ·)
  let indices := HeapKnowledge.eliminateIndices dropped
    (src.indices ++ HeapKnowledge.restateReads src.links (!read ·) src.indices)
  let focus := slots ++ lacking.flatMap Atom.names
  let known := (atomsOf { src with indices }).flatMap (fun a =>
      if a.names.all read then a.renameEach targetsOf else []) |>.filter fun a => a.names.any focus.contains
  { source := l, target := t.label, exit, thrown, requirement, required := req,
    established := ofAtoms established tw, lacking := ofAtoms lacking tw, known := ofAtoms known.eraseDups tw }

/-- The edge's facts over the target slots `slots`, as a head's query
reads them (`headExit`): the facts its store holds over the source slots
the mapping reads for them, with the links its context's types state. -/
def edgeKnowledge (G : NormalGraph ι) (t : Target) (Γ : List (Ty ι)) (names : List Nat) (edgeStore : Store)
    (slots : List Nat) : Knowledge :=
  let (k, _, _) := materialize { names, store := edgeStore } Γ.length (slots.map (PointClaims.slot t.mapping)) true
  HeapKnowledge.withTypedLinks G Γ k

/-- The deferred facts of an edge refused for a requirement other than
facts, `due` (the requirement and its target slots), where it names one
(`edgeFactsAt`, over the edge's facts at those slots, `edgeKnowledge`). -/
def requirementDetail (G : NormalGraph ι) {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l exit : Nat)
    (t : Target) (tc : PointClaim ι) (Γ : List (Ty ι)) (names : List Nat) (edgeStore : Store)
    (due : Option (EdgeRequirement × List Nat)) : Option (Thunk (Option (RefusalDetail ι))) :=
  due.map fun (r, slots) => Thunk.mk fun _ =>
    some (.edge (edgeFactsAt G env l exit t tc Γ r {} (edgeKnowledge G t Γ names edgeStore slots) slots))

/-- An edge into a head (`exitStep`): recorded; where the edge's context is
met, the head's given implications and the slots it states to hold an
input's entry value or the promised input hold on it; the head's given state
entailed on it. -/
def headExit (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (l exit : Nat)
    (t : Target) (tc : PointClaim ι) (Γ : List (Ty ι)) (names : List Nat) (edgeStore : Store) (pushed : Bool)
    (vacuous : Bool) (carried : List (PromiseCalls.Implication ι)) (freshOut : List Nat) (acc : ExitsDone ι G) :
    Except (WalkStop ι G) (ExitsDone ι G) :=
  let width := (env.claimed[l]!).context.length
  let edges := acc.edges.push { source := l, target := t, pushed, carried, meets := !vacuous }
  -- The head's given implications hold on every edge into it.
  let (implOk, answers) := if vacuous then (true, acc.answers) else headImplies G images env t names carried acc.answers
  if !implOk then
    let failing := headImpliesFailing G images env t names carried acc.answers
    let due := failing.map (fun (a, b) => (EdgeRequirement.implication a b, [a, b]))
    .error (WalkStop.mk (.refused s!"edge from node {l} into statement entry {t.label}: an implication{match failing with
      | some (a, b) => s!" {a} {b}"
      | none => ""}" none (requirementDetail G env l exit t tc Γ names edgeStore due)) acc.counts answers acc.trace)
  -- The slots it states hold the promised input, or an input's entry
  -- value, hold it on every edge.
  else if !vacuous && ((env.givenInputs[t.label]?).getD []).any (fun (j, q) => names[PointClaims.slot t.mapping j]? != env.startNames[q]?) then
    let failing := ((env.givenInputs[t.label]?).getD []).find? (fun (j, q) => names[PointClaims.slot t.mapping j]? != env.startNames[q]?)
    let due := failing.map (fun (j, q) => (EdgeRequirement.inputValue j q, [j]))
    .error (WalkStop.mk (.refused s!"edge from node {l} into statement entry {t.label}: an input's value" none
      (requirementDetail G env l exit t tc Γ names edgeStore due)) acc.counts answers acc.trace)
  else if !vacuous && ((env.givenArgs[t.label]?).getD []).any (fun j => names[PointClaims.slot t.mapping j]? != env.argName) then
    let failing := ((env.givenArgs[t.label]?).getD []).find? (fun j => names[PointClaims.slot t.mapping j]? != env.argName)
    let due := failing.map (fun j => (EdgeRequirement.promisedInput j, [j]))
    .error (WalkStop.mk (.refused s!"edge from node {l} into statement entry {t.label}: the promised input" none
      (requirementDetail G env l exit t tc Γ names edgeStore due)) acc.counts answers acc.trace)
  else if !vacuous && (headFreshAt env t.label).any (fun j => !(names[PointClaims.slot t.mapping j]?).any freshOut.contains) then
    .error (WalkStop.mk (.refused s!"edge from node {l} into statement entry {t.label}: a fresh slot") acc.counts answers acc.trace)
  else
    -- The head's given state is entailed on every edge into it.
    match env.given[t.label]! with
    | none => .error (WalkStop.mk (.refused s!"head {t.label}") acc.counts answers acc.trace)
    | some req =>
      let slots := (atomsOf req).flatMap Atom.names
      let srcSlots := slots.map (PointClaims.slot t.mapping)
      let (k, _, _) := materialize { names, store := edgeStore } (if pushed then width + 1 else width) srcSlots true
      let counts := { acc.counts with queries := acc.counts.queries + 1, queryAtoms := acc.counts.queryAtoms + (atomsOf k).length }
      if !vacuous && !(timedKind "head query" fun _ => KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context)
          (HeapKnowledge.withTypedLinks G Γ (ControlFlow.withTypedCells G Γ req t.mapping k)) req t.mapping) then
        -- The given facts the edge does not establish, named.
        let ctx := KnowledgeExpand.ctxOf G tc.context
        let src := HeapKnowledge.withTypedLinks G Γ (ControlFlow.withTypedCells G Γ req t.mapping k)
        let missing := (atomsOf req).filter fun a => !KnowledgeExpand.checkIn ctx src (ofAtoms [a] tc.context.length) t.mapping
        let trace := if env.tracing then
            { acc.trace with missing := missing.filterMap fun a => a.rename fun i => names[PointClaims.slot t.mapping i]? }
          else acc.trace
        .error (WalkStop.mk (.refused s!"edge from node {l} into statement entry {t.label}: lacks {missing.length} of its facts"
          (some (t.label, missing.filterMap fun a => match a with | .index x => some (.index x) | .link g => some (.link g) | _ => none))
          (some (Thunk.mk fun _ => some (.edge (edgeFactsAt G env l exit t tc Γ .facts req src []))))) counts answers trace)
      else .ok { acc with edges, answers, counts }

/-- A target's assertion established on an edge into a node other than a
head, as the edge test into a statement entry establishes it
(`checkTargetResult`): over the edge's facts, its context `Γe` as the
yields refine it, with the facts that context's types state of the cells
and links it reads; the counters and trace after it, or the refusal. -/
def assertionExit (G : NormalGraph ι) {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l exit : Nat)
    (t : Target) (tc : PointClaim ι) (Γe : Thunk (List (Ty ι))) (names : List Nat) (edgeStore : Store) (pushed : Bool)
    (observed : Option BranchRefinement.Observation) (vacuous : Bool) (acc : ExitsDone ι G) :
    Except (WalkStop ι G) (ExitsDone ι G) :=
  let width := (env.claimed[l]!).context.length
  match env.stated[t.label]! with
  | none => .ok acc
  | some req =>
    if vacuous then .ok acc
    else
      let slots := (atomsOf req).flatMap Atom.names
      let srcSlots := slots.map (PointClaims.slot t.mapping)
      let (k, _, _) := materialize { names, store := edgeStore } (if pushed then width + 1 else width) srcSlots false
      let Γe := Γe.get
      let k := match observed with
        | some o => HeapKnowledge.observeTyped G Γe (ControlFlow.withTypedCells G Γe req t.mapping k) 0 o
        | none => HeapKnowledge.withTypedLinks G Γe (ControlFlow.withTypedCells G Γe req t.mapping k)
      let counts := { acc.counts with queries := acc.counts.queries + 1, queryAtoms := acc.counts.queryAtoms + (atomsOf k).length }
      if !KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context) k req t.mapping then
        let missing := (atomsOf req).filter fun a =>
          !KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context) k (ofAtoms [a] tc.context.length) t.mapping
        let trace := if env.tracing then
            { acc.trace with missing := missing.filterMap fun a => a.rename fun i => names[PointClaims.slot t.mapping i]? }
          else acc.trace
        .error (WalkStop.mk (.refused s!"edge from node {l} into node {t.label}: its assertion lacks {missing.length} of its facts" none
          (some (Thunk.mk fun _ => some (.edge (edgeFactsAt G env l exit t tc Γe .facts req k []))))) counts acc.answers trace)
      else .ok { acc with counts }

/-- An edge into a node other than a head carried in (`exitStep`): the
state and implications it carries (`edgeTransfer`) pushed at the target,
where it came from (where observed or traced), the edge recorded, into a
merge the edge as the merge reads it (its context `Γe`, its implications at
the source's slots, its mapping); the target's in-degree one less, and the
target queued where it reaches 0. -/
def pushExit {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat) (t : Target)
    (target : State) (carried : List (PromiseCalls.Implication ι)) (Γe : Thunk (List (Ty ι))) (names : List Nat)
    (pushed vacuous : Bool) (acc : ExitsDone ι G) : ExitsDone ι G :=
  let incoming := acc.incoming.modify t.label (target :: ·)
  let incomingFrom := if env.observe == some t.label || env.tracing then acc.incomingFrom.modify t.label (l :: ·)
    else acc.incomingFrom
  let incomingImpl := acc.incomingImpl.modify t.label (carried :: ·)
  let edges := acc.edges.push { source := l, target := t, pushed, carried, meets := !vacuous }
  let incomingEdges := if env.merging[t.label]! then
      let slotsOf : Std.HashMap Nat (List Nat) := names.zipIdx.foldl (fun acc (x, i) =>
        acc.insert x (i :: acc.getD x [])) {}
      let atSlots := carried.flatMap fun (x : PromiseCalls.Implication ι) =>
        (slotsOf.getD x.test []).flatMap fun i => (slotsOf.getD x.target []).map fun j =>
          (⟨i, j, x.type⟩ : PromiseCalls.Implication ι)
      acc.incomingEdges.modify t.label ((Γe.get, atSlots, t.mapping) :: ·)
    else acc.incomingEdges
  let indeg := acc.indeg.modify t.label (· - 1)
  let queue := if indeg[t.label]! == 0 then t.label :: acc.queue else acc.queue
  { acc with incoming, incomingFrom, incomingImpl, edges, incomingEdges, indeg, queue }

/-- Whether an exit's mapping `m` gives a target of `width` slots over
`count` source names: the identity where `count = width`, else as many
slots as `width`, each below `count`. -/
def mappingWidthOk (m : PointClaims.Mapping) (count width : Nat) : Bool :=
  match m with
  | none => count == width
  | some slots => slots.length == width && slots.all (· < count)

/-- **One exit of node `l`** (`visitExits` folds it over the node's exits
with their positions): the exit's context and names, its edge facts
(`edgeStoreOf`), whether some environment meets it, the target's
satisfiability; where it is met, its types (`exitTypes`); then into a head
`headExit`, else the target's assertion (`assertionExit`) and the carried
state (`pushExit`); the exit recorded (`ExitRecord`). Whether the exit is its continuation's first (a
two-way dispatch's true arm) is its position. -/
def exitStep (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (l : Nat)
    (en : Entered ι) (sd : StepDone ι G) (ysAll : List (PromiseCalls.Yield ι)) (outAll : Thunk Knowledge)
    (acc : ExitsDone ι G) (exi : Exit × Nat) : Except (WalkStop ι G) (ExitsDone ι G) :=
  let ex := exi.1
  let first := exi.2 == 0
  let node := env.nodes[l]!
  let c := env.claimed[l]!
  let width := c.context.length
  let entry := en.entry
  let st := sd.st
  let t := ex.target
  let pushed := ex.pushed
  let observed := ex.observed
  let isHandler := ex.isHandler
  let pushedNames := st.result :: entry.names
  let acc := if env.tracing then { acc with trace := { acc.trace with edge := some t.label } } else acc
  match env.claimed[t.label]? with
  | none => .error (WalkStop.mk (.refused s!"edge from {l}") acc.counts acc.answers acc.trace)
  | some tc =>
    let Γ := if isHandler then sd.thrownTy.getD [] :: c.context else if pushed then c.type :: c.context else c.context
    let names := if isHandler then sd.thrown :: entry.names else if pushed then pushedNames else entry.names
    -- The mapping gives the target's width over the exit's names.
    if !mappingWidthOk t.mapping names.length tc.context.length then
      .error (WalkStop.mk (.refused s!"edge from {l}: its mapping's width") acc.counts acc.answers acc.trace)
    else
    -- The edge's own facts: an observation of the result; a throw's, the
    -- entry's facts no heap change affects.
    let edgeStore := edgeStoreOf G Γ entry.store st.store names pushedNames width pushed isHandler observed ex.promote
    -- Whether no environment meets the edge's context: the node's own
    -- context's answer, and the pushed result's type.
    let unsatΓ := en.here || (if isHandler then ControlFlow.unsatisfiable G [sd.thrownTy.getD []]
      else pushed && ControlFlow.unsatisfiable G [c.type])
    -- Whether no environment meets the edge: its types, or its facts,
    -- which hold at no environment where they contain a false constant.
    let vacuous := (match observed with
      | some o => unsatΓ || (Γ[0]?).any (BranchRefinement.impossible G · o)
      | none => unsatΓ) || edgeStore.impossible
    let diff := if vacuous then [] else timedKind "edge types" fun _ => differing Γ tc.context t.mapping
    -- The target's own answer: a slot of the empty type is one the edge's
    -- context gives (where it has none) or a slot whose type differs.
    let acc := if (acc.unsat[t.label]!).isNone then
        let u := if unsatΓ then ControlFlow.unsatisfiable G tc.context
          else diff.any fun (i, _) => (tc.context[i]?).any fun B => ControlFlow.unsatisfiable G [B]
        { acc with unsat := acc.unsat.set! t.label (some u) }
      else acc
    let typed := if vacuous then .ok (acc, ExitTyped.vacuous)
      else exitTypes G images env l en sd outAll t tc Γ names edgeStore pushed isHandler observed first diff acc
    match typed with
    | .error stop => .error stop
    | .ok (acc, typed) =>
      -- The edge's implications: the entry's, and on a pushed edge those the
      -- result's conditional yields state of it.
      let freshImpl : List (PromiseCalls.Implication ι) := if !pushed || isHandler then [] else
        ((acc.yields.getD []).filterMap fun y => if y.conditional && !y.onFalse then
          (entry.names[y.target]?).map fun tgt => ⟨st.result, tgt, y.type⟩ else none)
      let record : ExitRecord ι := { index := exi.2, target := t, Γ, names, edgeStore, typed, head := false, Γe := none, carried := none }
      if env.isHead[t.label]! then
        (headExit G images env l exi.2 t tc Γ names edgeStore pushed vacuous (en.implies ++ freshImpl)
          (if pushed && !isHandler && sd.outFresh && !entry.fresh.contains st.result then st.result :: entry.fresh else entry.fresh) acc).map fun acc =>
          { acc with exits := acc.exits.push { record with head := true } }
      else
        let Γe : Thunk (List (Ty ι)) := Thunk.mk fun _ => if isHandler then Γ else refinedContext G c node.continuation ysAll outAll.get first
        match assertionExit G env l exi.2 t tc Γe names edgeStore pushed observed vacuous acc with
        | .error stop => .error stop
        | .ok acc =>
          let (target, carried) := edgeTransfer names t.mapping pushed isHandler sd.outFresh entry st.result edgeStore
            (en.implies ++ freshImpl) (env.live[t.label]!)
          let read := ((env.stated[t.label]!).isSome && !vacuous) || env.merging[t.label]!
          let acc := pushExit env l t target carried Γe names pushed vacuous acc
          let Γr := if read then some Γe.get else none
          .ok { acc with exits := acc.exits.push { record with Γe := Γr, carried := some (target, carried) } }

/-- A node's exits (`visit`'s third part), from the walk's state `σ`, its
entry `en` and its step `sd`: the yields the exits read (`exitsYields`), a
regional check (`regionalAt`), then `exitStep` folded over the exits with
their positions; the walk's arrays and threaded values after them. -/
def visitExits (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (σ : WalkState ι G)
    (l : Nat) (en : Entered ι) (sd : StepDone ι G) : Except (WalkStop ι G) (ExitsDone ι G) :=
  let node := env.nodes[l]!
  let c := env.claimed[l]!
  let (yields, answers) := exitsYields G images env l en sd
  let ysAll := yieldsAtSlots en.entry.names (yields.getD [])
  let outAll : Thunk Knowledge := Thunk.mk fun _ => outAllOf G c sd.st.stepOut
  let regional : Except String (Option (RegionalDone ι)) := match env.regional with
    | none => .ok none
    | some rg => (regionalAt G images env l en sd rg answers σ.regionIn).map some
  match regional with
  | .error why => .error (WalkStop.mk (.refused why) sd.counts answers sd.trace)
  | .ok regional =>
    let regionIn := match regional with
      | some r => r.regionIn
      | none => σ.regionIn
    let acc0 : ExitsDone ι G :=
      { incoming := σ.walk.incoming, incomingImpl := σ.walk.incomingImpl, incomingEdges := σ.walk.incomingEdges,
        edges := σ.walk.edges, answers, counts := sd.counts, trace := sd.trace, indeg := σ.indeg, regionIn,
        incomingFrom := σ.incomingFrom, queue := σ.queue, unsat := σ.unsat, yields, regional }
    (Exit.ofNode node).zipIdx.foldlM (exitStep G images env l en sd ysAll outAll) acc0

/-- What the walk records of a visited label, from its entry `en`, its step
`sd` and the regional facts its regional check used (`visitBody` writes it
once). -/
def LabelWalk.ofVisit {G : NormalGraph ι} (entryFresh : Nat) (en : Entered ι) (sd : StepDone ι G)
    (region : Option RegionState) : LabelWalk ι :=
  { visited := true, entryFresh, entry := some en.entry, implies := en.implies, stepFresh := en.fresh,
    stepSummaries := sd.stepAnswers.summaries.size, stepped := some sd.st,
    after := some { en.entry with names := sd.st.result :: en.entry.names, store := sd.st.store },
    bounded := sd.bounded, returned := sd.returned, merge := en.merge, region }

/-- The visits' records with a visit's record, where it made one. -/
def pushRecord (visits : Array VisitRecord) : Option VisitRecord → Array VisitRecord
  | some r => visits.push r
  | none => visits

/-- **The step a node's exits read** (`keptStep` at the supports
`env.framed` gives the node): at a framed node, the store after the step
holds the facts its return keeps. -/
def keptDone {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat) (en : Entered ι)
    (sd : StepDone ι G) : StepDone ι G :=
  { sd with st := keptStep (framedAt env.framed l) en.entry sd.st }

omit [Instantiates ι] in
/-- The step the exits read differs from the step in its store alone. -/
theorem keptDone_answers {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat)
    (en : Entered ι) (sd : StepDone ι G) : (keptDone env l en sd).answers = sd.answers := rfl

omit [Instantiates ι] in
theorem keptDone_outFresh {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat)
    (en : Entered ι) (sd : StepDone ι G) : (keptDone env l en sd).outFresh = sd.outFresh := rfl

omit [Instantiates ι] in
theorem keptDone_thrown {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat)
    (en : Entered ι) (sd : StepDone ι G) : (keptDone env l en sd).thrown = sd.thrown := rfl

omit [Instantiates ι] in
theorem keptDone_thrownTy {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat)
    (en : Entered ι) (sd : StepDone ι G) : (keptDone env l en sd).thrownTy = sd.thrownTy := rfl

omit [Instantiates ι] in
theorem keptDone_yields {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat)
    (en : Entered ι) (sd : StepDone ι G) : (keptDone env l en sd).yields = sd.yields := rfl

/-- One node's visit, its entry, its step and its exits, from the walk's
state `σ`: the state after it built here alone, the label's record written
once (`visit` keeps its read-summary table); the exits read the step with
the facts a framed node's return keeps (`keptDone`). -/
def visitBody (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (σ : WalkState ι G)
    (l : Nat) : Except (WalkStop ι G) (WalkState ι G) :=
  match visitEntry G images env σ l with
  | .error stop => .error stop
  | .ok en => match visitStep G images env σ l en with
    | .error stop => .error stop
    | .ok sd => match visitExits G images env σ l en (keptDone env l en sd) with
      | .error stop => .error stop
      | .ok ex =>
        .ok { walk := { labels := σ.walk.labels.set! l (LabelWalk.ofVisit σ.fresh en sd (ex.regional.map (·.state))), incoming := ex.incoming,
                        incomingImpl := ex.incomingImpl, incomingEdges := ex.incomingEdges, edges := ex.edges,
                        visited := σ.walk.visited + 1, visits := pushRecord σ.walk.visits sd.record },
              answers := ex.answers, counts := ex.counts, trace := ex.trace, indeg := ex.indeg, fresh := sd.fresh,
              regionIn := ex.regionIn, incomingFrom := ex.incomingFrom, queue := ex.queue, unsat := ex.unsat,
              lastStamp := en.lastStamp, lastKind := sd.lastKind }

/-- One node's visit (`drive` visits each once): `visitBody`, the answers it
leaves or stops with holding the table it started from as a prefix, so the
read-summary table only grows along the walk. -/
def visit (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (σ : WalkState ι G)
    (l : Nat) : Except (WalkStop ι G) (WalkState ι G) :=
  match visitBody G images env σ l with
  | .ok σ' => .ok { σ' with answers := keepSummaries σ.answers σ'.answers }
  | .error stop => .error { stop with answers := keepSummaries σ.answers stop.answers }

/-! ### The visit as the compiled verifier runs it

`visitBodyFast` and `visitFast` compute `visitBody` and `visit`
(`visitBody_eq_fast`, `visit_eq_fast`) holding no value of the walk's state
past its last read: the arrays and tables a visit updates are then held
once, and updated in place. -/

/-- `keepSummaries` from the earlier table alone. -/
def keepSummariesOf {G : NormalGraph ι} (pre : Array (ReadSummary ι)) (b : Answered G) : Answered G :=
  { b with summaries := pre ++ b.summaries.extract pre.size b.summaries.size }

/-- A step's record with the answers only the proofs read emptied. -/
def StepDone.light {G : NormalGraph ι} (sd : StepDone ι G) : StepDone ι G :=
  { sd with stepAnswers := {}, steppedAnswers := {}, yieldAnswers := {} }

theorem visitExits_light (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images)
    (σ : WalkState ι G) (L : Array (LabelWalk ι)) (V : Array VisitRecord) (l : Nat) (en : Entered ι) (sd : StepDone ι G) :
    visitExits G images env { σ with walk := { σ.walk with labels := L, visits := V } } l en sd.light =
      visitExits G images env σ l en sd := by
  rfl

omit [Instantiates ι] in
theorem keptDone_light {G : NormalGraph ι} {images : InstanceImageCheck G} (env : WalkEnv ι G images) (l : Nat)
    (en : Entered ι) (sd : StepDone ι G) : keptDone env l en sd.light = (keptDone env l en sd).light :=
  rfl

/-- `visitBody`, the walk's state taken apart after the step, the step's
record passed to the exits without the answers only the proofs read. -/
def visitBodyFast (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (σ : WalkState ι G)
    (l : Nat) : Except (WalkStop ι G) (WalkState ι G) :=
  match visitEntry G images env σ l with
  | .error stop => .error stop
  | .ok en => match visitStep G images env σ l en with
    | .error stop => .error stop
    | .ok sd =>
      let labels := σ.walk.labels
      let visits := σ.walk.visits
      let fresh := σ.fresh
      let visited := σ.walk.visited
      let stepSummaries := sd.stepAnswers.summaries.size
      let σx := { σ with walk := { σ.walk with labels := #[], visits := #[] } }
      let sdx := sd.light
      match visitExits G images env σx l en (keptDone env l en sdx) with
      | .error stop => .error stop
      | .ok ex =>
        .ok { walk := { labels := labels.set! l { LabelWalk.ofVisit fresh en sdx (ex.regional.map (·.state)) with
                          stepSummaries }, incoming := ex.incoming,
                        incomingImpl := ex.incomingImpl, incomingEdges := ex.incomingEdges, edges := ex.edges,
                        visited := visited + 1, visits := pushRecord visits sdx.record },
              answers := ex.answers, counts := ex.counts, trace := ex.trace, indeg := ex.indeg, fresh := sdx.fresh,
              regionIn := ex.regionIn, incomingFrom := ex.incomingFrom, queue := ex.queue, unsat := ex.unsat,
              lastStamp := en.lastStamp, lastKind := sdx.lastKind }

@[csimp] theorem visitBody_eq_fast : @visitBody = @visitBodyFast := by
  funext ι _ _ _ G images env σ l
  unfold visitBody visitBodyFast
  split
  · rfl
  · split
    · rfl
    · rename_i sd _
      simp only [keptDone_light, visitExits_light]
      split <;> rfl

/-- `visit`, holding of the walk's state it started from its read-summary
table alone. -/
def visitFast (G : NormalGraph ι) (images : InstanceImageCheck G) (env : WalkEnv ι G images) (σ : WalkState ι G)
    (l : Nat) : Except (WalkStop ι G) (WalkState ι G) :=
  let pre := σ.answers.summaries
  match visitBody G images env σ l with
  | .ok σ' => .ok { σ' with answers := keepSummariesOf pre σ'.answers }
  | .error stop => .error { stop with answers := keepSummariesOf pre stop.answers }

@[csimp] theorem visit_eq_fast : @visit = @visitFast := by
  funext ι _ _ _ G images env σ l
  rfl

/-- A fact of a store as one line (`DebugText`). -/
def Atom.text : Atom → String
  | .index a => DebugText.indexAtom a
  | .value f => s!"n{f.slot}.{DebugText.key f.field} ∈ {DebugText.oneLine f.contents}"
  | .cell f => s!"cell n{f.slot}.{DebugText.key f.field} ∈ {DebugText.oneLine f.contents}"
  | .link g => s!"link {DebugText.oneLine g}"
  | .elem e => s!"elem {DebugText.oneLine e}"
  | .sep f => s!"sep {DebugText.oneLine f}"

/-- A completed walk as text (`TSCERT_DUMP`): each node's term and
continuation, the slots it or a later node reads (`liveSlots`, `all` for
every slot), the names at its slots on entry, and the facts after its step,
with how many it added and dropped from its entry's. -/
def walkText (nodes : Array Node) (live : Array LiveSlots) (w : Walk ι) : String := Id.run do
  let mut out := s!"walk: {nodes.size} nodes"
  for l in [0:nodes.size] do
    let lw := w.labels[l]?
    let node := (nodes[l]?.map DebugText.node).getD "?"
    let reads := match (live[l]?).bind (·.slots) with
      | some L => String.intercalate " " ((L.toList.toArray.qsort (· < ·)).toList.map fun i => s!"#{i}")
      | none => "all"
    out := out ++ s!"\nnode {l}: {node}\n  reads: {reads}"
    match lw.bind (·.entry), lw.bind (·.after) with
    | some e, some a =>
      let before := e.store.live.toList.map Atom.text
      let after := a.store.live.toList.map Atom.text
      let added := after.filter (!before.contains ·)
      let dropped := before.filter (!after.contains ·)
      let slots := String.intercalate " " ((a.names.zipIdx).map fun (n, i) => s!"#{i}=n{n}")
      out := out ++ s!"\n  slots after: {slots}\n  facts after: {after.length} (+{added.length} -{dropped.length})"
      for f in (after.toArray.qsort (· < ·)).toList do
        out := out ++ s!"\n    {if added.contains f then "+" else " "} {f}"
      for f in (dropped.toArray.qsort (· < ·)).toList do
        out := out ++ s!"\n    - {f}"
    | _, _ => out := out ++ "\n  (not visited)"
  return out

/-- The walk over one graph: the setup, then `drive` over the visits; the
walk's state and the nodes the start reaches, or where it stopped. Under
`grading` each visit records its step's local effect (`Walk.visits`). -/
def runWalk (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge := #[]) (debugNode : Nat := 1000000000)
    (bound : Option RunBound := none)
    (givenImplies : Array (List (PromiseCalls.Implication ι)) := #[])
    (givenArgs : Array (List Nat) := #[])
    («ensures» : List HeapKnowledge.IndexFact := []) (givenInputs : Array (List (Nat × Nat)) := #[])
    (entrySeparation : HeapSeparation.Separation := {}) (observe : Option Nat := none) (tracing : Bool := false) (observeEntry : Bool := false)
    (regional : Option Regional := none) (grading : Bool := false)
    (framed : List (Nat × List Confinement.FrameSpec) := [])
    (givenFresh : Array (List Nat) := #[]) :
    Except (WalkStop ι G) (WalkState ι G × Nat) := do
  let (env, σ0) ← setup G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices
    suggestions known codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures
    givenInputs entrySeparation observe tracing observeEntry regional grading framed givenFresh
  -- Each node enters the queue once: a fuel of the nodes and one never runs out.
  let σ ← drive (visit G images env) (env.n + 1) σ0
  let _ := clock σ.lastKind σ.lastStamp σ.walk.visited
  let reachable := (env.reached.toList.filter id).length
  return dumpWalk (fun _ => walkText env.nodes env.live σ.walk) (σ, reachable)

/-- Check a local-confinement table `conf` against a completed walk `w`: the
start entry is empty, every framed node is in bounds, and every visited node
passes `LocalConfinement.checkNode` at its recorded `stepK` and `stepDeriv`. -/
def checkWalkConfinement (G : NormalGraph ι) (images : InstanceImageCheck G)
    (codes : CodeEntry ι → Bool) (sums : List (ProgramCertificates.ReadSummary ι))
    (P : Program) (claims : List (PointClaim ι)) (start : Nat)
    (conf : LocalConfinement.Table) (w : Walk ι) : Bool :=
  (conf.at start == {}) &&
  conf.framedNodes.all (· < P.length) &&
  (List.range P.length).all fun l =>
    match w.labels[l]? with
    | some lw =>
        if lw.visited then
          match P[l]?, claims[l]?, lw.stepped with
          | some node, some c, some st =>
              LocalConfinement.checkNode G images codes sums claims conf l node c st.stepK st.stepDeriv
          | _, _, _ => false
        else true
    | none => true

/-- The pass over one graph: its verdict a function of the walk's record
(`Walk.outcome`), plus `checkWalkConfinement` when `confinement` is supplied;
under `grading`, the visits' records in its counts. -/
def run (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List HeapKnowledge.Candidate)) (entryIndices : List IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge := #[]) (debugNode : Nat := 1000000000)
    (bound : Option RunBound := none)
    (givenImplies : Array (List (PromiseCalls.Implication ι)) := #[])
    (givenArgs : Array (List Nat) := #[])
    («ensures» : List HeapKnowledge.IndexFact := []) (givenInputs : Array (List (Nat × Nat)) := #[])
    (entrySeparation : HeapSeparation.Separation := {}) (observe : Option Nat := none) (tracing : Bool := false) (observeEntry : Bool := false)
    (regional : Option Regional := none) (grading : Bool := false)
    (framed : List (Nat × List Confinement.FrameSpec) := [])
    (confinement : Option LocalConfinement.Table := none)
    (givenFresh : Array (List Nat) := #[]) : Outcome ι × Counts × Answered G × Trace :=
  match runWalk G images pool fuel P claims start inputs goal assertions cuts candidates entryIndices suggestions known
      codes aliases passChecker answers reference debugNode bound givenImplies givenArgs ensures givenInputs
      entrySeparation observe tracing observeEntry regional grading framed givenFresh with
  | .error stop => (stop.outcome.outcome, stop.counts, stop.answers, stop.trace)
  | .ok (σ, reachable) =>
    let counts := { σ.counts with reached := reachable, grades := σ.walk.visits }
    let out := match confinement with
      | none => σ.walk.outcome reachable
      | some conf =>
          if framed == conf.framed &&
             checkWalkConfinement G images codes σ.answers.summaries.toList P claims start conf σ.walk then
            σ.walk.outcome reachable
          else
            .refused "local confinement"
    (out, counts, σ.answers, σ.trace)


/-- Where a fact over names, absent on entry of node `p`, was last present,
and what removed it: per path back, the node and the reason. A merge that
renames a name follows each predecessor under its own name. -/
def Trace.locate (t : Trace) (p : Nat) (a : Atom) (limit : Nat := 4) (onEntry : Bool := true) : List (Nat × String) := Id.run do
  -- The work: (node, fact over its names, whether absent on its entry (true)
  -- or on the edge out of it (false)).
  let mut work : List (Nat × Atom × Bool) := [(p, a, onEntry)]
  let mut seen : Std.HashSet (Nat × Bool) := {}
  let mut out : List (Nat × String) := []
  let mut fuel := t.entries.size * 2 + 2
  while fuel > 0 && out.length < limit do
    fuel := fuel - 1
    let some (q, b, onEntry) := work.head? | break
    work := work.tail
    if seen.contains (q, onEntry) then continue
    seen := seen.insert (q, onEntry)
    if onEntry then
      if (t.heads[q]?).getD false then
        out := out ++ [(q, if q == t.start then "not assumed at the unit's entry" else s!"not in the given invariant of loop head {q}")]
        continue
      match (t.merges[q]?).getD [] with
      | [] => match (t.single[q]?).join with
        | some r => work := work ++ [(r, b, false)]
        | none => out := out ++ [(q, "no predecessor")]
      | preds =>
        let having := preds.filter fun (_, (st : State), _) => st.store.holds b
        if !having.isEmpty then
          let lacking := preds.filter fun (_, (st : State), _) => !st.store.holds b
          out := out ++ [(q, s!"the merge at node {q} did not keep it: stated from {having.map (·.1)}, missing from {lacking.map (·.1)}")]
        -- Each predecessor lacking it, followed under its own names.
        for (r, (st : State), (m : Std.HashMap Nat (List Nat))) in preds do
          if !st.store.holds b then
            let inv : Std.HashMap Nat Nat := m.fold (fun acc x φs => φs.foldl (fun acc φ => acc.insert φ x) acc) {}
            match b.rename fun x => some (inv.getD x x) with
            | some b' => work := work ++ [(r, b', false)]
            | none => pure ()
    else
      let after := ((t.afters[q]?).join).map (·.store)
      let before := ((t.entries[q]?).join)
      if after.any (·.holds b) then
        out := out ++ [(q, s!"present after node {q}; the edge out of it does not carry it")]
      else if before.any (·.store.holds b) then
        out := out ++ [(q, s!"present on entry of node {q}; its step removed it")]
      else if !(b.names.all fun x => before.any (·.names.contains x)) then
        out := out ++ [(q, s!"a name it mentions is the result of node {q}, whose step does not state it")]
      else work := work ++ [(q, b, true)]
  return out

/-- The names a store's facts connect to the given ones, at most `limit`. -/
def Store.connected (s : Store) (seeds : List Nat) (limit : Nat := 40) : List Nat := Id.run do
  let mut seen : Std.HashSet Nat := Std.HashSet.ofList seeds
  let mut frontier := seeds
  while !frontier.isEmpty && seen.size < limit do
    let mut next := []
    for x in frontier do
      for a in s.about x do
        for y in a.names do
          if !seen.contains y then
            seen := seen.insert y
            next := y :: next
    frontier := next
  return seen.toList

/-- The facts over the focus's connected names that some state before the
refusal node held, renamed to that node's names, and that its state lacks:
each with where it was last present and what removed it. -/
def Trace.lost (t : Trace) (limit : Nat := 30) : List (Atom × List (Nat × String)) := Id.run do
  let some here := (t.entries[t.node]?).join | return []
  let live := Std.HashSet.ofList here.names
  let focus := Std.HashSet.ofList (here.store.connected t.focus)
  -- Back from the node: each predecessor with its names' renaming to the
  -- node's names, through merges, to the loop heads.
  let mut work : List (Nat × Std.HashMap Nat Nat) := [(t.node, {})]
  let mut seen : Std.HashSet Nat := {}
  let mut found : Std.HashSet Atom := {}
  let mut out : List Atom := []
  while out.length < limit do
    let some (q, toL) := work.head? | break
    work := work.tail
    if seen.contains q then continue
    seen := seen.insert q
    let states := [((t.afters[q]?).join), ((t.entries[q]?).join)].filterMap id
    for st in states do
      for b in st.store.toList do
        if out.length < limit then
          if let some bL := b.rename fun x => some (toL.getD x x) then
            if bL.names.all live.contains && bL.names.any focus.contains && !here.store.holds bL && !found.contains bL then
              found := found.insert bL
              out := out ++ [bL]
    if (t.heads[q]?).getD false then continue
    match (t.merges[q]?).getD [] with
    | [] => if let some r := (t.single[q]?).join then work := work ++ [(r, toL)]
    | preds =>
      for (r, _, (m : Std.HashMap Nat (List Nat))) in preds do
        work := work ++ [(r, m.fold (fun acc x φs => let φ := φs.headD x; acc.insert x (toL.getD φ φ)) toL)]
  return out.map fun a => (a, t.locate t.node a 2)

end
end Verification.SinglePass
