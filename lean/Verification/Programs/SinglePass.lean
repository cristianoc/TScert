import Verification.Programs.CertificateProducer
import Verification.Programs.GraphCode
import Verification.Programs.SinglePassStats
import Verification.Programs.ArgumentRegionCertificates

/-! One forward pass over a graph cut at its statement entries
(docs/drafts/single-pass.md): each node visited once, in a topological order
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

def Store.addRaw (s : Store) (a : Atom) : Store :=
  let a := a.canon
  if s.live.contains a then s else
  { live := s.live.insert a,
    byName := a.names.eraseDups.foldl (fun m n => m.insert n (a :: m.getD n [])) s.byName }

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
  /-- The names holding a store this run allocated (`GraphCode.inferFresh`'s
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
  | .objAt _ (.graph _ _ _ _ caps _ _) _ => mentionedAll d caps
  | .makeAt (.graph _ _ _ _ caps _ _) _ args => do pure ((← mentionedAll d caps) ++ (← mentionedAll d args))
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

/-- Whether `timedKind` measures (`TSCERT_PROFILE`): off, it runs `f` alone. -/
initialize profiling : IO.Ref Bool ← IO.mkRef false

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

/-- `f ()`, its time added to `kind`'s. -/
@[implemented_by timedKindImpl] def timedKind {α : Type} (_kind : String) (f : Unit → α) : α := f ()

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

/-- The verdict: refused at a located obligation, a construct the pass
does not handle, or the state observed at a chosen node. -/
inductive Outcome (ι : Type) where
  | accepted
  | refused (why : String)
  /-- Refused at node `l`'s footprint check (`GraphCode.nodeChecked`): the
  one refusal a regional check may still answer. -/
  | outsideBound (l : Nat)
  | notHandled (what : String)
  | observed (o : Observation ι)

instance : ToString (Outcome ι) where
  toString
    | .accepted => "accepted"
    | .refused w => s!"refused: {w}"
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

/-- One round of the selective worklist: each fact over a frontier name
not yet kept, kept in order; each name it chains through not yet seen,
seen and on the next frontier. -/
def selectRound (s : Store) (chain : Bool) (frontier : List Nat) (seen : Std.HashSet Nat)
    (kept : Std.HashSet Atom) (out : Array Atom) : List Nat × Std.HashSet Nat × Std.HashSet Atom × Array Atom :=
  frontier.foldl (fun acc x => (s.about x).foldl (fun (next, seen, kept, out) a =>
    if kept.contains a then (next, seen, kept, out) else
    (a.through chain).foldl (fun (next, seen, kept, out) y =>
      if seen.contains y then (next, seen, kept, out) else (y :: next, seen.insert y, kept, out))
      (next, seen, kept.insert a, out.push a)) acc) ([], seen, kept, out)

/-- The selective worklist (`selectRound`) from `frontier` until a round
finds no new name: each round with a next frontier keeps a new fact, so a
fuel of the store's size and two never runs out. -/
def selectFrom (s : Store) (chain : Bool) : Nat → List Nat → Std.HashSet Nat → Std.HashSet Atom → Array Atom → Array Atom
  | 0, _, _, _, out => out
  | fuel + 1, frontier, seen, kept, out =>
    if frontier.isEmpty then out else
    let (next, seen, kept, out) := selectRound s chain frontier seen kept out
    selectFrom s chain fuel next seen kept out

/-- The knowledge a step reads, at slots: the facts over the names of
`slots` and over the names those facts mention, a name out of scope
eliminated from the linear facts. With `whole`, every fact. The store's
facts with their images, for the step's delta, and the table of slots. -/
def materialize (st : State) (d : Nat) (slots : List Nat) (whole : Bool) (chain : Bool := true) :
    Knowledge × List (Atom × Atom) × Std.HashMap Nat Nat := timedKind (if whole then "materialize whole" else "materialize") fun _ =>
  let given := slots.filterMap fun s => st.names[s]?
  let atoms : List Atom := if whole then st.store.toList else
    (selectFrom st.store chain (st.store.size + 2) given (given.foldl (·.insert ·) {}) {} #[]).toList
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
      HeapKnowledge.restateStores links isOut indices
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
  -- path (`HeapKnowledge.restateReads`): the form a later step keeps where
  -- it drops the read's name.
  for x in added do
    for v in x.fact.slots do
      let reads := (s.about v).filterMap fun b => match b with
        | .link g => if !g.alias && g.value == v then some g else none
        | _ => none
      if !reads.isEmpty then
        for y in HeapKnowledge.restateReads reads (· == v) [x] do s := s.add (.index y)
  return s

instance : Inhabited Node := ⟨⟨.nul, .ret, none⟩⟩

/-- `a == b`, answered at once where they are one object (`withPtrEq`,
justified by the equality's reflexivity). -/
def same {α : Type} [BEq α] [ReflBEq α] (a b : α) : Bool :=
  withPtrEq a b (fun _ => a == b) (fun h => by subst h; exact BEq.rfl)

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
def orderedSuffix (slots : List Nat) (n : Nat) : Nat := Id.run do
  let arr := slots.toArray
  let mut k := arr.size
  while k > 0 && arr[k - 1]! + (arr.size - k) + 1 == n do k := k - 1
  return k

/-- The names of a target's slots: the mapping applied to the source's. -/
def mapNames (names : List Nat) (m : PointClaims.Mapping) : List Nat :=
  match m with
  | none => names
  | some slots => Id.run do
    -- The longest suffix of `slots` reading the source's slots in order to
    -- its end: those target slots share the source's names.
    let arr := slots.toArray
    let k := orderedSuffix slots names.length
    let tail := if k < arr.size then names.drop arr[k]! else []
    let mut cur := Cursor.of names
    let mut out : Array Nat := Array.mkEmpty k
    for s in slots.take k do
      let (x, c) := cur.get s
      cur := c
      out := out.push (x.getD 0)
    return out.toList ++ tail

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
    HeapKnowledge.restateStores links isOut indices
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
  let ordered := L.filter (fun (p : CallEffects.Arrow (Ty ι)) => p.effect.elements.isSome) ++
    L.filter (fun (p : CallEffects.Arrow (Ty ι)) => p.effect.elements.isNone)
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

/-- The facts one store holds and the other does not, each way. -/
def Store.diff (s t : Store) : List Atom × List Atom :=
  (s.toList.filter fun a => !t.live.contains a, t.toList.filter fun a => !s.live.contains a)

/-- The unconditional index facts connected to the names through linear
facts, at most `limit`: what a linear entailment over those names reads. -/
def Store.linearNear (s : Store) (names : List Nat) (limit : Nat := 40) : List IndexAtom := Id.run do
  let mut seen : Std.HashSet Nat := Std.HashSet.ofList names
  let mut frontier := names
  let mut kept : Std.HashSet Atom := {}
  let mut out : Array IndexAtom := #[]
  while !frontier.isEmpty && out.size < limit do
    let mut next := []
    for x in frontier do
      for a in s.about x do
        if let .index i := a then
          if i.cond.isNone && !kept.contains a && out.size < limit then
            kept := kept.insert a
            out := out.push i
            if let .linear _ := i.fact then
              for y in a.names do
                if !seen.contains y then
                  seen := seen.insert y
                  next := y :: next
    frontier := next
  return out.toList

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
store regions, whether it bounds a throw, the field names fresh fields
range over, and each loop head's given regional facts. -/
structure Regional where
  Φ : Footprints.Closed
  regions : List Footprints.ArgumentStoreRegion
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

/-- The loop heads of a graph: each target of a retreating edge of a
depth-first walk from the start (handlers' edges included); and the nodes
the walk reaches. -/
def loopHeads (nodes : Array ControlFlow.Node) (start : Nat) : Array Bool × Array Bool := Id.run do
  let n := nodes.size
  let mut heads : Array Bool := Array.replicate n false
  let mut state : Array Nat := Array.replicate n 0   -- 0 new, 1 on the stack, 2 done
  let mut stack : List (Nat × List Nat) := []
  if start < n then
    state := state.set! start 1
    stack := [(start, (successors nodes[start]!.continuation ++ nodes[start]!.handler.toList).map (·.label))]
  while true do
    match stack with
    | [] => break
    | (v, []) :: rest =>
      state := state.set! v 2
      stack := rest
    | (v, w :: ws) :: rest =>
      stack := (v, ws) :: rest
      if w < n then
        match state[w]! with
        | 0 =>
          state := state.set! w 1
          stack := (w, (successors nodes[w]!.continuation ++ nodes[w]!.handler.toList).map (·.label)) :: stack
        | 1 => heads := heads.set! w true
        | _ => pure ()
  return (heads, state.map (· != 0))

/-- A list of `n` labels' tables, empty but at the given labels. -/
def sparse {α : Type} (n : Nat) (empty : α) (at_ : List (Nat × α)) : List α :=
  at_.foldl (fun acc (l, x) => acc.set l x) (List.replicate n empty)

/-- The checker the pass runs: the proved layers (`Checker.ordinary`),
whose `select` takes a derivation as given, so the pass checks the step's
tree; or a qualified body's (`Checker.withSubtyping`), whose `select` is its
`run` (`select_eq_run`). -/
inductive PassChecker (G : NormalGraph ι) (images : InstanceImageCheck G) where
  | ordinary
  | qualified (subtyping : BodySubtyping G)
      (ord : ∀ {A B p}, PositiveCertificates.checkUsing G images A B p = true → subtyping.check A B p = true)

def PassChecker.checker {G : NormalGraph ι} {images : InstanceImageCheck G} :
    PassChecker G images → HeapExpressionRules.Checker G images
  | .ordinary => HeapExpressionRules.Checker.ordinary G images
  | .qualified s o => HeapExpressionRules.Checker.withSubtyping G images s o

/-- Whether the checker's `select` checks the step itself. -/
def PassChecker.selectChecks {G : NormalGraph ι} {images : InstanceImageCheck G} : PassChecker G images → Bool
  | .ordinary => false
  | .qualified .. => true

omit [Hashable ι] [Instantiates ι] in
theorem PassChecker.select_eq_run {G : NormalGraph ι} {images : InstanceImageCheck G} {p : PassChecker G images}
    (h : p.selectChecks = true) : p.checker.select = p.checker.run := by
  cases p with
  | ordinary => cases h
  | qualified s o => rfl

/-- The unit's entry checked as `ControlFlow.checkEntryResult` checks a
certificate's (no edge enters the start on the first invocation): the start's
context is the request's inputs; the promised input's slot is one of them;
the start's given state states no implication, names a slot after the
promised input only at that input's own slot and after an input's entry value
only at that input's slot; and its written and supplied facts are entailed
by the request's entry facts (`ControlFlow.entryKnows`). The refusal where
one fails. -/
def entryRefusal (G : NormalGraph ι) (inputs : List (Ty ι)) (claims : List (PointClaim ι)) (start : Nat)
    (goal : Goal ι) (written : Option Knowledge) (supplied : List IndexAtom)
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
    else
      let k := written.getD {}
      let k := { k with indices := k.indices ++ supplied }
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

/-- The start's given state as `run` builds it: `startWritten`, with the
claims' facts there (`supplied`). -/
def startGiven (written : Option Knowledge) (entryIndices : List IndexAtom)
    (entrySeparation : HeapSeparation.Separation) (supplied : List IndexAtom) : Knowledge :=
  let w := startWritten written entryIndices entrySeparation
  { w with indices := w.indices ++ supplied }

/-- **A node's step within a footprint bound** (`GraphCode.nodeChecked`),
at a node outside the region from which no normal return is possible: the
step within `Φ` (`ExpressionEffects.check`, `writeWithin`, `initWriteWithin`,
the step's derivation `deriv` within it at the fresh receivers `F`
(`selectedWithinAt`), claimed at the node's term and context and its tree
accepted, an empty type); its throw within it where a live handler catches
it or the bound covers throws (`exc`); a return under a fresh result
(`ret`) returning a fresh value (`outFresh`); the term in scope. -/
def footprintCheck (G : NormalGraph ι) (images : InstanceImageCheck G) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) (Φ : Footprints.Closed) (F : List Nat) (c : PointClaim ι) (node : Node)
    (stepK : Knowledge) (deriv : ProgramCertificates.Evidence ι) (liveHandler exc ret outFresh : Bool) : Bool :=
  -- The step's derivation, where its signature bounds the step: claimed
  -- at the node's term and context, its tree accepted (`GraphCode.nodeChecked`'s
  -- conjuncts beside `selectedWithinAt`).
  let derivChecked : Thunk Bool := Thunk.mk fun _ =>
    (ProgramCertificates.claim deriv).term == node.expression &&
      (ProgramCertificates.claim deriv).context == c.context &&
      (ProgramCertificates.checkTreeUsing G images deriv codes sums ||
        PromiseCalls.requiresTree G images stepK codes sums deriv)
  let writes := ExpressionEffects.writeWithin G c.context Φ node.expression ||
    ExpressionEffects.initWriteWithin G c.context stepK Φ node.expression
  let within := ExpressionEffects.check G c.context node.expression || writes ||
    (GraphCode.selectedWithinAt Φ F deriv && derivChecked.get) || ExpressionEffects.emptyType G c.type ||
    c.context.any (ExpressionEffects.emptyType G ·)
  -- The throw within the bound where a handler outside the region with
  -- no normal return catches it or the bound covers throws
  -- (`GraphCode.nodeChecked`'s `deadHandler`): an effect without
  -- `onThrow` bounds no throw a live handler catches.
  let throws := !(liveHandler || exc) || ExpressionEffects.check G c.context node.expression || writes ||
    (GraphCode.selectedWithinAt Φ F deriv && derivChecked.get && ExpressionEffects.selectedThrows deriv &&
      (match ExpressionEffects.selectedEffect deriv with | some eff => eff.onThrow | none => false)) ||
    c.context.any (ExpressionEffects.emptyType G ·)
  let returns := match node.continuation with
    | .ret => !ret || outFresh
    | _ => true
  within && throws && returns && ProgramCertificates.checkScope c.context.length node.expression

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
    (ensures : List HeapKnowledge.IndexFact) (c : PointClaim ι) (l : Nat) (entry : State) (store : Store)
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
    let k' := HeapKnowledge.withElements (HeapKnowledge.observeTyped G Γ k 0 o)
    let inverse : Std.HashMap Nat Nat := table.fold (fun acc nm s => acc.insert s nm) {}
    applyDelta store pairs k' false fun i => (inverse.get? i).orElse fun _ => names[i]?
  | none, some q =>
    let (k, pairs, table) := materialize { names := pushedNames, store } (width + 1) [0] false
    let k' := HeapKnowledge.withElements (HeapKnowledge.promoteTruthy k 0 q)
    let inverse : Std.HashMap Nat Nat := table.fold (fun acc nm s => acc.insert s nm) {}
    applyDelta store pairs k' false fun i => (inverse.get? i).orElse fun _ => pushedNames[i]?
  | none, none => store

/-- What an edge into a node other than a loop head carries, from the
source's names `names` on the edge and its store: the target's names (the
mapping applied), the store without the names the edge drops
(`droppedBy`, and an unpushed result no slot holds), the fresh names it
keeps (the result where pushed and fresh), and the implications naming no
dropped name. -/
def edgeTransfer (names : List Nat) (m : PointClaims.Mapping) (pushed isHandler outFresh : Bool) (entry : State)
    (result : Nat) (edgeStore : Store) (implies : List (PromiseCalls.Implication ι)) :
    State × List (PromiseCalls.Implication ι) :=
  let targetNames := timedKind "edge names" fun _ => mapNames names m
  let gone := timedKind "edge dropped" fun _ => droppedBy names m targetNames ++
    (if !pushed && !entry.names.contains result then [result] else [])
  let freshOut := (if pushed && !isHandler && outFresh && !entry.fresh.contains result then result :: entry.fresh
    else entry.fresh).filter (!gone.contains ·)
  let carried := timedKind "edge implications" fun _ => (keepFirst {} (implies.filter fun x =>
    !gone.contains x.test && !gone.contains x.target)).2.toList
  ({ names := targetNames, store := edgeStore.drop gone, fresh := freshOut }, carried)

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

/-- The merge of the states `preds` entering a node of context `context`
through the edges `edgesIn` (each as the search's merge reads it), its
fresh names from `fresh`: the names, the facts every predecessor holds and
those a join keeps, the fresh stores, the implications. -/
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
      ((timedKind "merge diff" fun _ => Store.diff met0 st.store).2.filter fun a => !a.names.any m.contains) ++
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
  -- store separation; each kept where every predecessor's facts entail it.
  let tags : List HeapKnowledge.GuardTag := [.null, .undef]
  let tagged := diffs.flatMap fun d => d.filterMap fun a => match a with
    | .value f => if tags.any (fun g => HeapKnowledge.guardTags { values := [f] } f.slot [] g) then some f.slot else none
    | _ => none
  let seeds := (diffs.flatMap fun d => d.flatMap fun a => match a with
    | .index ⟨.guarded .., _, _⟩ | .index ⟨.storeApart .., _, _⟩ | .link _ => a.names
    | _ => [])
  let seeds := if tagged.isEmpty then seeds else seeds ++ tagged ++
    (diffs.flatMap fun d => d.flatMap fun a => if a.names.any tagged.contains then a.names else [])
  let seedSlots := (keepFirst {} (seeds.filterMap mergedNames.idxOf?)).2.toList
  let guarded : List HeapKnowledge.IndexAtom := if seedSlots.isEmpty then [] else Id.run do
    let projections := views.map fun ps => (materialize ps width seedSlots false).1
    let common := (materialize { names := mergedNames, store := met0 } width seedSlots false).1
    let lowered := projections.map fun (p : Knowledge) =>
      { p with indices := p.indices ++ ((HeapKnowledge.lowerGuards p.links p.indices).filter (!p.indices.contains ·)) }
    let joined := timedKind "meet guarded" fun _ => CertificateProducer.joinGuarded lowered common
    let tagged := timedKind "meet tagged" fun _ =>
      let nullish := ((projections.flatMap fun (o : Knowledge) => o.values.flatMap fun f =>
        (tags.filter fun g => HeapKnowledge.guardTags o f.slot [] g).flatMap fun g =>
          (HeapLinks.aliases o.links f.slot).map (·, g))).eraseDups
      if nullish.isEmpty then [] else
      let candidates := (projections.flatMap fun (p : Knowledge) => p.indices.flatMap fun a =>
        if a.cond.isSome || common.indices.contains a then [] else match a.fact with
        | .guarded .. => []
        | F => (nullish.filter fun (z, _) => F.slots.contains z).map fun (z, g) =>
            ({ fact := .guarded z [] g F } : HeapKnowledge.IndexAtom)).eraseDups
      candidates.filter fun a => projections.all fun (p : Knowledge) =>
        HeapKnowledge.indicesCheckWith (HeapKnowledge.guardTags p) (HeapLinks.aliases p.links) p.links
          p.indices [a] none
    return joined ++ tagged
  met := guarded.foldl (fun (acc : Store) x => match (Atom.index x).rename (mergedNames[·]?) with
    | some a => acc.add a
    | none => acc) met
  -- A name holds a fresh store where every predecessor's does.
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
    | .var i => if (c.context[i]?).any (· == c.type) && (IndexWrites.litSlot G c.context i).isNone then
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
    -- A construction reads every fact: its result's facts (a typed array's
    -- view length) follow from facts its operands' names do not reach.
    let wholeStep := match node.expression with | .construct .. => true | _ => false
    -- A test, a conditional or a read of a slot reads the facts over its
    -- names and their aliases; a step that may need an entailment over
    -- them also reads the linear facts they chain through.
    let (k, pairs, table) := materialize entry width ms wholeStep
    let kE := KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G c.context) k
    let own := (keepFirst {} (c.type :: ms.filterMap fun i => c.context[i]?)).2.toList
    let j : Sequent ι := ⟨c.context, node.expression, c.type⟩
    let kindKey := SinglePassStats.termKind node.expression
    -- Each precondition the call's signatures state, decided once, where the
    -- search first asks it (`admitsNear`).
    let stated : List ((Option CallEffects.ElemPred × List HeapKnowledge.IndexFact) × Thunk Bool) :=
      own.foldl (fun acc F => match PositiveRules.expand G F with
        | [PositiveNormalization.Clause.arrs L _] | [PositiveNormalization.Clause.callable _ _ L _ _] => L.foldl (fun acc p =>
            let key := (p.effect.requires, p.effect.pre)
            if acc.any (·.1 == key) then acc
            else acc ++ [(key, Thunk.mk fun _ => admitsNear kE p.effect node.expression)]) acc
        | _ => acc) []
    let admits := fun (eff : CallEffects.Effect) (t : Tm) =>
      if t == node.expression then
        match stated.find? (·.1 == (eff.requires, eff.pre)) with
        | some (_, v) => v.get
        | none => admitsNear kE eff t
      else admitsNear kE eff t
    -- A call of a slot: its derivation read off the callee's signatures
    -- (`directCall`), its step `ordinary`; otherwise the search.
    let (direct, a0) := match node.expression with
      | .invoke .. => timedKind "direct call" fun _ => directCall G images c.context node.expression c.type admits undefTy answers
      | _ => (none, answers)
    answers := a0
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
    answers := a
    stats := { stats with rules := stats.rules + 1, directCalls := stats.directCalls + (if direct.isSome then 1 else 0) }
    let some (deriv, effect, searched) := r.value | return (.error s!"expression at node {l}: {(reprStr node.expression).take 300} with {(atomsOf k).length} facts {(reprStr k).take 1500}", stats, answers)
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
    -- A call keeping the heap (`PromiseCalls.keepsCall`), where no layer
    -- before it in `Checker.ordinary` decides the step, keeps every fact
    -- it does not name: its output over the facts it names is its delta.
    -- A call whose output keeps every heap fact it does not name, as the
    -- layers of `Checker.ordinary` decide it, outermost first: one
    -- promising its receiver's elements (`elementsCall`), one at a
    -- precondition whose effect keeps the heap (`requiresCall`), one
    -- allocating its result (`freshCall`), else one keeping the heap
    -- (`keepsCall`) that changes no receiver's own locations (`ownCall`).
    let keepsHeap := match effect with
      | .ordinary p =>
        (PromiseCalls.elementsCall G images j effect codes sums).isSome ||
        (if PromiseCalls.requiresCall G images j kE effect codes sums then
          (ExpressionEffects.selectedEffect p).any PromiseCalls.keepsHeap
        else PromiseCalls.freshCall G images j effect codes sums ||
          ((PromiseCalls.ownCall G images j effect codes sums).isNone &&
            PromiseCalls.keepsCall G images j effect codes sums))
      | _ => false
    let preserving := keepsHeap || match effect with
      | .ordinary _ | .written .. | .boundedWrite .. => false
      | _ => true
    -- A slot's read is that slot's value: it keeps its name.
    match node.expression, entry.names[(match node.expression with | .var i => i | _ => 0)]? with
    | .var _, some x => result := x
    | _, _ =>
      result := fresh
      fresh := fresh + 1
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
      let kE := KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G c.context) k
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
      stepK := kE
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
    (argSlots : List Nat) (inputSlots : List (Nat × Nat)) (implies : List (PromiseCalls.Implication ι)) :
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
  ({ names, store }, implies.filterMap (fun x => do pure ⟨← f x.test, ← f x.target, x.type⟩), next)

/-- The pass over one graph. -/
def run (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (inputs : List (Ty ι)) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List IndexAtom)) (entryIndices : List IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (passChecker : PassChecker G images)
    (answers : Answered G) (reference : Array Knowledge := #[]) (debugNode : Nat := 1000000000)
    (bound : Option (Footprints.Closed × Bool × Bool) := none)
    (givenImplies : Array (List (PromiseCalls.Implication ι)) := #[])
    (givenArgs : Array (List Nat) := #[])
    (ensures : List HeapKnowledge.IndexFact := []) (givenInputs : Array (List (Nat × Nat)) := #[])
    (entrySeparation : HeapSeparation.Separation := {}) (observe : Option Nat := none) (tracing : Bool := false) (observeEntry : Bool := false)
    (regional : Option Regional := none) : Outcome ι × Counts × Answered G × Trace := Id.run do
  let nodes := P.toArray
  let claimed := claims.toArray
  let n := nodes.size
  let mut answers := answers
  let edgeCount := nodes.foldl (fun acc node => acc + (successors node.continuation).length + node.handler.toList.length) 0
  let mut counts : Counts := { nodes := n, edges := edgeCount }
  let mut trace : Trace := {}
  if claimed.size != n then return (.notHandled "claim count", counts, answers, trace)
  let index := KnownIndex.of known
  -- The type of `undefined` alone, among the pool's: a call's omitted
  -- receiver is read at it.
  let undefTy := pool.find? fun B => match PositiveRules.expand G B with
    | [PositiveNormalization.Clause.undef] => true
    | _ => false
  -- The loop heads (`loopHeads`). A statement entry that is no loop head is
  -- an ordinary node.
  let (loopHeads, reached) := SinglePass.loopHeads nodes start
  let _ := cuts
  let isHead : Array Bool := if start < n then loopHeads.set! start true else loopHeads
  let stated := byLabel n assertions
  if tracing then
    let e : Array (Option State) := Array.replicate n none
    let ms : Array (List (Nat × State × Std.HashMap Nat (List Nat))) := Array.replicate n []
    let sg : Array (Option Nat) := Array.replicate n none
    trace := Trace.mk e e ms sg isHead start 0 none [] [] []
  let supplied := byLabel n candidates
  -- The entry, which no edge checks on the first invocation.
  if let some why := entryRefusal G inputs claims start goal (stated.getD start none) ((supplied.getD start none).getD [])
      ((givenImplies[start]?).getD []) ((givenArgs[start]?).getD []) ((givenInputs[start]?).getD [])
      entryIndices entrySeparation then
    return (.refused why, counts, answers, trace)
  -- In-degrees without the edges into cuts, of the edges from nodes the
  -- start reaches: a node no path from the start reaches never runs.
  let mut indeg : Array Nat := Array.replicate n 0
  for (node, l) in nodes.zipIdx do
    if reached[l]! then
      for t in successors node.continuation ++ node.handler.toList do
        if t.label < n && !isHead[t.label]! then indeg := indeg.modify t.label (· + 1)
  let merging : Array Bool := indeg.map (· > 1)
  let mut fresh := 0
  -- Under a footprint bound, the region from which no normal return is
  -- possible (`GraphCode.inferDead`), refined from every node.
  let deadArr : Array Bool := match bound with
    | some (_, _, false) =>
      let flags := (nodes.zip claimed).map fun (node, c) => (node, ExpressionEffects.emptyType G c.type)
      GraphCode.deadIterate flags (n + 1) (Array.replicate n true)
    | _ => #[]
  -- The states entering each node, one per predecessor.
  let mut incoming : Array (List State) := Array.replicate n []
  -- Under a regional check, the regional facts each edge into a label
  -- establishes.
  let mut regionIn : Array (List RegionState) := Array.replicate n []
  -- Where each incoming state came from, kept only where observed.
  let mut incomingFrom : Array (List Nat) := Array.replicate n []
  -- Beside each entering state, the implications its edge carries, over
  -- names (`PromiseCalls.Implication`: where the test holds `true`, the
  -- target has the type).
  let mut incomingImpl : Array (List (List (PromiseCalls.Implication ι))) := Array.replicate n []
  -- Into a merge, each edge as the search's merge reads it
  -- (`CertificateProducer.meetImplications`): its context refined by the
  -- source's yields, its implications at the source's slots, its mapping.
  let mut incomingEdges : Array (List (List (Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping)) :=
    Array.replicate n []
  let mut queue : List Nat := []
  -- The given invariant of each head, at its slots: its written assertion
  -- and the claims' facts there.
  let mut given : Array (Option Knowledge) := Array.replicate n none
  for l in List.range n do
    if isHead[l]! then
      -- The start assumes the request's entry facts: its index facts and
      -- the separation of its inputs (`startWritten`, `startGiven`).
      let written : Knowledge := if l == start then startWritten stated[l]! entryIndices entrySeparation
        else (stated[l]!).getD {}
      let claimsFacts := (supplied[l]!).getD []
      counts := { counts with
        givenWritten := counts.givenWritten + (atomsOf written).length
        givenClaims := counts.givenClaims + claimsFacts.length }
      given := given.set! l (some (if l == start then startGiven stated[l]! entryIndices entrySeparation claimsFacts
        else { written with indices := written.indices ++ claimsFacts }))
  for l in List.range n do
    if reached[l]! && indeg[l]! == 0 && (isHead[l]! || l == start) then queue := queue ++ [l]
  let mut visitedAll := 0
  -- The start's names, fixed before any node is visited (a cut may be
  -- visited before it), and the name of the input a promise goal is about.
  let startWidth := ((claimed[start]?).map (·.context.length)).getD 0
  let startNames := (List.range startWidth).map (· + fresh)
  fresh := fresh + startWidth
  let argName : Option Nat := goal.slot.bind fun sl => startNames[sl]?
  -- Per node, whether no environment meets its context, known from its
  -- first entering edge.
  let mut unsat : Array (Option Bool) := Array.replicate n none
  let mut lastStamp := 0
  let mut lastKind := ""
  while true do
    let some l := queue.head? | break
    -- Measuring: the previous node's time, with its edges, by its kind.
    lastStamp := clock lastKind lastStamp l
    queue := queue.tail
    visitedAll := visitedAll + 1
    let node := nodes[l]!
    let c := claimed[l]!
    let width := c.context.length
    -- Whether no environment meets the node's context.
    let here ← match unsat[l]! with
      | some u => pure u
      | none => pure (ControlFlow.unsatisfiable G c.context)
    -- The node's entry state: given at a head, its one predecessor's, or
    -- the meet of its predecessors'.
    let mut entry : State := { names := [] }
    let mut implies : List (PromiseCalls.Implication ι) := []
    -- At a merge observed, each predecessor's state at the merge's slots.
    let mut predViews : List (Nat × Knowledge) := []
    let mut predNames : List (List Nat) := []
    match given[l]! with
    | some g =>
      let (st, imp, fr) := headEntry g (l == start) width fresh startNames argName ((givenArgs[l]?).getD [])
        ((givenInputs[l]?).getD []) ((givenImplies[l]?).getD [])
      entry := st
      implies := imp
      fresh := fr
      counts := { counts with givenImplies := counts.givenImplies + implies.length }
    | none => match incoming[l]! with
      | [s] =>
        entry := s
        if tracing then trace := { trace with single := trace.single.set! l (incomingFrom[l]!).head? }
        implies := (incomingImpl[l]!).headD []
      | [] => pure ()
      | s :: rest =>
        let mg := mergeState G c.context (s :: rest) incomingEdges[l]! fresh
        fresh := mg.fresh
        counts := { counts with merges := counts.merges + 1, mergeDiffs := counts.mergeDiffs + mg.diffCount }
        if observe == some l then
          predViews := incomingFrom[l]!.zip (mg.views.map fun ps => (materialize ps width (List.range width) true).1)
          predNames := mg.state.names :: (s :: rest).map (·.names)
        if tracing then
          trace := { trace with merges := trace.merges.set! l ((incomingFrom[l]!).zip (mg.views.zip mg.renames)) }
        entry := mg.state
        implies := mg.implies
    if tracing then
      let focus := ((mentioned 0 node.expression).getD []).filterMap (entry.names[·]?)
      trace := { trace with entries := trace.entries.set! l (some entry), node := l, edge := none, names := fresh :: entry.names, focus }
    counts := { counts with
      visited := counts.visited + 1, storeMax := max counts.storeMax entry.store.size
      stateSum := counts.stateSum + entry.store.size, heads := counts.heads + (if isHead[l]! then 1 else 0) }
    -- Debugging: the facts a reference certificate holds here that this
    -- state does not entail.
    if let some old := reference[l]? then
      if !isHead[l]! then
        let (k, _, _) := materialize entry width (List.range width) true
        let ctx := KnowledgeExpand.ctxOf G c.context
        let missingCells := old.cells.filter fun f => !KnowledgeExpand.checkIn ctx k { cells := [f] } none
        if !missingCells.isEmpty then
          return (.refused s!"reference: node {l} lacks cells {reprStr missingCells}", counts, answers, trace)
        let missing := old.indices.filter fun a => !KnowledgeExpand.checkIn ctx k { indices := [a] } none
        if !missing.isEmpty then
          return (.refused s!"reference: node {l} lacks {reprStr missing}", counts, answers, trace)
    -- A written assertion, established on every edge into a node other than
    -- a head, holds there: its facts join the state.
    if !isHead[l]! then
      if let some req := stated[l]! then
        let f := fun (i : Nat) => entry.names[i]?
        entry := { entry with store := (atomsOf req).foldl (fun s a => match a.rename f with
          | some b => s.add b | none => s) entry.store }
    -- Observing a node whose step is refused: its state on entry alone.
    if observeEntry && observe == some l then
      let before := (materialize entry width (List.range width) true).1
      let o : Observation ι := { label := l, before, after := before, preds := predViews, names := predNames, implies := slotImplOf entry.names implies }
      return (.observed o, counts, answers, trace)
    -- The step.
    let some ms := timedKind "node mentioned" fun _ => mentioned 0 node.expression | return (.notHandled s!"term at node {l}: {(reprStr node.expression).take 200}", counts, answers, trace)
    let ms := (keepFirst {} ms).2.toList
    let (stepped, stats, a) := checkedStep G images pool fuel suggestions index codes aliases passChecker undefTy
      l node c entry ms fresh answers
    answers := a
    counts := { counts with
      rules := counts.rules + stats.rules, fullRules := counts.fullRules + stats.fullRules
      directCalls := counts.directCalls + stats.directCalls, copies := counts.copies + stats.copies }
    let st ← match stepped with
      | .ok st => pure st
      | .error why => return (.refused why, counts, answers, trace)
    lastKind := if (given[l]!).isSome then "node: head" else if (incoming[l]!).length > 1 then "node: merge"
      else if st.copied then "node: copy" else "node: step"
    fresh := st.fresh
    let store := st.store
    let result := st.result
    let stepK := st.stepK
    let stepOut := st.stepOut
    let stepDeriv := st.stepDeriv
    let stepEffect := st.stepEffect
    let pushedNames := result :: entry.names
    if tracing then
      let st : State := { entry with names := pushedNames, store := store }
      trace := { trace with afters := trace.afters.set! l (some st), names := pushedNames, focus := result :: trace.focus }
    if observe == some l then
      let before := (materialize entry width (List.range width) true).1
      let after := (materialize { entry with names := pushedNames, store := store } (width + 1) (List.range (width + 1)) true).1
      let o : Observation ι := { label := l, before, after, preds := predViews, names := predNames, implies := slotImplOf entry.names implies }
      return (.observed o, counts, answers, trace)
    -- Whether the result holds a fresh store: a copy of a fresh slot, or a
    -- call at a selected signature stating a fresh result (`GraphCode.varFresh`,
    -- `callFresh`).
    let deriv := stepDeriv.getD (.node ⟨c.context, node.expression, c.type⟩ .var [])
    let outFresh := (match node.expression with
      | .var i => (entry.names[i]?).any entry.fresh.contains
      | _ => false) ||
      ((match ExpressionEffects.selectedEffect deriv with | some eff => eff.fresh | none => false) &&
        ExpressionEffects.selectedOperands deriv && (ProgramCertificates.claim deriv).term == node.expression)
    -- The footprint bound at this node (`GraphCode.nodeChecked`).
    if let some (Φ, ret, exc) := bound then
      if deadArr.getD l false then
        if !(GraphCode.deadNode G deadArr.toList node ⟨none, some ⟨c.context, node.expression, c.type⟩, [], {}, none, {}, none, [], [], [], none⟩ && !exc) then
          return (.outsideBound l, counts, answers, trace)
      else
        let F := match PromiseCalls.receiverSlot node.expression with
          | some i => if (entry.names[i]?).any entry.fresh.contains then [i] else []
          | none => []
        let liveHandler := match node.handler with
          | some t => !deadArr.getD t.label false
          | none => false
        if !footprintCheck G images codes answers.summaries.toList Φ F c node stepK deriv liveHandler exc ret outFresh then
          return (.outsideBound l, counts, answers, trace)
    -- The step's yields, computed where an edge's types need them. A read
    -- of a slot yields what the implications testing it state.
    let mut yields : Option (List (PromiseCalls.Yield ι)) := none
    if let .var i := node.expression then
      if let some x := entry.names[i]? then
        let tested := implies.filter (·.test == x)
        if !tested.isEmpty then
          -- At every slot holding a target's name.
          let held := (entry.names.zipIdx).filter fun (nm, _) => tested.any (·.target == nm)
          yields := some (tested.flatMap fun y => (held.filter (·.1 == y.target)).map fun (_, t) =>
            ({ conditional := true, target := t, type := y.type } : PromiseCalls.Yield ι))
    -- The node's implications at its slots, as the search's yields read
    -- them (`produceNode`): a negation's or a copy's yields restate them.
    let slotImpl : Thunk (List (PromiseCalls.Implication ι)) := Thunk.mk fun _ => slotImplOf entry.names implies
    -- Another step's yields (a test's, a promise call's): computed for the
    -- implications its pushed result carries.
    let isRead := match node.expression with | .var _ => true | _ => false
    if yields.isNone && !isRead && !st.copied then
      let e := stepDeriv.getD (.node ⟨c.context, node.expression, c.type⟩ .var [])
      let (ys, a) := timedKind "yields" fun _ => (nodeYields G images pool c.context slotImpl.get e stepOut stepK) answers
      answers := a
      yields := some ys
    -- A handler receives the thrown value in a fresh name, at a type
    -- admitting every value its target states for the slot it lands in, or
    -- the pool's (`produceNodeAt`), under the facts a throw keeps
    -- (`ControlFlow.handlerFacts`: no heap fact).
    let thrownTy : Option (Ty ι) := node.handler.bind fun t => do
      let tc ← claimed[t.label]?
      let landing := (List.range tc.context.length).filterMap fun i =>
        if PointClaims.slot t.mapping i == 0 then tc.context[i]? else none
      (landing ++ pool).find? (ControlFlow.admitsAll G)
    if node.handler.isSome && thrownTy.isNone then return (.refused s!"handler of node {l}", counts, answers, trace)
    let thrown := fresh
    if node.handler.isSome then fresh := fresh + 1
    if let .ret := node.continuation then
      let (refusal, a, queried) := returnCheck G images goal ensures c l entry store result start startNames argName
        (yields.getD []) debugNode answers
      answers := a
      if let some q := queried then
        counts := { counts with queries := counts.queries + 1, queryAtoms := counts.queryAtoms + q }
      if let some why := refusal then return (.refused why, counts, answers, trace)
    -- The edges: target, whether the result is pushed, an observation of
    -- it, and a branch's answer.
    let edges := Exit.ofNode node
    -- The edges' contexts as the step's yields refine them (`produceNodeAt`),
    -- read where a target's assertion is checked on the edge.
    if yields.isNone && edges.any (fun e => !isHead[e.target.label]! && (stated[e.target.label]!).isSome) then
      let e := stepDeriv.getD (.node ⟨c.context, node.expression, c.type⟩ .var [])
      let (ys, a) := (nodeYields G images pool c.context slotImpl.get e stepOut stepK) answers
      answers := a
      yields := some ys
    let ysAll := (yields.getD []).flatMap fun y => match entry.names[y.target]? with
      | some nm => (entry.names.zipIdx.filter (·.1 == nm)).map fun (_, j) => { y with target := j }
      | none => [y]
    let outAll : Thunk Knowledge := Thunk.mk fun _ => KnowledgeExpand.expandLinks (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G c.context) 1) stepOut
    let refinedΓ := fun (first : Bool) =>
      let pushedRefine := fun facts => PromiseCalls.refineBy G (c.type :: c.context)
        (PromiseCalls.aliasFacts outAll.get.links facts 1) 0
      let keptRefine := fun facts => PromiseCalls.refineBy G c.context
        (PromiseCalls.aliasFacts (HeapKnowledge.dropResult outAll.get).links facts 0) 0
      let unconditional := PromiseCalls.yieldFacts ysAll false
      let conditional := PromiseCalls.yieldFacts ysAll true
      match node.continuation with
      | .bind _ => pushedRefine unconditional
      | .effect _ => keptRefine unconditional
      | .branch .. => keptRefine (if first then conditional else unconditional)
      | .branchBind .. => pushedRefine (if first then conditional else PromiseCalls.yieldFacts ysAll false true)
      | .tagBind tg .. => pushedRefine (if first then PromiseCalls.yieldFacts ysAll (ControlFlow.truthyBoolean G tg c.type)
          else unconditional)
      | .ret => c.context
    -- A regional check at this node, as `ArgumentRegionGraph.checkNode`
    -- makes it: its regional facts on entry (the regions' input slots at the
    -- start, a loop head's given ones, else what every edge into it
    -- establishes), the cells and fields it keeps, and on each edge what
    -- the node establishes at the target (a loop head's given facts there).
    if let some rg := regional then
      let here : RegionState := if l == start then
          { facts := ((rg.regions.map fun (x : Footprints.ArgumentStoreRegion) =>
              (⟨x.position, []⟩ : Footprints.ArgumentStoreRegion)).eraseDups).map fun x => ⟨x.position, x⟩ }
        else if isHead[l]! then ((rg.heads[l]?).join).getD {}
        else RegionState.meet (regionIn[l]!)
      let sums := answers.summaries.toList
      let ordinaryEv : Option (OrdinaryEvidence ι) := match stepDeriv, stepEffect with
        | some d, _ => some (.proof d)
        | none, some _ => some .effect
        | none, none => none
      let kHere := (materialize entry width (List.range width) true).1
      let cEv : NodeEvidence ι := ⟨ordinaryEv, some ⟨c.context, node.expression, c.type⟩, [], kHere, stepEffect, {}, none, [], [], [], none⟩
      let t0 := node.expression
      let F := here.values
      let C := if GraphCode.ArgumentRegionGraph.cellsKept G images sums rg.Φ F here.cells cEv t0 node.handler.isSome
        then here.cells else []
      let Fs := here.fields.filter fun p =>
        HeapExpressionRules.stableFirst G c.context p.1 p.2 || GraphCode.ArgumentRegionFresh.nullishSlot G c.context p.1
      let origins := GraphCode.ArgumentRegionGraph.nodeOrigins rg.regions here.facts t0
      let pushes := GraphCode.pushes node.continuation
      let outR := if pushes then GraphCode.ArgumentPathTracking.afterPush here.facts origins else here.facts
      let outF := GraphCode.ArgumentRegionGraph.freshOut G images sums F C cEv t0
      let outC := GraphCode.ArgumentRegionGraph.cellOut F C t0
      let outFs := GraphCode.ArgumentRegionGraph.fieldOut rg.names F Fs t0
      let established := fun (t : Target) (handler : Bool) => Id.run do
        let w := ((claimed[t.label]?).map (·.context.length)).getD 0
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
        return ({ facts, values, cells, fields } : RegionState)
      let targets := (successors node.continuation).map (·, false) ++ node.handler.toList.map (·, true)
      let mut at_ : List (Nat × RegionState) := [(l, { here with cells := C, fields := Fs })]
      for (t, h) in targets do
        let e := established t h
        if isHead[t.label]! then at_ := at_ ++ [(t.label, ((rg.heads[t.label]?).join).getD {})]
        else
          at_ := at_ ++ [(t.label, e)]
          regionIn := regionIn.modify t.label (e :: ·)
      let table := sparse n [] (at_.map fun (x, r) => (x, r.facts))
      let ft : GraphCode.ArgumentRegionFresh.FreshTables := ⟨sparse n [] (at_.map fun (x, r) => (x, r.values)),
        sparse n [] (at_.map fun (x, r) => (x, r.cells)), sparse n [] (at_.map fun (x, r) => (x, r.fields)), rg.names⟩
      if !(timedKind "regional node" fun _ => GraphCode.ArgumentRegionGraph.checkNode G images sums rg.Φ rg.regions table ft rg.exc l node cEv) then
        return (.refused s!"store regions at node {l}", counts, answers, trace)
    let mut edgeIndex := 0
    for ex in edges do
      let t := ex.target
      let pushed := ex.pushed
      let observed := ex.observed
      let promote := ex.promote
      let isHandler := ex.isHandler
      let first := edgeIndex == 0
      edgeIndex := edgeIndex + 1
      if tracing then trace := { trace with edge := some t.label }
      let some tc := claimed[t.label]? | return (.refused s!"edge from {l}", counts, answers, trace)
      let Γ := if isHandler then thrownTy.getD [] :: c.context else if pushed then c.type :: c.context else c.context
      let names := if isHandler then thrown :: entry.names else if pushed then pushedNames else entry.names
      -- The edge's own facts: an observation of the result; a throw's, the
      -- entry's facts no heap change affects.
      let edgeStore := edgeStoreOf G Γ entry.store store names pushedNames width pushed isHandler observed promote
      -- The slots' types: each the target's, or below it.
      -- Whether no environment meets the edge's context: the node's own
      -- context's answer, and the pushed result's type.
      let unsatΓ := here || (if isHandler then ControlFlow.unsatisfiable G [thrownTy.getD []]
        else pushed && ControlFlow.unsatisfiable G [c.type])
      let vacuous := match observed with
        | some o => unsatΓ || (Γ[0]?).any (BranchRefinement.impossible G · o)
        | none => unsatΓ
      let diff := if vacuous then [] else timedKind "edge types" fun _ => differing Γ tc.context t.mapping
      -- The target's own answer: a slot of the empty type is one the edge's
      -- context gives (where it has none) or a slot whose type differs.
      if (unsat[t.label]!).isNone then
        let u := if unsatΓ then ControlFlow.unsatisfiable G tc.context
          else diff.any fun (i, _) => (tc.context[i]?).any fun B => ControlFlow.unsatisfiable G [B]
        unsat := unsat.set! t.label (some u)
      if !vacuous then
        let mut ok := true
        for (i, s) in diff do
          match Γ[s]?, tc.context[i]? with
          | some A, some B =>
            if observed.isNone || s != 0 then
              let (r, a) := subtypeUsing G images A B answers
              answers := a
              if r.value.isNone then ok := false
            else ok := false
          | _, _ => ok := false
        if !ok then
          -- The edge as the search reads it, its observation included.
          counts := { counts with edgeSearches := counts.edgeSearches + 1 }
          let (ko, _, _) := materialize { names, store := edgeStore } (if pushed then width + 1 else width)
            (0 :: diff.map (·.2)) false
          -- Its links restated on every slot of their classes, as an edge reads
          -- a node's output (`ControlFlow.outFacts`).
          let ko := KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G Γ) ko
          let (found, a) := timedKind "edge search" fun _ => checkedEdge G images claimed tc.context Γ t observed ko answers
          answers := a
          if !found && isHandler then
            return (.refused s!"handler edge from node {l} to node {t.label}", counts, answers, trace)
          if !found then
            -- The edge's context as the step's yields refine it
            -- (`produceNodeAt`): what a test or a promise establishes.
            let ys ← match yields with
              | some ys => pure ys
              | none =>
                let e := stepDeriv.getD (.node ⟨c.context, node.expression, c.type⟩ .var [])
                let (ys, a) := (nodeYields G images pool c.context slotImpl.get e stepOut stepK) answers
                answers := a
                pure ys
            yields := some ys
            -- Each yield restated at every slot holding its target's name, as
            -- the alias links of a positional state relate them.
            let ys := ys.flatMap fun y => match entry.names[y.target]? with
              | some nm => (entry.names.zipIdx.filter (·.1 == nm)).map fun (_, j) => { y with target := j }
              | none => [y]
            let outL := outAll.get
            let pushedRefine := fun facts => PromiseCalls.refineBy G (c.type :: c.context)
              (PromiseCalls.aliasFacts outL.links facts 1) 0
            let keptRefine := fun facts => PromiseCalls.refineBy G c.context
              (PromiseCalls.aliasFacts (HeapKnowledge.dropResult outL).links facts 0) 0
            let unconditional := PromiseCalls.yieldFacts ys false
            let conditional := PromiseCalls.yieldFacts ys true
            let first := t == (successors node.continuation).headD t
            let Γ' := match node.continuation with
              | .bind _ => pushedRefine unconditional
              | .effect _ => keptRefine unconditional
              | .branch .. => keptRefine (if first then conditional else unconditional)
              | .branchBind .. => pushedRefine (if first then conditional else PromiseCalls.yieldFacts ys false true)
              | .tagBind tg .. => pushedRefine (if first then PromiseCalls.yieldFacts ys (ControlFlow.truthyBoolean G tg c.type)
                  else unconditional)
              | .ret => Γ
            let (found, a) := checkedEdge G images claimed tc.context Γ' t observed outL answers
            answers := a
            -- A slot whose refined type the target's does not admit read at
            -- its unrefined type: both are types of its value (an alias
            -- refined through an array's invariant element type).
            let mut found := found
            if !found then
              let mut mixed : Array (Ty ι) := #[]
              for (A', s) in Γ'.zipIdx do
                let A := (Γ[s]?).getD A'
                let reads := (List.range tc.context.length).filter fun i => PointClaims.slot t.mapping i == s
                let mut fits := true
                for i in reads do
                  if fits then
                    match tc.context[i]? with
                    | some B =>
                      if !same A' B then
                        let (res, a') := subtypeUsing G images A' B answers
                        answers := a'
                        if res.value.isNone then fits := false
                    | none => pure ()
                mixed := mixed.push (if fits then A' else A)
              let Γm := mixed.toList
              if Γm != Γ' then
                let (found', a) := checkedEdge G images claimed tc.context Γm t observed outL answers
                answers := a
                found := found'
            if !found then return (.refused s!"edge from node {l} to node {t.label}{if l == debugNode then s!" fields {reprStr (readFields ko 0)} links {reprStr ko.links} diff {reprStr diff} implies {reprStr (implies.map fun x => (x.test, x.target))} names {reprStr (entry.names.take 6)} yields {reprStr ((yields.getD []).map fun y => (y.target, y.conditional))}" else ""}", counts, answers, trace)
      -- The edge's implications: the entry's, and on a pushed edge those the
      -- result's conditional yields state of it.
      let freshImpl : List (PromiseCalls.Implication ι) := if !pushed || isHandler then [] else
        ((yields.getD []).filterMap fun y => if y.conditional && !y.onFalse then
          (entry.names[y.target]?).map fun tgt => ⟨result, tgt, y.type⟩ else none)
      if isHead[t.label]! then
        -- The head's given implications hold on every edge into it.
        if !vacuous then
          for x in (givenImplies[t.label]?).getD [] do
            let nt := names[PointClaims.slot t.mapping x.test]?
            let na := names[PointClaims.slot t.mapping x.target]?
            let held := (implies ++ freshImpl).filter fun y => some y.test == nt && some y.target == na
            let mut ok := false
            for y in held do
              if !ok then
                if same y.type x.type then ok := true
                else
                  let (res, a') := subtypeUsing G images y.type x.type answers
                  answers := a'
                  if res.value.isSome then ok := true
            if !ok then return (.refused s!"edge from node {l} into statement entry {t.label}: an implication", counts, answers, trace)
        -- The slots it states hold the promised input, or an input's entry
        -- value, hold it on every edge.
        if !vacuous then
          for (j, q) in (givenInputs[t.label]?).getD [] do
            if names[PointClaims.slot t.mapping j]? != startNames[q]? then
              return (.refused s!"edge from node {l} into statement entry {t.label}: an input's value", counts, answers, trace)
          for j in (givenArgs[t.label]?).getD [] do
            if names[PointClaims.slot t.mapping j]? != argName then
              return (.refused s!"edge from node {l} into statement entry {t.label}: the promised input", counts, answers, trace)
        -- The head's given state is entailed on every edge into it.
        let some req := given[t.label]! | return (.refused s!"head {t.label}", counts, answers, trace)
        let slots := (atomsOf req).flatMap Atom.names
        let srcSlots := slots.map (PointClaims.slot t.mapping)
        let (k, _, _) := materialize { names, store := edgeStore } (if pushed then width + 1 else width) srcSlots true
        counts := { counts with queries := counts.queries + 1, queryAtoms := counts.queryAtoms + (atomsOf k).length }
        if !vacuous && !(timedKind "head query" fun _ => KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context)
            (HeapKnowledge.withTypedLinks G Γ (ControlFlow.withTypedCells G Γ req t.mapping k)) req t.mapping) then
          -- The given facts the edge does not establish, named.
          let ctx := KnowledgeExpand.ctxOf G tc.context
          let src := HeapKnowledge.withTypedLinks G Γ (ControlFlow.withTypedCells G Γ req t.mapping k)
          let missing := (atomsOf req).filter fun a => !KnowledgeExpand.checkIn ctx src (ofAtoms [a] tc.context.length) t.mapping
          if tracing then
            trace := { trace with missing := missing.filterMap fun a => a.rename fun i => names[PointClaims.slot t.mapping i]? }
          return (.refused s!"edge from node {l} into statement entry {t.label}: lacks {(reprStr (missing.map fun a => match a with | .index x => reprStr x | .cell f => s!"cell {f.slot}" | .value f => s!"value {f.slot}" | .link g => s!"link {g.cell} {g.value}" | .elem e => s!"elems {e.slot}" | .sep f => s!"sep {f.slot}")).take 1500}", counts, answers, trace)
      else
        -- A target's assertion established on the edge, as the edge test
        -- into a statement entry establishes it (`checkTargetResult`): over the
        -- edge's facts, its context as the yields refine it, with the facts
        -- that context's types state of the cells and links it reads.
        if let some req := stated[t.label]! then
          if !vacuous then
            let Γe := if isHandler then Γ else refinedΓ first
            let slots := (atomsOf req).flatMap Atom.names
            let srcSlots := slots.map (PointClaims.slot t.mapping)
            let (k, _, _) := materialize { names, store := edgeStore } (if pushed then width + 1 else width) srcSlots false
            let k := match observed with
              | some o => HeapKnowledge.observeTyped G Γe (ControlFlow.withTypedCells G Γe req t.mapping k) 0 o
              | none => HeapKnowledge.withTypedLinks G Γe (ControlFlow.withTypedCells G Γe req t.mapping k)
            counts := { counts with queries := counts.queries + 1, queryAtoms := counts.queryAtoms + (atomsOf k).length }
            if !KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context) k req t.mapping then
              let missing := (atomsOf req).filter fun a =>
                !KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context) k (ofAtoms [a] tc.context.length) t.mapping
              if tracing then
                trace := { trace with missing := missing.filterMap fun a => a.rename fun i => names[PointClaims.slot t.mapping i]? }
              return (.refused s!"edge from node {l} into node {t.label}: its assertion lacks {(missing.map fun a => match a with | .index x => (reprStr x.fact).take 80 | .cell f => s!"cell {f.slot}.{f.field}" | .value f => s!"value {f.slot}" | .link g => s!"link {g.cell}.{g.field}={g.value}" | .elem e => s!"elems {e.slot}" | .sep f => s!"sep {f.slot}").take 4}", counts, answers, trace)
        let (target, carried) := edgeTransfer names t.mapping pushed isHandler outFresh entry result edgeStore
          (implies ++ freshImpl)
        incoming := incoming.modify t.label (target :: ·)
        if observe == some t.label || tracing then incomingFrom := incomingFrom.modify t.label (l :: ·)
        incomingImpl := incomingImpl.modify t.label (carried :: ·)
        if merging[t.label]! then
          let Γe := if isHandler then Γ else refinedΓ first
          let slotsOf : Std.HashMap Nat (List Nat) := names.zipIdx.foldl (fun acc (x, i) =>
            acc.insert x (i :: acc.getD x [])) {}
          let atSlots := carried.flatMap fun (x : PromiseCalls.Implication ι) =>
            (slotsOf.getD x.test []).flatMap fun i => (slotsOf.getD x.target []).map fun j =>
              (⟨i, j, x.type⟩ : PromiseCalls.Implication ι)
          incomingEdges := incomingEdges.modify t.label ((Γe, atSlots, t.mapping) :: ·)
        indeg := indeg.modify t.label (· - 1)
        if indeg[t.label]! == 0 then queue := t.label :: queue
  let _ := clock lastKind lastStamp visitedAll
  let reachable := (reached.toList.filter id).length
  counts := { counts with reached := reachable }
  if visitedAll < reachable then return (.notHandled s!"{reachable - visitedAll} nodes not reached", counts, answers, trace)
  -- A node no path from the start reaches never runs (`reached` follows
  -- every normal and exceptional edge, so it holds every node a run can
  -- be at): the pass decides nothing of it. The proved layer checks such a
  -- node at its own context all the same (`GraphCode.unreachableEntry`),
  -- which the referee still does.
  return (.accepted, counts, answers, trace)


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
