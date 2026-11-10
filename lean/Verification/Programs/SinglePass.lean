import Verification.Programs.CertificateProducer
import Lean.Data.PersistentHashMap
import Verification.Programs.SinglePassStats

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
  deriving BEq, Hashable

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

/-- The facts a state holds, over names, and by each name the facts that
mention it (removed facts are filtered out where read). -/
structure Store where
  live : Lean.PersistentHashMap Atom Unit := {}
  byName : Lean.PersistentHashMap Nat (List Atom) := {}
  count : Nat := 0

def Store.add (s : Store) (a : Atom) : Store :=
  if s.live.contains a then s else
  { live := s.live.insert a (), count := s.count + 1,
    byName := a.names.foldl (fun m n => m.insert n (a :: m.findD n [])) s.byName }

def Store.remove (s : Store) (a : Atom) : Store :=
  if s.live.contains a then { s with live := s.live.erase a, count := s.count - 1 } else s

def Store.about (s : Store) (n : Nat) : List Atom := (s.byName.findD n []).filter s.live.contains

def Store.size (s : Store) : Nat := s.count

def Store.toList (s : Store) : List Atom := s.live.foldl (fun acc a _ => a :: acc) []

/-- A program point's state: the name at each slot, the facts. -/
structure State where
  names : List Nat
  store : Store := {}

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

private unsafe def timedKindImpl {α : Type} (kind : String) (f : Unit → α) : α :=
  match unsafeIO (do
      let t0 ← IO.monoNanosNow
      let a ← IO.lazyPure f
      let t1 ← IO.monoNanosNow
      kindNanos.modify fun m => let (t, n) := m.getD kind (0, 0); m.insert kind (t + (t1 - t0), n + 1)
      pure a) with
  | .ok a => a
  | .error _ => f ()

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

instance : ToString Counts where
  toString c := s!"visited {c.visited}, rule applications {c.rules} (whole store {c.fullRules}), copies {c.copies}, entailment queries {c.queries} (mean atoms {c.queryAtoms / max c.queries 1}), edge searches {c.edgeSearches}, head facts written {c.givenWritten} + from claims {c.givenClaims}, largest store {c.storeMax}"

/-- The verdict: refused at a located obligation, or a construct the pass
does not handle. -/
inductive Outcome where
  | accepted
  | refused (why : String)
  | notHandled (what : String)

instance : ToString Outcome where
  toString
    | .accepted => "accepted"
    | .refused w => s!"refused: {w}"
    | .notHandled w => s!"not handled: {w}"

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

/-- The knowledge a step reads, at slots: the facts over the names of
`slots` and over the names those facts mention, a name out of scope
eliminated from the linear facts. With `whole`, every fact. The store's
facts with their images, for the step's delta, and the table of slots. -/
def materialize (st : State) (d : Nat) (slots : List Nat) (whole : Bool) :
    Knowledge × List (Atom × Atom) × Std.HashMap Nat Nat := timedKind (if whole then "materialize whole" else "materialize") fun _ =>
  let given := slots.filterMap fun s => st.names[s]?
  let atoms : List Atom := if whole then st.store.toList else Id.run do
    -- The facts over the given names and over every name an alias link
    -- relates to one of them.
    let mut seen : Std.HashSet Nat := given.foldl (·.insert ·) {}
    let mut frontier := given
    let mut kept : Std.HashSet Atom := {}
    let mut out : Array Atom := #[]
    while !frontier.isEmpty do
      let mut next := []
      for x in frontier do
        for a in st.store.about x do
          if !kept.contains a then
            kept := kept.insert a
            out := out.push a
            -- Through an alias link, and through a linear fact: the facts
            -- an entailment over the given names may chain through.
            let through := match a with
              | .link g => [g.cell, g.value]
              | .index x => match x.fact with
                | .linear _ => a.names
                | _ => []
              | _ => []
            for y in through do
              if !seen.contains y then
                seen := seen.insert y
                next := y :: next
      frontier := next
    return out.toList
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
  -- Each of `slots` holding a name a slot before it holds is related to it
  -- by an alias link.
  let aliasLinks := slots.filterMap fun s => do
    let n ← st.names[s]?
    let first ← table.get? n
    if first == s then none else some (Atom.link { cell := first, value := s, alias := true })
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
  for o in outs do
    if !inSet.contains o then
      if let some a := o.rename back then
        -- A link of a name to itself states nothing.
        let trivial := match a with | .link g => g.alias && g.cell == g.value | _ => false
        if !trivial then s := s.add a
  return s

instance : Inhabited Node := ⟨⟨.nul, .ret, none⟩⟩

private unsafe def sameImpl {α : Type} [BEq α] (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b || a == b
/-- `a == b`, answered at once where they are one object. -/
@[implemented_by sameImpl] def same {α : Type} [BEq α] (a b : α) : Bool := a == b

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

/-- The names of a target's slots: the mapping applied to the source's. -/
def mapNames (names : List Nat) (m : PointClaims.Mapping) : List Nat :=
  match m with
  | none => names
  | some slots => Id.run do
    let mut cur := Cursor.of names
    let mut out : Array Nat := Array.mkEmpty slots.length
    for s in slots do
      let (x, c) := cur.get s
      cur := c
      out := out.push (x.getD 0)
    return out.toList

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
    let held : Std.HashSet Nat := target.foldl (·.insert ·) {}
    return (keepFirst {} (skipped.filter (!held.contains ·))).2.toList

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
  for x in derived do
    let a := Atom.index x
    if a.names.all (!dset.contains ·) then s := s.add a
  return s

/-- The index facts of `k` connected to the slots `seeds` through shared
slots (alias links included), transitively: a linear entailment over the
seeds' terms reads only these. -/
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
      for g in k.links do
        if g.alias && (g.cell == x || g.value == x) then
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
    let mut cur := Cursor.of Γ
    let mut out := []
    let mut i := 0
    let mut ss := slots
    for B in Δ do
      match ss with
      | s :: rest =>
        let (A, c) := cur.get s
        cur := c
        if A.all (!same · B) then out := (i, s) :: out
        ss := rest
      | [] => out := (i, 0) :: out
      i := i + 1
    return out

/-- The pass over one graph. -/
def run (G : NormalGraph ι) (images : InstanceImageCheck G) (pool : List (Ty ι)) (fuel : Nat)
    (P : Program) (claims : List (PointClaim ι)) (start : Nat) (goal : Goal ι)
    (assertions : List (Nat × Knowledge)) (cuts : List Nat)
    (candidates : List (Nat × List IndexAtom)) (entryIndices : List IndexAtom)
    (suggestions : List (Sequent ι)) (known : List (ProgramCertificates.Evidence ι)) (codes : CodeEntry ι → Bool)
    (aliases : List (ι × ι)) (checker : HeapExpressionRules.Checker G images)
    (answers : Answered G) (reference : Array Knowledge := #[]) (debugNode : Nat := 1000000000) : Outcome × Counts × Answered G := Id.run do
  let nodes := P.toArray
  let claimed := claims.toArray
  let n := nodes.size
  let mut answers := answers
  let mut counts : Counts := {}
  if claimed.size != n then return (.notHandled "claim count", counts, answers)
  let index := KnownIndex.of known
  let isHead : Array Bool := (cuts ++ [start]).foldl (fun a l => if l < n then a.set! l true else a)
    (Array.replicate n false)
  let stated := byLabel n assertions
  let supplied := byLabel n candidates
  -- In-degrees without the edges into cuts.
  let mut indeg : Array Nat := Array.replicate n 0
  for node in nodes do
    for t in successors node.continuation ++ node.handler.toList do
      if t.label < n && !isHead[t.label]! then indeg := indeg.modify t.label (· + 1)
  let mut fresh := 0
  -- The states entering each node, one per predecessor.
  let mut incoming : Array (List State) := Array.replicate n []
  -- Beside each entering state, the implications its edge carries, over
  -- names (`PromiseCalls.Implication`: where the test holds `true`, the
  -- target has the type).
  let mut incomingImpl : Array (List (List (PromiseCalls.Implication ι))) := Array.replicate n []
  let mut queue : List Nat := []
  -- The given invariant of each head, at its slots: its written assertion
  -- and the claims' facts there.
  let mut given : Array (Option Knowledge) := Array.replicate n none
  for l in List.range n do
    if isHead[l]! then
      let written := (stated[l]!).getD {}
      let written := if l == start then { written with indices := written.indices ++ entryIndices } else written
      let claimsFacts := (supplied[l]!).getD []
      counts := { counts with
        givenWritten := counts.givenWritten + (atomsOf written).length
        givenClaims := counts.givenClaims + claimsFacts.length }
      given := given.set! l (some { written with indices := written.indices ++ claimsFacts })
  for l in List.range n do
    if indeg[l]! == 0 && (isHead[l]! || l == start) then queue := queue ++ [l]
  let mut visitedAll := 0
  -- Per node, whether no environment meets its context, known from its
  -- first entering edge.
  let mut unsat : Array (Option Bool) := Array.replicate n none
  while true do
    let some l := queue.head? | break
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
    match given[l]! with
    | some g =>
      -- A head's state is its given invariant, over fresh names.
      let names := (List.range width).map (· + fresh)
      fresh := fresh + width
      let f := fun (i : Nat) => if i < width then some (i + fresh - width) else none
      entry := { names, store := timedKind "head state" fun _ => (atomsOf g).foldl (fun s a => match a.rename f with
        | some b => s.add b | none => s) {} }
    | none => match incoming[l]! with
      | [s] =>
        entry := s
        implies := (incomingImpl[l]!).headD []
      | [] => pure ()
      | s :: rest =>
        -- Names: a slot whose predecessors' names differ takes a fresh one.
        let width := c.context.length
        let preds := s :: rest
        let arrs := preds.map (·.names.toArray)
        let mut names : Array Nat := Array.mkEmpty width
        let mut renames : List (Std.HashMap Nat Nat) := arrs.map fun _ => {}
        for i in List.range width do
          let ns := arrs.map (·.getD i 0)
          let n0 := ns.headD 0
          if ns.all (· == n0) then names := names.push n0
          else
            names := names.push fresh
            renames := (renames.zip ns).map fun (m, x) => m.insert x fresh
            fresh := fresh + 1
        -- The facts every predecessor holds, renamed.
        let stores : List (Std.HashSet Atom) := (preds.zip renames).map fun ((st : State), (m : Std.HashMap Nat Nat)) =>
          st.store.toList.foldl (fun (acc : Std.HashSet Atom) (a : Atom) =>
            acc.insert ((a.rename fun x => some (m.getD x x)).getD a)) {}
        let first := stores.headD {}
        let met := timedKind "meet" fun _ => first.fold (fun (acc : Store) a =>
          if stores.tail.all (·.contains a) then acc.add a else acc) {}
        entry := { names := names.toList, store := met }
        -- The implications every predecessor carries, renamed, at the
        -- union of their types.
        let renamedImpl : List (List (PromiseCalls.Implication ι)) :=
          ((incomingImpl[l]!).zip renames).map fun ((xs : List (PromiseCalls.Implication ι)), (m : Std.HashMap Nat Nat)) =>
            xs.map fun x => (⟨m.getD x.test x.test, m.getD x.target x.target, x.type⟩ : PromiseCalls.Implication ι)
        match renamedImpl with
        | firstXs :: others =>
          implies := firstXs.filterMap fun (x : PromiseCalls.Implication ι) =>
            if others.all (·.any fun (y : PromiseCalls.Implication ι) => y.test == x.test && y.target == x.target) then
              some ⟨x.test, x.target, (x.type ++ (others.flatMap fun ys => (ys.filter fun (y : PromiseCalls.Implication ι) =>
                y.test == x.test && y.target == x.target).flatMap (·.type))).eraseDups⟩
            else none
          implies := (keepFirst {} implies).2.toList
        | [] => pure ()
    counts := { counts with visited := counts.visited + 1, storeMax := max counts.storeMax entry.store.size }
    -- Debugging: the facts a reference certificate holds here that this
    -- state does not entail.
    if let some old := reference[l]? then
      if !isHead[l]! then
        let (k, _, _) := materialize entry width (List.range width) true
        let ctx := KnowledgeExpand.ctxOf G c.context
        let missing := old.indices.filter fun a => !KnowledgeExpand.checkIn ctx k { indices := [a] } none
        if !missing.isEmpty then
          return (.refused s!"reference: node {l} lacks {reprStr missing}", counts, answers)
    -- A required assertion at a node other than a head is entailed by its
    -- entry state.
    if !isHead[l]! then
      if let some req := stated[l]! then
        let slots := (atomsOf req).flatMap Atom.names
        let (k, _, _) := materialize entry width slots false
        counts := { counts with queries := counts.queries + 1, queryAtoms := counts.queryAtoms + (atomsOf k).length }
        if !KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G c.context) k req none then
          return (.refused s!"assertion at node {l}", counts, answers)
    -- The step.
    let some ms := mentioned 0 node.expression | return (.notHandled s!"term at node {l}: {(reprStr node.expression).take 200}", counts, answers)
    let ms := (keepFirst {} ms).2.toList
    -- A read of a slot whose type is the claim's: the result is that slot's
    -- value, named as it (`HeapExpressionRules.copy`).
    let copied : Option Nat := match node.expression with
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
    match copied with
    | some x =>
      counts := { counts with copies := counts.copies + 1 }
      result := x
    | none =>
      let (k, pairs, table) := materialize entry width ms false
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
      let (r, a) := timedKind (if kindKey == "invoke" then s!"invoke facts {(atomsOf k).length / 10 * 10}" else kindKey) fun _ =>
        expressionEffectUsing G images pool fuel j kE suggestions index codes aliases checker (some own)
          (some admits) answers
      answers := a
      counts := { counts with rules := counts.rules + 1 }
      let some (deriv, effect, out) := r.value | return (.refused s!"expression at node {l}: {(reprStr node.expression).take 300} with {(atomsOf k).length} facts {(reprStr k).take 1500}", counts, answers)
      let preserving := match effect with
        | .ordinary _ | .written .. | .boundedWrite .. => false
        | _ => true
      -- A slot's read is that slot's value: it keeps its name.
      match node.expression, entry.names[(match node.expression with | .var i => i | _ => 0)]? with
      | .var _, some x => result := x
      | _, _ =>
        result := fresh
        fresh := fresh + 1
      if l == debugNode then
        return (.refused s!"debug {l}: effect preserving {preserving}, in {reprStr k}\nout {reprStr out}", counts, answers)
      stepK := kE
      stepOut := out
      stepDeriv := deriv
      if preserving then
        let inverse : Std.HashMap Nat Nat := table.fold (fun acc nm s => acc.insert s nm) {}
        store := applyDelta store pairs out true fun i => if i == 0 then some result else (inverse.get? (i - 1)).orElse fun _ => entry.names[i - 1]?
      else
        -- A step that may write: its rule reads every fact.
        let (k, pairs, table) := materialize entry width ms true
        let kE := KnowledgeExpand.expandLinks (KnowledgeExpand.ctxOf G c.context) k
        -- The step the search selected over the facts the expression names,
        -- its output over every fact.
        let r := timedKind ("whole " ++ SinglePassStats.termKind node.expression) fun _ =>
          checker.select j kE effect codes answers.summaries.toList
        counts := { counts with rules := counts.rules + 1, fullRules := counts.fullRules + 1 }
        let some out := r.value | return (.refused s!"expression at node {l} over every fact", counts, answers)
        stepK := kE
        stepOut := out
        let inverse : Std.HashMap Nat Nat := table.fold (fun acc nm s => acc.insert s nm) {}
        store := applyDelta store pairs out true fun i => if i == 0 then some result else (inverse.get? (i - 1)).orElse fun _ => entry.names[i - 1]?
    let pushedNames := result :: entry.names
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
    -- Another step's yields (a test's, a promise call's): computed for the
    -- implications its pushed result carries.
    let isRead := match node.expression with | .var _ => true | _ => false
    if yields.isNone && !isRead && copied.isNone then
      let e := stepDeriv.getD (.node ⟨c.context, node.expression, c.type⟩ .var [])
      let slotImpl : List (PromiseCalls.Implication ι) := []
      let (ys, a) := (nodeYields G images pool c.context slotImpl e stepOut stepK) answers
      answers := a
      yields := some ys
    if node.handler.isSome then return (.notHandled s!"handler at node {l}", counts, answers)
    if let .ret := node.continuation then
      match goal with
      | .plain R => if !(c.type == R || c.type.isEmpty) then return (.refused s!"return at node {l}", counts, answers)
      | _ => return (.notHandled "promise goal", counts, answers)
    -- The edges: target, whether the result is pushed, an observation of
    -- it, and a branch's answer.
    let edges : List (Target × Bool × Option BranchRefinement.Observation × Option Bool) :=
      match node.continuation with
      | .ret => []
      | .bind t => [(t, true, none, none)]
      | .effect t => [(t, false, none, none)]
      | .branch y m => [(y, false, none, some true), (m, false, none, some false)]
      | .branchBind y m => [(y, true, some (.boolean true), none), (m, true, some (.boolean false), none)]
      | .tagBind tg y m => [(y, true, some (.tag tg true), none), (m, true, some (.tag tg false), none)]
    for (t, pushed, observed, promote) in edges do
      let some tc := claimed[t.label]? | return (.refused s!"edge from {l}", counts, answers)
      let Γ := if pushed then c.type :: c.context else c.context
      let names := if pushed then pushedNames else entry.names
      -- The edge's own facts: an observation of the result.
      let mut edgeStore := store
      match observed, promote with
      | some o, _ =>
        let (k, pairs, table) := materialize { names, store } (if pushed then width + 1 else width) [0] false
        let k' := HeapKnowledge.observeTyped G Γ k 0 o
        let inverse : Std.HashMap Nat Nat := table.fold (fun acc nm s => acc.insert s nm) {}
        edgeStore := applyDelta store pairs k' false fun i => (inverse.get? i).orElse fun _ => names[i]?
      | none, some q =>
        let (k, pairs, table) := materialize { names := pushedNames, store } (width + 1) [0] false
        let k' := HeapKnowledge.promoteTruthy k 0 q
        let inverse : Std.HashMap Nat Nat := table.fold (fun acc nm s => acc.insert s nm) {}
        edgeStore := applyDelta store pairs k' false fun i => (inverse.get? i).orElse fun _ => pushedNames[i]?
      | none, none => pure ()
      -- The slots' types: each the target's, or below it.
      -- Whether no environment meets the edge's context: the node's own
      -- context's answer, and the pushed result's type.
      let unsatΓ := here || (pushed && ControlFlow.unsatisfiable G [c.type])
      let vacuous := match observed with
        | some o => unsatΓ || (Γ[0]?).any (BranchRefinement.impossible G · o)
        | none => unsatΓ
      let diff := if vacuous then [] else differing Γ tc.context t.mapping
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
          let (r, a) := edgeUsing G images claimed Γ t (observed.map (0, ·)) (readFields ko 0) (optionalFields ko 0)
            (match observed with
              | some o => HeapKnowledge.aliasCells (HeapKnowledge.observeTyped G Γ ko 0 o)
              | none => []) answers
          answers := a
          if r.value.isNone then
            -- The edge's context as the step's yields refine it
            -- (`produceNodeAt`): what a test or a promise establishes.
            let ys ← match yields with
              | some ys => pure ys
              | none =>
                let e := stepDeriv.getD (.node ⟨c.context, node.expression, c.type⟩ .var [])
                let (ys, a) := (nodeYields G images pool c.context [] e stepOut stepK) answers
                answers := a
                pure ys
            yields := some ys
            let outL := KnowledgeExpand.expandLinks (HeapKnowledge.setsCtx (HeapKnowledge.typeSets G c.context) 1) stepOut
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
            let (r, a) := edgeUsing G images claimed Γ' t (observed.map (0, ·)) (readFields outL 0) (optionalFields outL 0)
              (match observed with
                | some o => HeapKnowledge.aliasCells (HeapKnowledge.observeTyped G Γ' outL 0 o)
                | none => []) answers
            answers := a
            if r.value.isNone then return (.refused s!"edge from node {l} to node {t.label}{if l == debugNode then s!" fields {reprStr (readFields ko 0)} links {reprStr ko.links} diff {reprStr diff} implies {reprStr (implies.map fun x => (x.test, x.target))} names {reprStr (entry.names.take 6)} yields {reprStr ((yields.getD []).map fun y => (y.target, y.conditional))}" else ""}", counts, answers)
      if isHead[t.label]! then
        -- The head's given state is entailed on every edge into it.
        let some req := given[t.label]! | return (.refused s!"head {t.label}", counts, answers)
        let slots := (atomsOf req).flatMap Atom.names
        let srcSlots := slots.map (PointClaims.slot t.mapping)
        let (k, _, _) := materialize { names, store := edgeStore } (if pushed then width + 1 else width) srcSlots false
        counts := { counts with queries := counts.queries + 1, queryAtoms := counts.queryAtoms + (atomsOf k).length }
        if !vacuous && !(timedKind "head query" fun _ => KnowledgeExpand.checkIn (KnowledgeExpand.ctxOf G tc.context)
            (HeapKnowledge.withTypedLinks G Γ (ControlFlow.withTypedCells G Γ req t.mapping k)) req t.mapping) then
          return (.refused s!"edge from node {l} into statement entry {t.label}", counts, answers)
      else
        let targetNames := mapNames names t.mapping
        -- The names the edge drops leave the store.
        let gone := droppedBy names t.mapping targetNames ++
          (if !pushed && !entry.names.contains result then [result] else [])
        let gone := if pushed || t.mapping.isSome then gone else gone
        incoming := incoming.modify t.label ({ names := targetNames, store := edgeStore.drop gone } :: ·)
        -- The edge's implications: the entry's, and on a pushed edge those
        -- the result's conditional yields state of it; none naming a name
        -- the edge drops.
        let fresh' : List (PromiseCalls.Implication ι) := if !pushed then [] else
          ((yields.getD []).filterMap fun y => if y.conditional && !y.onFalse then
            (entry.names[y.target]?).map fun tgt => ⟨result, tgt, y.type⟩ else none)
        let carried := (keepFirst {} ((implies ++ fresh').filter fun x =>
          !gone.contains x.test && !gone.contains x.target)).2.toList
        incomingImpl := incomingImpl.modify t.label (carried :: ·)
        indeg := indeg.modify t.label (· - 1)
        if indeg[t.label]! == 0 then queue := t.label :: queue
  if visitedAll < n then return (.notHandled s!"{n - visitedAll} nodes not reached", counts, answers)
  return (.accepted, counts, answers)

end
end Verification.SinglePass
