import Verification.Source.Equations.Interning
import Verification.Source.Equations.Instances

/-! Section references follow `RECURSIVE-EQUATIONS.md`. -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-! ### Finishing: hash-consing, validation, checks -/

/-- Merge literal and scheme heads with equal templates (§8.1), until no two
more are equal: each round only merges, so there are at most as many rounds
as heads. Returns each head's representative. -/
def hashCons (heads : Array Draft) : Array Nat := Id.run do
  let mergeable (d : Draft) : Bool := d.kind == .literal || d.kind == .scheme || d.kind == .primitive
  let mut rep : Array Nat := Array.range heads.size
  for _ in [0:heads.size + 1] do
    let mut seen : Std.HashMap String Nat := {}
    let mut next := rep
    for h in [0:heads.size] do
      let d := heads[h]!
      if !mergeable d then continue
      let r := rep
      -- Renamed, a union is normalized again, as `compact` writes it.
      let body := d.body.map (mapRow fun U => normUnion (U.map (treeRename fun g => r[g]!)))
      let key := s!"{spelling d.kinds}|{bindersSpelling d.binders}|{spelling body}"
      match seen.get? key with
      | some g => next := next.set! h (min g next[h]!)
      | none => seen := seen.insert key h
    if next == rep then break
    rep := next
  return rep

/-- The heads' raw rows. -/
def rawHeads (drafts : Array Draft) (bodies : Array (GraphRow Tree (List Tree))) : List RawHead :=
  (List.range drafts.size).map fun h =>
    let d := drafts[h]!
    { name := d.name
      header := { parameters := d.kinds.length, binders := d.binders, kinds := d.kinds }
      body := bodies[h]! }

def builtinsOf (E : Equations) (proto unknown : Option Nat) (excluded : List PropKey) :
    Option (ArrayBuiltins (Label E.signature)) :=
  proto.bind fun p => unknown.bind fun u => (Label.ofTree? (mkApp p [])).bind fun l =>
    (Label.ofTree? (mkApp u [])).map fun k => ⟨[l], [k], excluded⟩

/-- A bound obligation's closed form: inside a template, the head's
parameters are read as bounded parameter labels. On the actual side each is
a family variable met with its declared bound (§8.2); on the upper side the
variable itself. Under an assignment meeting the bounds both keep their
meaning (SOURCE-CONTRACTS.md, "Written applications"); a meet only on the
actual side lets a bound recurring in the upper one (`T extends Node<T>`)
be compared at the variable. -/
def closeObligation (o : Obligation) : Union × Union :=
  let var (p : Tree) : Tree := match p with
    | .argument i => .var 1000000 i .value
    | .local j => .var 2000000 j .value
    | t => t
  let rec bounded (fuel : Nat) (seen : List Tree) (p : Tree) : Union :=
    match fuel with
    | 0 => [var p]
    | fuel + 1 =>
      if seen.contains p then [var p] else
        match o.bounds.find? (·.1 == p) with
        | none => [var p]
        | some (_, B) =>
          let next := bounded fuel (p :: seen)
          let B := B.flatMap (treeSubst (next ∘ .argument) (next ∘ .local))
          let B := B.flatMap (treeReplace fun t => if isPlaceholder t then some (next t) else none)
          meetUnions [[var p], B]
  let σ := bounded (o.bounds.length + 1) []
  let close (σ : Tree → Union) (U : Union) :=
    (U.flatMap (treeSubst (σ ∘ .argument) (σ ∘ .local))).flatMap
      (treeReplace fun t => if isPlaceholder t then some (σ t) else none)
  (close σ o.actual, close (fun p => [var p]) o.upper)

/-- The lowered heads, hash-consed and compacted, before validation. -/
structure Built where
  state : State
  /-- Old head index to new. -/
  rename : Nat → Nat
  drafts : Array Draft
  bodies : Array (GraphRow Tree (List Tree))

def Built.rn (b : Built) (U : Union) : Union := normUnion (U.map (treeRename b.rename))

/-- Each head's class of unfolding: rounds of hashes of its parameter
kinds, binders and row, each head the row names read as its previous hash,
until a round tells no more heads apart. The store's numbering and the
heads' names are nowhere in it, so two stores holding the same equations
give their heads the same classes. -/
def unfoldingClasses (heads : Array Draft) : Array UInt64 := Id.run do
  let mut previous : Array UInt64 := heads.map fun _ => 0
  let mut count := 1
  for _ in [0:heads.size + 1] do
    let prev := previous
    let next := heads.mapIdx fun i d =>
      let at_ (h : Nat) : Nat := (prev[h]?.getD 0).toNat
      let body := (d.body.map (mapRow fun U => normUnion (U.map (treeRename at_)))).map
        (fun b => (toJson (b.map (treeRename at_) id)).compress)
      hash (spelling d.kinds, bindersSpelling d.binders, prev[i]?.getD 0, body.getD "none")
    let c := (next.foldl (fun (m : Std.HashSet UInt64) x => m.insert x) {}).size
    previous := next
    if c == count then break
    count := c
  return previous

/-- Merge equal templates and compact (§8.1): the kept heads with the
primitive values' and kinds' heads first, then every head no hash-consing
merges, in order, then the literal, scheme and primitive heads by their
class of unfolding
(`unfoldingClasses`), equal classes in order. Unions are ordered by their
members' heads, so two stores lowering the same literals order them alike
whatever order their sources wrote them in (STAGE-STORE.md, "Units of a
check"). -/
def compact (s : State) : Except String Built := do
  let rep := hashCons s.heads
  -- The primitive values' and the primitive kinds' heads, made first
  -- (`primitives`), keep their places.
  let mergeable (h : Nat) : Bool := h ≥ 9 && match s.heads[h]? with
    | some d => d.kind == .literal || d.kind == .scheme || d.kind == .primitive
    | none => false
  let classes := unfoldingClasses s.heads
  let all := (List.range s.heads.size).filter fun h => rep[h]! == h
  let kept := all.filter (!mergeable ·) ++
    ((all.filter mergeable).mergeSort fun a b => classes[a]! < classes[b]! || (classes[a]! == classes[b]! && a ≤ b))
  let index : Std.HashMap Nat Nat := kept.zipIdx.foldl (fun m (h, i) => m.insert h i) {}
  let f (h : Nat) : Nat := (index.get? rep[h]!).getD 0
  let rn (U : Union) : Union := normUnion (U.map (treeRename f))
  let drafts := (kept.map fun h => s.heads[h]!).toArray
  let bodies ← drafts.mapM fun d => match d.body with
    | some b => pure (mapRow rn b)
    | none => throw s!"{d.name}: its row was never lowered"
  return { state := s, rename := f, drafts, bodies }

/-- The same equations, with whether each label whose row is cached has
overlapping clauses (`BranchRefinement.selfOverlaps`) computed at most once,
on the equations' own graph: the graph's `overlapping` hint. -/
def _root_.Verification.EquationGraphs.Equations.withOverlaps (E : Equations) : Equations :=
  let G := E.graph
  let m : Std.HashMap Tree (Label E.signature × Thunk Bool) :=
    E.named.foldl (fun m l => m.insert l.1 (l, Thunk.mk fun _ => BranchRefinement.selfOverlaps G l)) {}
  { E with overlaps := fun l => match m[l.1]? with
      | some p => if l = p.1 then some p.2.get else none
      | none => none }

/-- Validated equations, with the built-ins. -/
def Built.equations (b : Built) : Except String Equations := do
  let E := (← Equations.ofRaw (rawHeads b.drafts b.bodies)).memo
  let proto := b.state.proto.map b.rename
  let unknown := (b.state.keys.get? unknownKey).map b.rename
  return Equations.withOverlaps
    { E with builtins := if b.state.arrays then builtinsOf E proto unknown b.state.excluded else none }

/-- The store the units grow, from the compacted heads: their rows, their
keys (a key that spells a head index spelled again with the new one), the
generic units' binders, the placeholders and the built-ins. -/
def Built.store (b : Built) : State :=
  let (s, f) := (b.state, b.rename)
  let drafts := (b.drafts.zip b.bodies).map fun (d, body) => { d with body := some body }
  -- Keys that spell a head index or a tree are made again from the new rows.
  let spelled (k : String) : Bool :=
    k.startsWith "ground|" || k.startsWith "method|" || k.startsWith "lifted|" || k.startsWith "schemeOver|"
  let kept := s.keys.fold (fun (m : Std.HashMap String Nat) k h =>
    if spelled k then m else m.insert k (f h)) {}
  let keys := (List.range drafts.size).foldl (fun (m : Std.HashMap String Nat) h =>
    let d := drafts[h]!
    match d.kind, d.body with
    | .method o key, _ => m.insert s!"method|{f o}|{key}" h
    -- Every nullary head is found by its clauses, a declaration's among
    -- them, as a finite table finds a row by its clauses.
    | _, some (.clauses cs) =>
      if d.kinds.isEmpty && !m.contains s!"ground|{spelling cs}" then m.insert s!"ground|{spelling cs}" h
      else m
    | _, _ => m) kept
  let rnB (b : Binding) : Binding := { b with value := b.value.map (treeRename f) }
  let owned (d : Draft) : Draft := match d.kind with
    | .method o key => { d with kind := .method (f o) key }
    | _ => d
  { s with heads := drafts.map owned, nullary := nullaryOf (drafts.map owned), nullary_eq := rfl,
           keys := keys, jobs := [], processing := [], obligations := [],
           meetChecks := [], unitBinders := [],
           scopes := s.scopes.map (fun (p, bs) => (p, bs.map fun (n, x) => (n, rnB x))),
           proto := s.proto.map f, nativeStable := s.nativeStable.map b.rn }

/-- Source lowering either refuses a form or reports the compared types
under the compacted equations. The outcome retains unfinished subtype work. -/
inductive Failure where
  | refusal (reason : String)
  | bound (store : State) (pos : Option Span) (site : String)
      (actual expected : Union) (outcome : RequestJson.DiagnosticOutcome)

/-- The checks lowering owes the source (§5): every closed meet with a value;
every declared bound where an application is written. Variances are not
lowering's: the checker computes them (RECURSIVE-EQUATIONS §4.3). -/
def Built.finish (b : Built) : Except Failure Equations := do
  let (s, f, rn, bodies) := (b.state, b.rename, b.rn, b.bodies)
  let E ← b.equations.mapError Failure.refusal
  -- Closed meets: an empty one is refused where it is lowered.
  let base (t : Tree) : Option (List (Clause (List Tree))) := match t with
    | .app g args => match bodies[g]? with
      | some (.clauses cs) => some (instantiateClauses cs (args.toList.map Types.toList))
      | _ => none
    | _ => none
  -- An intersection distributes over its operands' unions: it is empty when
  -- each of its meets is, a meet of clause rows whose meet has no value.
  let empty (t : Tree) : Bool := match treeRename f t with
    | .meet ps => match ps.toList.mapM base with
      | some lists => ((meetAll lists).filter Clause.isValue).isEmpty
      | none => false
    | _ => false
  for (U, site) in s.meetChecks do
    if !U.isEmpty && !U.any treeOpen && U.all empty then throw (.refusal s!"{site}: {emptyMeet}")
  -- Declared bounds, where written.
  for o in s.obligations do
    let o : Obligation := { o with actual := rn o.actual, upper := rn o.upper, bounds := o.bounds.map fun (p, U) => (p, rn U) }
    let (A, B) := closeObligation o
    let A ← (closedUnion E o.site A).mapError Failure.refusal
    let B ← (closedUnion E o.site B).mapError Failure.refusal
    match CertificateProducer.comparisonUsing E.graph { E.instanceImageCheck with budget := s.subtypeBudget } A B with
    | .established _ => pure ()
    | .notEstablished =>
      throw (.bound b.store o.pos o.site (A.map (·.1)) (B.map (·.1)) .notEstablished)
    | .exhausted rounds visited =>
      throw (.bound b.store o.pos o.site (A.map (·.1)) (B.map (·.1))
        (.exhausted s.subtypeBudget.rounds rounds visited))
  return E


end Verification.EquationLowering
