/- The experimental prototype of `docs/drafts/paper-rules-mode.md`: the
verifier's single pass with one checker layer over the ordinary checker
that applies the paper's rules Bound and Anch at a call of a callback
parameter bounded by an effect variable. Outside the `Verification` library
and its axiom checks: the layer's soundness is the axiom
`paperKeptFactsSurvive` (AGENTS.md, "Experimental rules: a lighter
process"). Its verdicts name the axiom; the ordinary `verifier` never runs
the layer.

  paper-rules-prototype <side.json> <ast.json> <interfaces.json> <file-key> <depth>

`side.json` is `dev/paper-annotations.mts`'s output: each function's bounded
callback parameters and their bounds. -/
import Verification.Source.RequestCli

namespace Verification.HeapExpressionRules
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower
open HeapFacts HeapKnowledge HeapObservations ProgramCertificates
open PositiveCertificates (InstanceImageCheck)

namespace PaperRules

/-- An access path of a type and what the type declares there (`Acc(T)`
of "Declared reach"): its steps (field keys and `[*]`), the keys the type
there declares, and whether it is an array there (a spine and cells). -/
structure AccPath where
  path : List String
  keys : List String
  array : Bool
  deriving Repr, BEq

/-- A bound entry's region, relative to a parameter: its spine, its cells,
a field, every field, or its reach through the access paths its declared
type admits (`"x.**"`). -/
inductive Key where
  | spine
  | cells
  | field (f : String)
  | fields
  | reach (acc : List AccPath)
  deriving Repr, BEq

/-- An effect at a callee's parameters: its entries and its `else`. -/
structure ParamEff where
  entries : List (Nat × Key × Footprints.Change)
  otherwise : Footprints.Change

/-- An effect variable's bound at a callback parameter: the callback's
position among the function's parameters, the bound's entries at the
function's parameters, and its `else`. -/
structure Bound where
  callback : Nat
  entries : List (Nat × Key × Footprints.Change)
  otherwise : Footprints.Change

/-- A call of a function with effect parameters, whose instances are
within their bounds (rule Inst, decided by the side file): the call's
source span and the components of its effect, each at the callee's
parameters: each variable's bound, read in place of its image, and the
callee's own effect besides them. The call's effect is their union, so a
fact survives the call when every component keeps it. -/
structure QCall where
  /-- The call's source span, which the unit's source map gives its node. -/
  span : Nat × Nat
  components : List ParamEff

/-- An unsafe assume `paperAssume(a === b, "#n")`: the source span of its
equality, the issue it names, and its line. At the step evaluating the
equality the layer adds the fact it states, which the sound verifier should
have established there; the issue tracks the verifier's extension. -/
structure Assume where
  span : Nat × Nat
  issue : String
  line : Nat

/-- The rules' information about one unit: its bounded callbacks, and the
number of its parameters, the last of the graph's inputs. -/
structure Unit where
  bounds : List Bound
  /-- The calls of the unit to functions with effect parameters. -/
  calls : List QCall := []
  /-- The unit's unsafe assumes. -/
  assumes : List Assume := []
  /-- The unit's nodes as the pass gives them: expression, context width,
  source span. -/
  sites : List SinglePass.LayerSite := []
  params : Nat
  /-- The number of the graph's inputs, set when the pass supplies it. -/
  inputs : Nat := 0

/-- The slot of parameter `p` at a context of `d` slots. The graph's inputs
are its outermost slots, and parameter `p` is at level `inputs - 1 - p`
from the outermost: the first parameter the innermost input. -/
def slotOf (u : Unit) (d p : Nat) : Nat := d - u.inputs + p

/-- The slot a region is rooted at, where it is rooted at one. -/
def rootSlot : Footprints.Region → Option Nat
  | .field x _ | .fields x | .cells x | .path x _ _ | .pathFields x _ | .pathCells x _ | .spine x _ => some x
  | .inCls r _ => rootSlot r
  | .cls _ | .all => none

/-- The slots holding an object the function's body allocated and never
reassigned: the subjects of the separation facts an allocation records,
over every own location (`HeapSeparation.freshFact`). Slots of the lowered
graph are bound once, so a reassigned local is another slot. -/
def freshSlots (k : Knowledge) : List Nat :=
  k.separation.facts.filterMap fun f =>
    if f.fields.isNone && f.slot < k.separation.depth then some (k.separation.depth - 1 - f.slot) else none

/-- A region of a callee's parameter key at a caller's slot, in the form
the facts' supports take: a key at the empty path of the slot, the spine
at the key `[]`; none for a reach, which is no region of a footprint. -/
def keyRegion (s : Nat) : Key → Option Footprints.Region
  | .spine => some (Footprints.Region.path s [] arraySpineKey)
  | .cells => some (Footprints.Region.cells s)
  | .field f => some (Footprints.Region.path s [] (.str f))
  | .fields => some (Footprints.Region.fields s)
  | .reach _ => none

/-- The bound's entries as regions at the call's slots. -/
def boundAt (u : Unit) (d : Nat) (b : Bound) : Footprints.Footprint :=
  b.entries.filterMap fun (p, key, c) => (keyRegion (slotOf u d p) key).map (·, c)

/-- The slots a reach's roots reach at a step, each with its access path:
a root at the empty path, closed under the read links `y = x.f` of a key
`f` the type declares at `x`'s path (`y` at that path followed by `f`) and
under alias links. The paper's reach follows the access paths of the type;
the knowledge gives the slots the body read along them. -/
def reachPairs (k : Knowledge) (roots : List (Nat × List AccPath)) : List (Nat × List AccPath × List String) :=
  let start := roots.map fun (s, acc) => (s, acc, ([] : List String))
  let step := fun (rs : List (Nat × List AccPath × List String)) => rs ++ k.links.flatMap fun l =>
    rs.filterMap fun (s, acc, a) =>
      if l.alias then
        if s == l.cell then some (l.value, acc, a) else if s == l.value then some (l.cell, acc, a) else none
      else match l.field with
        | .str f => if s == l.cell && acc.any (fun e => e.path == a && e.keys.contains f) then some (l.value, acc, a ++ [f]) else none
        | .sym _ => none
  let rec go : Nat → List (Nat × List AccPath × List String) → List (Nat × List AccPath × List String)
    | 0, rs => rs
    | n + 1, rs =>
      let next := (step rs).eraseDups
      if next.length == rs.length then rs else go n next
  go (k.links.length + 1) start.eraseDups

/-- A key the type declares at an access path, the spine's where it is an
array there. -/
def declaresAt (acc : List AccPath) (a : List String) : PropKey → Bool
  | .str f => acc.any fun e => e.path == a && ((f == "[]" && e.array) || e.keys.contains f)
  | .sym _ => false

/-- Whether a region lies in a reach: rooted at a slot the reach reaches
at an access path `a`, through a path `p` with `a ++ p` an access path of
the type, at a key the type declares there, or at its spine or cells where
it is an array. -/
def inReach (pairs : List (Nat × List AccPath × List String)) : Footprints.Region → Bool
  | .field x k => pairs.any fun (s, acc, a) => s == x && declaresAt acc a k
  | .path x p k => pairs.any fun (s, acc, a) => s == x && declaresAt acc (a ++ p) k
  | .spine x p => pairs.any fun (s, acc, a) => s == x && acc.any fun e => e.path == a ++ p && e.array
  | .cells x => pairs.any fun (s, acc, a) => s == x && acc.any fun e => e.path == a && e.array
  | .pathCells x p => pairs.any fun (s, acc, a) => s == x && acc.any fun e => e.path == a ++ p && e.array
  | .inCls r _ => inReach pairs r
  | .fields _ | .pathFields _ _ | .cls _ | .all => false

/-- A region without its class restriction. -/
def unrestricted : Footprints.Region → Footprints.Region
  | .inCls r _ => unrestricted r
  | r => r

/-- The slot whose object's own location a region names: a field, the
fields or the spine at a slot itself. A path through a field, and an
array's element locations, may name storage older than the slot's object. -/
def ownSlot : Footprints.Region → Option Nat
  | .field x _ | .fields x => some x
  | .path x [] _ | .pathFields x [] | .spine x [] => some x
  | .inCls r _ => ownSlot r
  | _ => none

/-- A change read at a region's category: on a spine, `init` and `scalar`
are `keep`; on contents, `extend` and `grow` are `scalar`
(`Change.onSpine`, `Change.onValue`). -/
def atCategory : Footprints.Region → Footprints.Change → Footprints.Change
  | .spine .., c => c.onSpine
  | .inCls r _, c => atCategory r c
  | _, c => c.onValue

/-- **The pair rule**: the callback's effect `ε` is within `δ` on `r`
(Definition "Order") when one of the two effects `ε` is included in is
(the meet, rules Anch and Bound):

- Anch, `{old: any}`: `r` is an own location of an object the body
  allocated, so no `old` location; its `else` is `keep`;
- Bound: every bound entry not disjoint from `r` is within `δ` (the
  existing `respects`, with its separation query), and the bound's `else`
  is within `δ` unless `r` lies in an entry: equal to an entry's region, or
  in a reach entry's declared reach. -/
def keepsPair (q : Footprints.SepQuery) (fresh : List Nat) (bound : Footprints.Footprint) (otherwise : Footprints.Change)
    (reach : Footprints.Region → Bool) (e : Footprints.Region × Footprints.Change) : Bool :=
  (ownSlot e.1).any fresh.contains ||
    (Footprints.respects q [e] bound &&
      ((atCategory e.1 otherwise).le e.2 || reach e.1 || bound.any (unrestricted ·.1 == unrestricted e.1)))

/-- An effect the layer reads at a call: its entries at the call's slots,
its `else`, the roots of its reach entries with their access paths, and
the slots of storage it leaves alone by Anch (none at a call whose effect
is not an anchored variable). -/
structure CallEff where
  fresh : List Nat
  bound : Footprints.Footprint
  otherwise : Footprints.Change
  roots : List (Nat × List AccPath)

/-- The facts of the call's entry that every effect of `effs` keeps, past
the call's result. The effects are the components of one call's effect
(its union), or of several calls the layer cannot tell apart: the facts
every one keeps survive. -/
def keptBy (effs : List CallEff) (stable : Nat → String → Bool) (k : Knowledge) : Knowledge :=
  let q := Footprints.knowledgeQuery k
  let keeps := fun (S : Footprints.Footprint) => !effs.isEmpty && effs.all fun c =>
    S.all (keepsPair q c.fresh c.bound c.otherwise (inReach (reachPairs k c.roots)))
  let idx := k.indices.filter fun a => !a.fact.envOnly &&
    match a.fact.support? (.ofFirst stable) with
    | some S => keeps S
    | none => false
  let cells := k.cells.filter fun f => keeps [(Footprints.Region.field f.slot f.field, .keep)]
  -- A read link `y = x.f` holds while the field location of `x` at `f`
  -- keeps its contents: its support is that location at `keep`. An alias
  -- link reads no heap, and the ordinary output keeps it.
  let links := k.links.filter fun l => !l.alias && keeps [(Footprints.Region.path l.cell [] l.field, .keep)]
  { cells := HeapFacts.shift cells, indices := HeapKnowledge.shiftIndices idx,
    links := links.map fun l => { l with cell := l.cell + 1, value := l.value + 1 } }

/-- The reach entries of an effect's entries, at slots. -/
def reachRoots (es : List (Nat × Key × Footprints.Change)) : List (Nat × List AccPath) :=
  es.filterMap fun (s, key, _) => match key with
    | .reach acc => some (s, acc)
    | _ => none

/-- At a call of a bounded callback parameter: the callback's effect is
the variable, within the bound (Bound) and within `{old: any}` (Anch). -/
def kept (u : Unit) (b : Bound) (stable : Nat → String → Bool) (d : Nat) (k : Knowledge) : Knowledge :=
  let roots := reachRoots (b.entries.map fun (p, key, c) => (slotOf u d p, key, c))
  keptBy [{ fresh := freshSlots k, bound := boundAt u d b, otherwise := b.otherwise, roots }] stable k

/-- At a call of a function with effect parameters (rule Inst's
conclusion): the call's effect is the callee's effect with each variable
replaced by its instance, and each instance is within its bound, so the
call's effect is within the union of the bounds and the callee's own
effect, read at the actual arguments' slots: one component each. No Anch:
the instance may change the caller's own storage. Where an entry's
parameter receives no slot, nothing is kept. -/
def atCall (c : QCall) (args : List Tm) : Option (List CallEff) :=
  let slot := fun (p : Nat) => match args[p]? with
    | some (.var a) => some a
    | _ => none
  c.components.mapM fun pe => do
    let es ← pe.entries.mapM fun (p, key, ch) => (slot p).map fun a => (a, key, ch)
    let bound := es.filterMap fun (a, key, ch) => (keyRegion a key).map (·, ch)
    pure { fresh := [], bound, otherwise := pe.otherwise, roots := reachRoots es }

/-- The fact an assumed equality states, in the knowledge's link forms, at
the call's context: `y === x.f` the read link `y = x.f`, `x === y` an alias
link; none for any other expression. -/
def linkOf : Tm → Option HeapLinks.Link
  | .arith .eq (.var a) (.readAt f (.var b)) | .arith .eq (.readAt f (.var b)) (.var a) =>
    some { cell := b, value := a, field := f }
  | .arith .eq (.var a) (.var b) => some { cell := a, value := b, alias := true }
  | _ => none

/-- The fact an unsafe assume adds at this step: the step evaluates an
assume's equality (its nodes' spans are all spans of the unit's assumes),
which `linkOf` represents; the link past the step's result. -/
def assumed (u : Unit) (spans : List (Option (Nat × Nat))) (t : Tm) : Option HeapLinks.Link :=
  if !spans.isEmpty && spans.all (fun sp => sp.any fun sp => u.assumes.any (·.span == sp)) then
    (linkOf t).map fun l => { l with cell := l.cell + 1, value := l.value + 1 }
  else none

/-- The layer's step: the ordinary checker's output, and at a call of a
bounded callback parameter the facts the rules keep added to it. -/
def run {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} (u : Unit)
    (base : Checker G images) (j : Sequent ι) (k : Knowledge) (e : StepEvidence ι) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) : CheckResult ι Knowledge :=
  let r := base.run j k e codes sums
  let spansHere := u.sites.filterMap fun (t, w, sp) => if t == j.term && w == j.context.length then some sp else none
  match assumed u spansHere j.term with
  | some l => r.map fun out => { out with links := (out.links ++ [l]).eraseDups }
  | none =>
  match j.term with
  | .invoke (.var s) _ args =>
    let d := j.context.length
    -- The callee is the parameter's slot or a copy of it (an alias link).
    let aliases := fun (x : Nat) => x == s || k.links.any fun l => l.alias &&
      ((l.cell == s && l.value == x) || (l.cell == x && l.value == s))
    let add := fun (add : Knowledge) => r.map fun out =>
      { out with cells := out.cells ++ add.cells, indices := out.indices ++ add.indices,
                 links := (out.links ++ add.links).eraseDups }
    match u.bounds.find? (fun b => aliases (slotOf u d b.callback)) with
    | some b => add (kept u b (stableFirst G j.context) d k)
    | none =>
      -- A call of a function with effect parameters, identified by its
      -- source span: the spans of the unit's nodes whose expression and
      -- context width are this step's, each the span of a side-file call,
      -- and all of them one call. Where the nodes give no span, or two
      -- calls, nothing is added.
      let spans := u.sites.filterMap fun (t, w, sp) => if t == j.term && w == d then some sp else none
      -- Nodes with equal terms and context widths are one site to the
      -- layer: it keeps what every call at such a node keeps.
      let effs := spans.map fun sp => sp.bind fun sp => (u.calls.find? (·.span == sp)).bind (atCall · args)
      match (effs.mapM id).map List.flatten with
      | some (c :: cs) => add (keptBy (c :: cs) (stableFirst G j.context) k)
      | _ => r
  | _ => r

/-- **The assumption the prototype rests on**: the facts the layer keeps
at a call of a bounded callback parameter survive the call, and the fact an
unsafe assume states holds after its call. Its premise is the layer's run,
which decides "allocated in the body" from the allocation's separation fact,
the bound from the side file, and an assume's fact from its expression. -/
axiom paperKeptFactsSurvive {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (u : Unit) (base : Checker G images) :
    ∀ {j k e out codes sums}, (run u base j k e codes sums).value = some out →
      CodesSound G codes → SummariesSound G images sums → ∀ {ε ρ n W h},
      EnvOk G j.context ρ n W → HeapKnowledge.Holds k ε ρ h →
      WorldAdm W → HeapOk n W h → RefsOk W (instantiate 0 ρ j.term) → RootsOk W ρ →
      SafePost (excOf G) (meaning G j.type)
        (fun h' v => HeapKnowledge.Holds out ε (push v ρ) h')
        n W h (instantiate 0 ρ j.term)

/-- The layer: a checker whose `run` is the rules' step. -/
def layer {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} (u : Unit)
    (base : Checker G images) : Checker G images where
  run := run u base
  sound := paperKeptFactsSurvive u base

/-! ## The side file -/

def changeOf : String → Option Footprints.Change
  | "keep" => some .keep | "init" => some .init | "scalar" => some .scalar
  | "extend" => some .extend | "grow" => some .grow | "any" => some .any | _ => none

/-- A key at a parameter list: `"x[*]"` its spine, `"x[#]"` its cells,
`"x.f"` a field, `"x.*"` every field, `"x.**"` its reach with the access
paths the side file gives; none for any other key (a path through a
field), which the layer does not read. -/
def keyOf (params : List String) (reach : String → Option (List AccPath)) (key : String) : Option (Nat × Key) :=
  let root := fun (n : Nat) => String.ofList (key.toList.take (key.length - n))
  if key.endsWith ".**" then do
    let acc ← reach key
    (params.idxOf? (root 3)).map (·, .reach acc)
  else if key.endsWith "[*]" then (params.idxOf? (root 3)).map (·, .spine)
  else if key.endsWith "[#]" then (params.idxOf? (root 3)).map (·, .cells)
  else if key.endsWith ".*" then (params.idxOf? (root 2)).map (·, .fields)
  else match key.splitOn "." with
    | [r, f] => (params.idxOf? r).map (·, .field f)
    | _ => none

open Lean in
/-- The access paths of an effect's reach entries, by key. -/
def reachOf (eff : Json) (key : String) : Option (List AccPath) := do
  let r ← (eff.getObjVal? "reach").toOption
  let a ← (r.getObjVal? key).toOption
  let paths ← ((a.getObjVal? "paths").toOption.bind (·.getArr?.toOption))
  paths.toList.mapM fun (e : Json) => do
    let path ← ((e.getObjVal? "path").toOption.bind (·.getArr?.toOption))
    let path ← path.toList.mapM (·.getStr?.toOption)
    let keys ← ((e.getObjVal? "keys").toOption.bind (·.getArr?.toOption))
    let keys ← keys.toList.mapM (·.getStr?.toOption)
    let array ← (e.getObjValAs? Bool "array").toOption
    pure { path, keys, array }

open Lean in
/-- An effect of the side file at a parameter list; none where a key or a
change is one the layer does not read. A reach is no region of the
footprint, so `respects` cannot weigh it against a support pair; at `keep`
it is within every change, and the layer reads it at `keep` only. -/
def paramEff (params : List String) (eff : Json) : Option ParamEff := do
  let entries ← ((eff.getObjVal? "entries").toOption.bind (·.getArr?.toOption))
  let entries ← entries.toList.mapM fun (en : Json) => do
    let pair ← en.getArr?.toOption
    let key ← (pair[0]?.getD Json.null).getStr?.toOption
    let c ← (pair[1]?.getD Json.null).getStr?.toOption
    let (i, k) ← keyOf params (reachOf eff) key
    let c ← changeOf c
    match k with
    | .reach _ => if c != .keep then none else pure (i, k, c)
    | _ => pure (i, k, c)
  let otherwise ← changeOf (← ((eff.getObjVal? "else").toOption.bind (·.getStr?.toOption)))
  pure { entries, otherwise }

open Lean in
/-- Each function's bounded callbacks, from `dev/paper-annotations.mts`. A
function whose bound the layer does not read gets no layer at its
callbacks' calls. -/
def unitsOf (side : Json) : Except String (Std.HashMap String Unit) := do
  let fns ← side.getObjVal? "functions"
  let .obj kvs := fns | throw "functions: an object"
  let mut out : Std.HashMap String Unit := {}
  for (name, info) in kvs.toArray do
    let params ← (← info.getObjVal? "params").getArr?
    let params ← params.toList.mapM (·.getStr?)
    let effects ← (← info.getObjVal? "effectParams").getArr?
    let bounded ← (← info.getObjVal? "bounded").getArr?
    let mut bounds := []
    let mut readable := true
    for bd in bounded do
      let index ← (← bd.getObjVal? "index").getNat?
      let var ← (← bd.getObjVal? "variable").getStr?
      let some ep := effects.find? (fun e => (e.getObjValAs? String "name").toOption == some var) | throw s!"no bound for {var}"
      match paramEff params (← ep.getObjVal? "bound") with
      | some pe => bounds := bounds ++ [{ callback := index, entries := pe.entries, otherwise := pe.otherwise : Bound }]
      | none => readable := false
    if readable && !bounds.isEmpty then out := out.insert name { bounds, params := params.length }
  -- Each caller's calls with instances within their bounds and the
  -- callee's own effect read, by source span.
  let calls ← (← side.getObjVal? "calls").getArr?
  for call in calls do
    let caller ← (← call.getObjVal? "caller").getStr?
    let ok := (call.getObjValAs? Bool "ok").toOption == some true
    if !ok then continue
    let .ok ownEff := call.getObjVal? "own" | continue
    if (ownEff.getStr?).isOk then continue
    let params ← (← call.getObjVal? "params").getArr?
    let params ← params.toList.mapM (·.getStr?)
    let span ← call.getObjVal? "span"
    let span : Nat × Nat := (← (← span.getArrVal? 0).getNat?, ← (← span.getArrVal? 1).getNat?)
    let bounds ← (← call.getObjVal? "bounds").getArr?
    let some components := (bounds.toList ++ [ownEff]).mapM (paramEff params) | continue
    let c : QCall := { span, components }
    let u := (out.get? caller).getD { bounds := [], params := 0 }
    out := out.insert caller { u with calls := u.calls ++ [c] }
  -- Each unit's unsafe assumes whose form the side script read.
  let assumes ← match side.getObjVal? "assumes" with
    | .ok a => a.getArr?
    | .error _ => pure #[]
  for a in assumes do
    if (a.getObjValAs? Bool "ok").toOption != some true then continue
    let caller ← (← a.getObjVal? "caller").getStr?
    let span ← a.getObjVal? "span"
    let span : Nat × Nat := (← (← span.getArrVal? 0).getNat?, ← (← span.getArrVal? 1).getNat?)
    let issue ← (← a.getObjVal? "issue").getStr?
    let line ← (← a.getObjVal? "line").getNat?
    let u := (out.get? caller).getD { bounds := [], params := 0 }
    out := out.insert caller { u with assumes := u.assumes ++ [{ span, issue, line }] }
  return out

end PaperRules
end Verification.HeapExpressionRules

open Verification Lean

/-- The layer of a unit, by its name: the rules' checker where the side
file bounds one of its callbacks, the ordinary checker otherwise. -/
def layerOf (units : Std.HashMap String HeapExpressionRules.PaperRules.Unit) : SinglePass.PassLayer :=
  fun name inputs sites _ _ _ _ _ _ base => match units.get? name with
    | some u => HeapExpressionRules.PaperRules.layer { u with inputs, sites } base
    | none => base

/-- Each selected unit's group checked by the pass with the layer; a verdict
line per unit, accepted ones naming the assumption. -/
def checkFile (units : Std.HashMap String HeapExpressionRules.PaperRules.Unit) (astPath fileKey : String) (fuel : Nat)
    (interfacesPath : String) : IO UInt32 := do
  match ← RequestCli.prepareUnitsFile astPath fileKey fuel none {} interfacesPath true with
  | .error e => RequestCli.refuse e
  | .ok p =>
    for i in p.units do
      let known ← p.known i
      let known := known ++ (p.fr.group i).filterMap fun j => match p.fr.units[j]? with
        | some (f, _, none) => some (f.name, none)
        | _ => none
      let memo ← p.memo.get
      let unit := p.fr.unitId i
      match p.plan i known memo with
      | .error reason => IO.println (Json.compress (Json.mkObj [("unit", unit), ("refusal", reason)]))
      | .ok f =>
        -- The verifier's own route (`PreparedFile.check`): the pass over the
        -- group with inferred loop-head facts, here with the layer.
        let (_, verdict, _, _) := f.passGroupMode8 true p.force (f.givenAt p.givenLines) fuel (p.fr.group i)
          (located := true) (layer := some (layerOf units))
        let applies := (p.fr.group i).any fun j => match p.fr.units[j]? with
          | some (fn, _, _) => units.contains fn.name
          | none => false
        -- The unsafe assumes the group's units rely on, by issue and line.
        let assumes := (p.fr.group i).flatMap fun j => match p.fr.units[j]? with
          | some (fn, _, _) => ((units.get? fn.name).map (·.assumes)).getD []
          | none => []
        let assumesJson := Json.arr (assumes.map fun a => Json.str s!"{a.issue} at line {a.line}").toArray
        match verdict with
        | .ok _ => IO.println (Json.compress (Json.mkObj (if applies
            then [("unit", unit), ("acceptedUnderPaperRules", true), ("assumed", "paperKeptFactsSurvive"),
                  ("assumes", assumesJson)]
            else [("unit", unit), ("accepted", true)])))
        | .error reason => IO.println (Json.compress (Json.mkObj [("unit", unit), ("refusal", (reason.take 400).toString)]))
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [side, ast, interfaces, key, depth] =>
    let some fuel := depth.toNat? | IO.eprintln "usage: depth is a number"; return 2
    let text ← IO.FS.readFile side
    match Json.parse text >>= HeapExpressionRules.PaperRules.unitsOf with
    | .error e => IO.eprintln s!"side file: {e}"; return 2
    | .ok units => checkFile units ast key fuel interfaces
  | _ =>
    IO.eprintln "usage: paper-rules-prototype <side.json> <ast.json> <interfaces.json> <file-key> <depth>"
    return 2
