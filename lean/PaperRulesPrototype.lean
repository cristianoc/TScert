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

/-- A bound entry's region, relative to a parameter: its spine, a field, or
its reach through declared keys (`"x.**"`). -/
inductive Key where
  | spine
  | field (f : String)
  | reach
  deriving Repr, BEq

/-- An effect variable's bound at a callback parameter: the callback's
position among the function's parameters, the bound's entries at the
function's parameters, and its `else`. -/
structure Bound where
  callback : Nat
  entries : List (Nat × Key × Footprints.Change)
  otherwise : Footprints.Change
  /-- The keys the types in the reach declare, for the entries `"x.**"`. -/
  keys : List String := []

/-- The rules' information about one unit: its bounded callbacks, and the
number of its parameters, the last of the graph's inputs. -/
structure Unit where
  bounds : List Bound
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

/-- The bound's entries as regions at the call's slots, in the form the
facts' supports take: a key at the empty path of a parameter's slot, the
spine at the key `[]`. -/
def boundAt (u : Unit) (d : Nat) (b : Bound) : Footprints.Footprint :=
  b.entries.filterMap fun (p, key, c) =>
    let s := slotOf u d p
    match key with
      | .spine => some (Footprints.Region.path s [] arraySpineKey, c)
      | .field f => some (Footprints.Region.path s [] (.str f), c)
      | .reach => none

/-- The slots a reach entry's roots reach at the call: its parameters'
slots, closed under the read links of a declared key and under alias
links. The paper's reach follows the keys the types declare; the knowledge
gives the slots the body read through such keys. -/
def reachSlots (k : Knowledge) (keys : List String) (roots : List Nat) : List Nat :=
  let step := fun (rs : List Nat) => (rs ++ k.links.filterMap fun l =>
    if l.alias then
      if rs.contains l.cell then some l.value else if rs.contains l.value then some l.cell else none
    else match l.field with
      | .str f => if rs.contains l.cell && keys.contains f then some l.value else none
      | .sym _ => none).eraseDups
  (List.range (k.links.length + 1)).foldl (fun rs _ => step rs) roots.eraseDups

/-- Whether a key is the spine's or one the reach's types declare. -/
def declared (keys : List String) : PropKey → Bool
  | .str f => f == "[]" || keys.contains f
  | .sym _ => false

/-- Whether a region lies in the reach: rooted at a reach slot, through
declared keys only. -/
def inReach (slots : List Nat) (keys : List String) : Footprints.Region → Bool
  | .field x k => slots.contains x && declared keys k
  | .path x p k => slots.contains x && p.all keys.contains && declared keys k
  | .spine x p => slots.contains x && p.all keys.contains
  | .cells x => slots.contains x
  | .pathCells x p => slots.contains x && p.all keys.contains
  | .inCls r _ => inReach slots keys r
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
      (otherwise.le e.2 || reach e.1 || bound.any (unrestricted ·.1 == unrestricted e.1)))

/-- The facts of the call's entry the rules keep, past the call's result. -/
def kept (u : Unit) (b : Bound) (stable : Nat → String → Bool) (d : Nat) (k : Knowledge) : Knowledge :=
  let q := Footprints.knowledgeQuery k
  let fresh := freshSlots k
  let bound := boundAt u d b
  let roots := b.entries.filterMap fun (p, key, _) => if key == .reach then some (slotOf u d p) else none
  let reach := inReach (reachSlots k b.keys roots) b.keys
  let keeps := fun (S : Footprints.Footprint) => S.all (keepsPair q fresh bound b.otherwise reach)
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

/-- The layer's step: the ordinary checker's output, and at a call of a
bounded callback parameter the facts the rules keep added to it. -/
def run {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} (u : Unit)
    (base : Checker G images) (j : Sequent ι) (k : Knowledge) (e : StepEvidence ι) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) : CheckResult ι Knowledge :=
  let r := base.run j k e codes sums
  match j.term with
  | .invoke (.var s) _ _ =>
    let d := j.context.length
    -- The callee is the parameter's slot or a copy of it (an alias link).
    let aliases := fun (x : Nat) => x == s || k.links.any fun l => l.alias &&
      ((l.cell == s && l.value == x) || (l.cell == x && l.value == s))
    match u.bounds.find? (fun b => aliases (slotOf u d b.callback)) with
    | some b => r.map fun out =>
      let add := kept u b (stableFirst G j.context) d k
      { out with cells := out.cells ++ add.cells, indices := out.indices ++ add.indices,
                 links := (out.links ++ add.links).eraseDups }
    | none => r
  | _ => r

/-- **The assumption the prototype rests on**: the facts the layer keeps
at a call of a bounded callback parameter survive the call. Its premise is
the layer's run, which decides "allocated in the body" from the allocation's
separation fact and the bound from the side file. -/
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

/-- A key `"x[*]"`, `"x.f"` or `"x.**"` at a parameter list. -/
def keyOf (params : List String) (key : String) : Option (Nat × Key) :=
  if key.endsWith ".**" then
    let root := String.ofList (key.toList.take (key.length - 3))
    (params.idxOf? root).map (·, .reach)
  else if key.endsWith "[*]" then
    let root := String.ofList (key.toList.take (key.length - 3))
    (params.idxOf? root).map (·, .spine)
  else match key.splitOn "." with
    | [root, f] => (params.idxOf? root).map (·, .field f)
    | _ => none

open Lean in
/-- Each function's bounded callbacks, from `dev/paper-annotations.mts`. -/
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
    for bd in bounded do
      let index ← (← bd.getObjVal? "index").getNat?
      let var ← (← bd.getObjVal? "variable").getStr?
      let some ep := effects.find? (fun e => (e.getObjValAs? String "name").toOption == some var) | throw s!"no bound for {var}"
      let bound ← ep.getObjVal? "bound"
      let entries ← (← bound.getObjVal? "entries").getArr?
      let entries ← entries.toList.mapM fun en => do
        let pair ← en.getArr?
        let key ← (pair[0]?.getD Json.null).getStr?
        let c ← (pair[1]?.getD Json.null).getStr?
        let some k := keyOf params key | throw s!"unsupported key {key}"
        let some c := changeOf c | throw s!"unknown change {c}"
        -- A reach is no region of the footprint, so `respects` cannot weigh
        -- it against a support pair; at `keep` it is within every change.
        if k.2 == .reach && c != .keep then throw s!"a reach entry {key} at {repr c}: the layer decides a reach at keep only"
        pure (k.1, k.2, c)
      let some otherwise := changeOf (← (← bound.getObjVal? "else").getStr?) | throw "unknown else"
      let keys ← match bound.getObjVal? "reachKeys" with
        | .ok ks => do (← ks.getArr?).toList.mapM (·.getStr?)
        | .error _ => pure []
      bounds := bounds ++ [{ callback := index, entries, otherwise, keys : Bound }]
    if !bounds.isEmpty then out := out.insert name { bounds, params := params.length }
  return out

end PaperRules
end Verification.HeapExpressionRules

open Verification Lean

/-- The layer of a unit, by its name: the rules' checker where the side
file bounds one of its callbacks, the ordinary checker otherwise. -/
def layerOf (units : Std.HashMap String HeapExpressionRules.PaperRules.Unit) : SinglePass.PassLayer :=
  fun name inputs _ _ _ _ _ _ base => match units.get? name with
    | some u => HeapExpressionRules.PaperRules.layer { u with inputs } base
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
        match verdict with
        | .ok _ => IO.println (Json.compress (Json.mkObj (if applies
            then [("unit", unit), ("acceptedUnderPaperRules", true), ("assumed", "paperKeptFactsSurvive")]
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
