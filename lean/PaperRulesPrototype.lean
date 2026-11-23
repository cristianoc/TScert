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

/-- A bound entry's region, relative to a parameter: its spine, or a field. -/
inductive Key where
  | spine
  | field (f : String)
  deriving Repr, BEq

/-- An effect variable's bound at a callback parameter: the callback's
position among the function's parameters, the bound's entries at the
function's parameters, and its `else`. -/
structure Bound where
  callback : Nat
  entries : List (Nat × Key × Footprints.Change)
  otherwise : Footprints.Change

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
  b.entries.map fun (p, key, c) =>
    let s := slotOf u d p
    (match key with
      | .spine => Footprints.Region.path s [] arraySpineKey
      | .field f => Footprints.Region.path s [] (.str f), c)

/-- A region without its class restriction. -/
def unrestricted : Footprints.Region → Footprints.Region
  | .inCls r _ => unrestricted r
  | r => r

/-- **The pair rule** (Bound and Anch, the meet): a pair `r : δ` of a fact's
support survives a call of the bounded callback when `r` is rooted at
storage the body allocated (Anch), or the bound keeps it: every bound entry
meeting `r` is within `δ`, and the bound's `else` is within `δ` unless an
entry is `r` itself (Bound). -/
def keepsPair (q : Footprints.SepQuery) (fresh : List Nat) (bound : Footprints.Footprint) (otherwise : Footprints.Change)
    (e : Footprints.Region × Footprints.Change) : Bool :=
  (rootSlot e.1).any fresh.contains ||
    (Footprints.respects q [e] bound && (otherwise.le e.2 || bound.any (unrestricted ·.1 == unrestricted e.1)))

/-- The facts of the call's entry the rules keep, past the call's result. -/
def kept (u : Unit) (b : Bound) (stable : Nat → String → Bool) (d : Nat) (k : Knowledge) : Knowledge :=
  let q := Footprints.knowledgeQuery k
  let fresh := freshSlots k
  let bound := boundAt u d b
  let keeps := fun (S : Footprints.Footprint) => S.all (keepsPair q fresh bound b.otherwise)
  let idx := k.indices.filter fun a => !a.fact.envOnly &&
    match a.fact.support? (.ofFirst stable) with
    | some S => keeps S
    | none => false
  let cells := k.cells.filter fun f => keeps [(Footprints.Region.field f.slot f.field, .keep)]
  { cells := HeapFacts.shift cells, indices := HeapKnowledge.shiftIndices idx }

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
      { out with cells := out.cells ++ add.cells, indices := out.indices ++ add.indices }
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

/-- A key `"x[*]"` or `"x.f"` at a parameter list. -/
def keyOf (params : List String) (key : String) : Option (Nat × Key) :=
  if key.endsWith "[*]" then
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
        pure (k.1, k.2, c)
      let some otherwise := changeOf (← (← bound.getObjVal? "else").getStr?) | throw "unknown else"
      bounds := bounds ++ [{ callback := index, entries, otherwise : Bound }]
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
