/- ============================================================================
   PROTOTYPE ONLY — SCHEDULED FOR DELETION UPON UNIFICATION
   Disposable experimental paper-rules executable (`docs/drafts/paper-rules-mode.md`).
   Must NEVER be imported by `lean/Verification/` or `lean/Main.lean`
   (enforced by `tests/prototype-isolation.mts`). Replaced upon unification by
   proved rules instantiating `Verification.Paper.EffectLanguage.Rules.Semantics`.
   ============================================================================ -/

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
a field, every field, its reach through the access paths its declared type
admits (`"x.**"`), or confined module-private state (`"@state"`). -/
inductive Key where
  | spine
  | cells
  | field (f : String)
  | fields
  | reach (acc : List AccPath)
  | moduleState
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
  callerComponents : List ParamEff := []
  /-- Non-escaping scoped inline callbacks passed at this call: `(closureSpan, paramIndex)`. -/
  scopedCallbacks : List ((Nat × Nat) × Nat) := []

/-- An unsafe assume `paperAssume(fact, "#n");`: the issue it names and its
line. The prototype checks the statement of the checked file as
`if (!(fact)) throw "#n";` (`assumedFile`), so past it the pass knows `fact`
as on the branch where it holds; the issue tracks either a verifier
extension or a proof the source does not yet give. -/
structure Assume where
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
  | .field x _ | .fields x | .cells x | .path x _ _ | .pathFields x _ | .pathCells x _ | .spine x _ | .elemSpines x _ => some x
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
at the key `[]`; none for a reach or confined module state, which are no
slot-rooted footprint regions. -/
def keyRegion (s : Nat) : Key → Option Footprints.Region
  | .spine => some (Footprints.Region.path s [] arraySpineKey)
  | .cells => some (Footprints.Region.cells s)
  | .field f => some (Footprints.Region.path s [] (.str f))
  | .fields => some (Footprints.Region.fields s)
  | .reach _ | .moduleState => none

/-- The bound's entries as regions at the call's slots. -/
def boundAt (u : Unit) (d : Nat) (b : Bound) : Footprints.Footprint :=
  b.entries.filterMap fun (p, key, c) => (keyRegion (slotOf u d p) key).map (·, c)

/-- The slots a reach's roots reach at a step, each with its access path:
a root at the empty path, closed under the read links `y = x.f` of a key
`f` the type declares at `x`'s path (`y` at that path followed by `f`) and
under alias links. The paper's reach follows the access paths of the type;
the knowledge gives the slots the body read along them. -/
def reachPairs (k : Knowledge) (roots : List (Nat × List AccPath)) : List (Nat × List AccPath × List String) :=
  let freads : List (Nat × Nat × String) := k.indices.filterMap fun atom =>
    if atom.cond.isSome then none else
    match atom.fact with
    | .guarded v [] t (.fieldRead v' c f) =>
      if v == v' && (t == .null || t == .undef) then some (v, c, f) else none
    | .fieldRead v c f => some (v, c, f)
    | _ => none
  let start := roots.map fun (s, acc) => (s, acc, ([] : List String))
  let step := fun (rs : List (Nat × List AccPath × List String)) => rs ++
    k.links.flatMap (fun l =>
      rs.filterMap fun (s, acc, a) =>
        if l.alias then
          if s == l.cell then some (l.value, acc, a) else if s == l.value then some (l.cell, acc, a) else none
        else match l.field with
          | .str f => if s == l.cell && acc.any (fun e => e.path == a && e.keys.contains f) then some (l.value, acc, a ++ [f]) else none
          | .sym _ => none) ++
    freads.flatMap fun (v, c, f) =>
      rs.filterMap fun (s, acc, a) =>
        if s == c && acc.any (fun e => e.path == a && e.keys.contains f) then some (v, acc, a ++ [f]) else none
  let rec go : Nat → List (Nat × List AccPath × List String) → List (Nat × List AccPath × List String)
    | 0, rs => rs
    | n + 1, rs =>
      let next := (step rs).eraseDups
      if next.length == rs.length then rs else go n next
  go (k.links.length + freads.length + 1) start.eraseDups

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
  | .elemSpines x p => pairs.any fun (s, acc, a) => s == x && acc.any fun e => e.path == a ++ p ++ ["[*]"] && e.array
  | .fields _ | .pathFields _ _ | .cls _ | .all => false

/-- The slot whose object's own location a region names: a field, the
fields or the spine at a slot itself. A path through a field, and an
array's element locations, may name storage older than the slot's object. -/
def ownSlot : Footprints.Region → Option Nat
  | .field x _ | .fields x => some x
  | .path x [] _ | .pathFields x [] | .spine x [] => some x
  | _ => none

/-- A change read at a region's category: on a spine, `init` and `scalar`
are `keep`; on contents, `extend` and `grow` are `scalar`
(`Change.onSpine`, `Change.onValue`). -/
def atCategory : Footprints.Region → Footprints.Change → Footprints.Change
  | .spine .., c | .elemSpines .., c => c.onSpine
  | _, c => c.onValue

/-- Whether a support region may overlap confined module-private state
`"@state"`: class/all regions, full field wildcards, or a cell location
(`Role.cell`, keyed by `"value"` in the calculus). Every other parameter- or
local-rooted region (a named field under any other key, a spine, or element
cells) is disjoint from confined module state by
`EffectLanguage.Model.closedOut_region_disjoint`. -/
def mayOverlapModState : Footprints.Region → Bool
  | .cls _ | .all | .fields _ | .pathFields _ _ => true
  | .field _ (.str "value") | .path _ [] (.str "value") => true
  | _ => false

/-- Whether a support region `r` is covered by a bound entry's region `b`,
modulo alias links (`sameSlot x y` when `x` and `y` denote the same object). -/
def coveredByBound (sameSlot : Nat → Nat → Bool) (r b : Footprints.Region) : Bool :=
  r == b || match r, b with
  | .field x k, .field y k' | .field x k, .path y [] k'
  | .path x [] k, .field y k' | .path x [] k, .path y [] k' => sameSlot x y && k == k'
  | .spine x [], .path y [] k' => sameSlot x y && k' == arraySpineKey
  | .spine x p, .spine y q => sameSlot x y && p == q
  | .field x k, .fields y | .path x [] k, .fields y => sameSlot x y && k != arraySpineKey
  | .fields x, .fields y | .pathFields x [], .fields y => sameSlot x y
  | .cells x, .cells y | .pathCells x [], .cells y => sameSlot x y
  | _, _ => false

/-- **The pair rule**: the callback's effect `ε` is within `δ` on `r`
(Definition "Order") when one of the two effects `ε` is included in is
(the meet, rules Anch and Bound):

- Anch, `{old: any}` (generalized for confined module state): `r` is an own
  location of an object the body allocated, so no `old` or confined module
  location; its `else` is `keep`;
- Bound: every bound entry not disjoint from `r` is within `δ` (the
  existing `respects`, with its separation query), any confined module-state
  entry `modChange` that may overlap `r` is within `δ`, and the bound's `else`
  is within `δ` unless `r` lies in an entry: covered by a bound entry's region
  (up to alias links), or in a reach entry's declared reach. -/
def keepsPair (q : Footprints.SepQuery) (sameSlot : Nat → Nat → Bool) (fresh : List Nat)
    (bound : Footprints.Footprint) (otherwise : Footprints.Change)
    (reach : Footprints.Region → Bool) (modChange : Footprints.Change)
    (e : Footprints.Region × Footprints.Change) : Bool :=
  (ownSlot e.1).any (fun s => fresh.any (sameSlot s)) ||
    (Footprints.respects q [e] bound &&
      (!mayOverlapModState e.1 || (atCategory e.1 modChange).le e.2) &&
      ((atCategory e.1 otherwise).le e.2 || reach e.1 || bound.any (fun b => coveredByBound sameSlot e.1 b.1)))

/-- An effect the layer reads at a call: its entries at the call's slots,
its `else`, the roots of its reach entries with their access paths, the
maximum change on confined module state `"@state"`, and the slots of storage
it leaves alone by Anch (none at a call whose effect is not an anchored
variable). -/
structure CallEff where
  fresh : List Nat
  bound : Footprints.Footprint
  otherwise : Footprints.Change
  roots : List (Nat × List AccPath)
  modChange : Footprints.Change := .keep

/-- The facts of the call's entry that every effect of `effs` keeps, past
the call's result. The effects are the components of one call's effect
(its union), or of several calls the layer cannot tell apart: the facts
every one keeps survive. -/
def keptBy (effs : List CallEff) (stable : Nat → String → Bool) (k : Knowledge) : Knowledge :=
  let q := Footprints.knowledgeQuery k
  let sameSlot := fun (x y : Nat) => x == y || (HeapLinks.aliases k.links x).contains y
  let prepared := effs.map fun c => (c, inReach (reachPairs k c.roots))
  let keeps := fun (S : Footprints.Footprint) => !prepared.isEmpty && prepared.all fun (c, reach) =>
    S.all (keepsPair q sameSlot c.fresh c.bound c.otherwise reach c.modChange)
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

/-- The largest change stated for confined module state `"@state"` in a list
of entries (`keep` when none). -/
def modChangeOf (es : List (Nat × Key × Footprints.Change)) : Footprints.Change :=
  es.foldl (fun acc (_, key, ch) => match key with | .moduleState => acc.max ch | _ => acc) .keep

/-- At a call of a bounded callback parameter: the callback's effect is
the variable, within the bound (Bound) and within `{old: any}` (Anch). -/
def kept (u : Unit) (b : Bound) (stable : Nat → String → Bool) (d : Nat) (k : Knowledge) : Knowledge :=
  let roots := reachRoots (b.entries.map fun (p, key, c) => (slotOf u d p, key, c))
  keptBy [{ fresh := freshSlots k, bound := boundAt u d b, otherwise := b.otherwise, roots,
            modChange := modChangeOf b.entries }] stable k

/-- At a call of a function with effect parameters (rule Inst's
conclusion): the call's effect is the callee's effect with each variable
replaced by its instance, and each instance is within its bound, so the
call's effect is within the union of the bounds and the callee's own
effect, read at the actual arguments' slots: one component each. No Anch:
the instance may change the caller's own storage. Confined module-state
entries (`"@state"`) require no argument slot. Where a parameter-rooted
entry's parameter receives no slot, nothing is kept. -/
def atCall (u : Unit) (d : Nat) (c : QCall) (args : List Tm) : Option (List CallEff) := do
  let entrySlot := fun (p : Nat) => match args[p]? with
    | some (.var a) => some (some a)
    | none | some .undef | some .nul | some .tru | some .fls
    | some (.num _) | some (.str _) | some (.bigint _) | some (.sym _) => some none
    | some _ => none
  let calleeEffs ← c.components.mapM fun pe => do
    let paramEntries := pe.entries.filter fun (_, key, _) => key != .moduleState
    let esOpt ← paramEntries.mapM fun (p, key, ch) => (entrySlot p).map fun oa => oa.map fun a => (a, key, ch)
    let es := esOpt.filterMap id
    let bound := es.filterMap fun (a, key, ch) => (keyRegion a key).map (·, ch)
    pure { fresh := [], bound, otherwise := pe.otherwise, roots := reachRoots es,
           modChange := modChangeOf pe.entries }
  let callerEffs := c.callerComponents.map fun pe =>
    let paramEntries := pe.entries.filter fun (_, key, _) => key != .moduleState
    let es := paramEntries.map fun (p, key, ch) => (slotOf u d p, key, ch)
    let bound := es.filterMap fun (a, key, ch) => (keyRegion a key).map (·, ch)
    { fresh := [], bound, otherwise := pe.otherwise, roots := reachRoots es,
      modChange := modChangeOf pe.entries : CallEff }
  pure (calleeEffs ++ callerEffs)

/-- The layer's step: the ordinary checker's output, and at a call of a
bounded callback parameter the facts the rules keep added to it. -/
def run {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} (u : Unit)
    (base : Checker G images) (j : Sequent ι) (k : Knowledge) (e : StepEvidence ι) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) : CheckResult ι Knowledge :=
  let r := base.run j k e codes sums
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
      let effs := spans.map fun sp => sp.bind fun sp => (u.calls.find? (·.span == sp)).bind (atCall u d · args)
      match (effs.mapM id).map List.flatten with
      | some (c :: cs) => add (keptBy (c :: cs) (stableFirst G j.context) k)
      | _ => r
  | _ => r

/-- **The assumption the prototype rests on**: the facts the layer keeps
at a call of a bounded callback parameter survive the call. Its premise is
the layer's run, which decides "allocated in the body" from the
allocation's separation fact and the bound from the side file. -/
axiom paperKeptFactsSurvive {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    (u : Unit) (base : Checker G images) :
    ∀ {j k e out codes sums}, (run u base j k e codes sums).value = some out →
      CodesSound G codes → SummariesSound G images sums → ∀ {ε ρ n W h},
      EnvOk G j.context ρ n W → HeapKnowledge.Holds k ε ρ h →
      WorldAdm W → HeapOk n W h → RefsOk W (instantiate 0 ρ j.term) → RootsOk W ρ →
      SafePost (excOf G) (meaning G j.type)
        (fun h' v => HeapKnowledge.Holds out ε (push v ρ) h')
        n W h (instantiate 0 ρ j.term)

/-- The layer's step is the ordinary checker's at every term but a call of
a slot. -/
theorem run_eq_base {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} (u : Unit)
    (base : Checker G images) {j : Sequent ι} {k e codes sums}
    (h : ∀ s t args, j.term ≠ .invoke (.var s) t args) :
    run u base j k e codes sums = base.run j k e codes sums := by
  unfold run
  split
  · rename_i s t args heq; exact absurd heq (h s t args)
  · rfl

/-- The layer: a checker whose `run` is the rules' step, and whose normal
effect is the ordinary checker's at every step it leaves to that checker. -/
def layer {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} (u : Unit)
    (base : Checker G images) : Checker G images where
  run := run u base
  sound := paperKeptFactsSurvive u base
  normal := fun j k e codes sums => match j.term with
    | .invoke (.var _) _ _ => Footprints.Closed.top
    | _ => base.normal j k e codes sums
  normal_sound := by
    intro j k e out codes sums hrun hc hs ε ρ n W h henv hk hW hok hrefs hn
    split at hn
    · exact absurd hn Footprints.Closed.top_ne_empty
    · rename_i hnot
      have heq := run_eq_base u base (j := j) (k := k) (e := e) (codes := codes) (sums := sums)
        (fun s t args hj => hnot s t args hj)
      rw [heq] at hrun
      exact base.normal_sound hrun hc hs henv hk hW hok hrefs hn

/-! ## The side file -/

def changeOf : String → Option Footprints.Change
  | "keep" => some .keep | "init" => some .init | "scalar" => some .scalar
  | "extend" => some .extend | "grow" => some .grow | "any" => some .any | _ => none

/-- A key at a parameter list: `"@state"` confined module-private state,
`"x[*]"` its spine, `"x[#]"` its cells, `"x.f"` a field, `"x.*"` every field,
`"x.**"` its reach with the access paths the side file gives; none for any
other key (a path through a field), which the layer does not read. -/
def keyOf (params : List String) (reach : String → Option (List AccPath)) (key : String) : Option (Nat × Key) :=
  let root := fun (n : Nat) => String.ofList (key.toList.take (key.length - n))
  if key == "@state" then some (0, .moduleState)
  else if key.endsWith ".**" then do
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
    let callerComponents ← match call.getObjVal? "callerBounds", call.getObjVal? "callerParams" with
      | .ok cb, .ok cp =>
        let cbs ← cb.getArr?
        let cps ← (← cp.getArr?).toList.mapM (·.getStr?)
        match cbs.toList.mapM (paramEff cps) with
        | some cs => pure cs
        | none => continue
      | _, _ => pure []
    let scopedCallbacks ← match call.getObjVal? "scopedCallbacks" with
      | .ok sc =>
        let arr ← sc.getArr?
        arr.toList.mapM fun item => do
          let sp ← item.getObjVal? "span"
          let span : Nat × Nat := (← (← sp.getArrVal? 0).getNat?, ← (← sp.getArrVal? 1).getNat?)
          let paramIndex ← (← item.getObjVal? "paramIndex").getNat?
          pure (span, paramIndex)
      | .error _ => pure []
    let c : QCall := { span, components, callerComponents, scopedCallbacks }
    let u := (out.get? caller).getD { bounds := [], params := 0 }
    out := out.insert caller { u with calls := u.calls ++ [c] }
  -- Each unit's unsafe assumes whose form the side script read.
  let assumes ← match side.getObjVal? "assumes" with
    | .ok a => a.getArr?
    | .error _ => pure #[]
  for a in assumes do
    if (a.getObjValAs? Bool "ok").toOption != some true then continue
    let caller ← (← a.getObjVal? "caller").getStr?
    let issue ← (← a.getObjVal? "issue").getStr?
    let line ← (← a.getObjVal? "line").getNat?
    let u := (out.get? caller).getD { bounds := [], params := 0 }
    out := out.insert caller { u with assumes := u.assumes ++ [{ issue, line }] }
  return out

/-- The parsed file with each unsafe assume's statement
`paperAssume(fact, "#n");` (an expression statement calling `paperAssume`
with two arguments) replaced by `if (!(fact)) throw "#n";`: the pass
lowers `fact` as a condition and learns from it on the branch where it
holds, as from any `if`. Where `fact` holds, the two statements have the
same normal continuation. -/
partial def assumedAst : Lean.Json → Lean.Json
  | .obj kvs =>
    let j := Lean.Json.obj (kvs.map fun _ v => assumedAst v)
    match j.getObjValAs? String "k", j.getObjVal? "e", j.getObjVal? "pos" with
    | .ok "effect", .ok call, .ok pos =>
      match call.getObjValAs? String "k", call.getObjVal? "callee", call.getObjVal? "args" with
      | .ok "apply", .ok callee, .ok (.arr #[fact, issue]) =>
        if (callee.getObjValAs? String "k").toOption == some "id" &&
            (callee.getObjValAs? String "name").toOption == some "paperAssume" then
          let factPos := (fact.getObjVal? "pos").toOption.getD pos
          Lean.Json.mkObj [("k", "if"), ("pos", pos),
            ("cond", Lean.Json.mkObj [("k", "not"), ("pos", factPos), ("e", fact)]),
            ("then", Lean.Json.arr #[Lean.Json.mkObj [("k", "throw"), ("pos", pos), ("e", issue)]]),
            ("else_", Lean.Json.null)]
        else j
      | _, _, _ => j
    | _, _, _ => j
  | .arr xs => .arr (xs.map assumedAst)
  | j => j

/-- The parsed file with the unsafe assumes of the checked file read as
`assumedAst` reads them, and its imported modules (`modules`) as written:
their interfaces were established over the source as written, and an
importer's check compares each module with its interface. -/
def assumedFile : Lean.Json → Lean.Json
  | .obj kvs => .obj (kvs.map fun k v => if k == "modules" then v else assumedAst v)
  | j => assumedAst j

/-- Whether `name` has a verified non-escaping scoped callback at
`(closureSpan, callSpan)`. -/
def wantsClosure (units : Std.HashMap String Unit) (name : String)
    (closureSpan callSpan : Option (Nat × Nat)) : Bool :=
  match units.get? name, closureSpan, callSpan with
  | some u, some clSp, some caSp =>
    u.calls.any fun c => c.span == caSp && c.scopedCallbacks.any fun (sp, _) => sp == clSp
  | _, _, _ => false

/-- **Rule Callback-Inv** (scoped callback invariant): at a call `H(..., cb)` to a
quantified function whose callback parameter does not escape, every caller fact
holding at the call whose support is kept by every component of the call's effect
(`own(H)` and `cb`'s instance/bound) and whose slots all resolve (modulo alias
links) to captures of `cb` holds at every invocation of `cb`, and is supplied on
entry to `cb`'s code graph. -/
def closureFacts (units : Std.HashMap String Unit) {ι : Type} [DecidableEq ι] [Hashable ι]
    [CertificateProducer.Instantiates ι] (G : NormalGraph ι) (site : SinglePass.ClosureSite ι) :
    List HeapKnowledge.IndexAtom :=
  match units.get? site.unitName, site.closureSpan, site.callSpan, site.callTerm with
  | some u, some clSp, some caSp, .invoke (.var _) _ args =>
    let matching := u.calls.filter fun c =>
      c.span == caSp && c.scopedCallbacks.any fun (sp, pi) => sp == clSp && pi == site.argIndex
    let u' := { u with inputs := site.unitInputs }
    let d := site.callContext.length
    match (matching.mapM (atCall u' d · args)).map List.flatten with
    | some (e0 :: es) =>
      let effs := e0 :: es
      let k := site.callKnowledge
      let q := Footprints.knowledgeQuery k
      let sameSlot := fun (x y : Nat) => x == y || (HeapLinks.aliases k.links x).contains y
      let stable := stableFirst G site.callContext
      let keeps := fun (S : Footprints.Footprint) => effs.all fun ce =>
        S.all (keepsPair q sameSlot ce.fresh ce.bound ce.otherwise (inReach (reachPairs k ce.roots)) ce.modChange)
      let remap := fun (x : Nat) =>
        site.captureSlots.zipIdx.findSome? fun (capOpt, idx) =>
          capOpt.bind fun s => if sameSlot x s then some (site.captureOffset + idx) else none
      k.indices.filterMap fun a =>
        if !a.fact.entrySlots.isEmpty then none
        else
          let survives := a.fact.envOnly || match a.fact.support? (.ofFirst stable) with
            | some S => keeps S
            | none => false
          if !survives then none
          else
            let cond' : Option (Option Nat) := match a.cond with
              | none => some none
              | some c => (remap c).map some
            match a.fact.mapM remap, cond' with
            | some f, some c => some { a with fact := f, cond := c }
            | _, _ => none
    | _ => []
  | _, _, _, _ => []

end PaperRules
end Verification.HeapExpressionRules

open Verification Lean

/-- The layer of a unit, by its name: the rules' checker where the side
file bounds one of its callbacks, the ordinary checker otherwise; plus
scoped callback invariant facts (`Callback-Inv`) for non-escaping inline
callbacks. -/
def layerOf (units : Std.HashMap String HeapExpressionRules.PaperRules.Unit) : SinglePass.PassLayer where
  checker := fun name inputs sites _ _ _ _ _ _ base => match units.get? name with
    | some u => HeapExpressionRules.PaperRules.layer { u with inputs, sites } base
    | none => base
  wantsClosure := HeapExpressionRules.PaperRules.wantsClosure units
  closureFacts := HeapExpressionRules.PaperRules.closureFacts units

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
        | .error reason =>
          IO.println (Json.compress (Json.mkObj [("unit", unit), ("refusal", (reason.take 400).toString)]))
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [side, ast, interfaces, key, depth] =>
    let some fuel := depth.toNat? | IO.eprintln "usage: depth is a number"; return 2
    let text ← IO.FS.readFile side
    match Json.parse text >>= HeapExpressionRules.PaperRules.unitsOf with
    | .error e => IO.eprintln s!"side file: {e}"; return 2
    | .ok units =>
      -- The parsed file with its unsafe assumes read as guards, beside it.
      match Json.parse (← IO.FS.readFile ast) with
      | .error e => IO.eprintln s!"parsed file: {e}"; return 2
      | .ok parsed =>
        let assumed := "fragment-assumed.json"
        IO.FS.writeFile assumed (HeapExpressionRules.PaperRules.assumedFile parsed).compress
        checkFile units assumed key fuel interfaces
  | _ =>
    IO.eprintln "usage: paper-rules-prototype <side.json> <ast.json> <interfaces.json> <file-key> <depth>"
    return 2
