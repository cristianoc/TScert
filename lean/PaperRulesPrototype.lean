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
a field, every field (at any path `p`), typed-array views (`"views"`), its
reach through the access paths its declared type admits (`"x.**"`), or
confined module-private state (`"@state"`). -/
inductive Key where
  | spine (p : List String := [])
  | cells (p : List String := [])
  | field (p : List String) (f : String)
  | fields (p : List String := [])
  | allFields
  | views
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
  /-- Source span `[start, end)` of the unit's name identifier, matching
  `Fragment.Function.namePos`. -/
  namePos : Option (Nat × Nat) := none
  bounds : List Bound
  /-- The calls of the unit to functions with effect parameters. -/
  calls : List QCall := []
  /-- Spans of unannotated calls in the unit, so span matching never confuses
  an annotated call with an unannotated call at the same lowered term and width. -/
  unannotatedCalls : List (Nat × Nat) := []
  /-- Spans of direct element writes `arr[i] = v` that must be certified as
  in-bounds `Dense` writes (`ExpressionEffects.denseWriteStep`) for the unit's
  stated `Effects<P, T>`. -/
  denseWrites : List (Nat × Nat) := []
  /-- Precomputed flag: true when some span in `denseWrites` has no matching
  `.writeAt` site in `sites` (set once in `layerOf`). -/
  missingDenseSite : Bool := false
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
  | .spine p => some (Footprints.Region.path s p arraySpineKey)
  | .cells [] => some (Footprints.Region.cells s)
  | .cells p => some (Footprints.Region.pathCells s p)
  | .field p f => some (Footprints.Region.path s p (.str f))
  | .fields [] => some (Footprints.Region.fields s)
  | .fields p => some (Footprints.Region.pathFields s p)
  | .views => some (Footprints.Region.cls .views)
  | .allFields | .reach _ | .moduleState => none

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

/-- Whether a support region may overlap named object fields (`"fields"`,
`Role.field`): array spines, array element cells, and element spines are
disjoint from `Role.field`. -/
def mayOverlapFields : Footprints.Region → Bool
  | .spine _ _ | .cells _ | .pathCells _ _ | .elemSpines _ _ => false
  | .field _ k | .path _ _ k => k != arraySpineKey
  | .cls s => s.value
  | _ => true

/-- Whether a support region `r` is covered by a bound entry's region `b`,
modulo alias links (`sameSlot x y` when `x` and `y` denote the same object). -/
def coveredByBound (sameSlot : Nat → Nat → Bool) (r b : Footprints.Region) : Bool :=
  r == b || match r, b with
  | .field x k, .field y k' | .field x k, .path y [] k'
  | .path x [] k, .field y k' | .path x [] k, .path y [] k' => sameSlot x y && k == k'
  | .spine x p, .path y q k' => sameSlot x y && p == q && k' == arraySpineKey
  | .path x p k, .path y q k' => sameSlot x y && p == q && k == k'
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
  entry `modChange` that may overlap `r` is within `δ`, any `"fields"` entry
  `fieldsChange` that may overlap `r` is within `δ`, and the bound's `else`
  is within `δ` unless `r` lies in an entry: covered by a bound entry's region
  (up to alias links), or in a reach entry's declared reach. -/
def keepsPair (q : Footprints.SepQuery) (sameSlot : Nat → Nat → Bool) (fresh : List Nat)
    (bound : Footprints.Footprint) (otherwise : Footprints.Change)
    (reach : Footprints.Region → Bool) (modChange : Footprints.Change)
    (fieldsChange : Footprints.Change)
    (e : Footprints.Region × Footprints.Change) : Bool :=
  (ownSlot e.1).any (fun s => fresh.any (sameSlot s)) ||
    (Footprints.respects q [e] bound &&
      (!mayOverlapModState e.1 || (atCategory e.1 modChange).le e.2) &&
      (!mayOverlapFields e.1 || (atCategory e.1 fieldsChange).le e.2) &&
      ((atCategory e.1 otherwise).le e.2 || reach e.1 || bound.any (fun b => coveredByBound sameSlot e.1 b.1)))

/-- An effect the layer reads at a call: its entries at the call's slots,
its `else`, the roots of its reach entries with their access paths, the
maximum change on confined module state `"@state"`, the maximum change on
named object fields `"fields"`, and the slots of storage it leaves alone by
Anch (none at a call whose effect is not an anchored variable). -/
structure CallEff where
  fresh : List Nat
  bound : Footprints.Footprint
  otherwise : Footprints.Change
  roots : List (Nat × List AccPath)
  modChange : Footprints.Change := .keep
  fieldsChange : Footprints.Change := .keep

/-- Separation query combining `typeSpineQuery` with element-cell disjointness
for type-disjoint plain arrays (`Plain-Cells-Disj` in `Rules.lean` /
`Model.lean`: two plain arrays whose element types cannot overlap cannot share
an element cell; typed-array views are excluded by `tyArrayOrNonObj` because
`.subarray()` views may share cells). -/
def typeRegionQuery {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) :
    Footprints.SepQuery :=
  let spineQ := HeapExpressionRules.typeSpineQuery G Γ
  let cellSite : Footprints.Region → Option (Nat × List String)
    | .cells x => some (x, [])
    | .pathCells x p => some (x, p)
    | _ => none
  let isPlain := fun (x : Nat) (p : List String) =>
    match HeapExpressionRules.pathTys G Γ x p with
    | some Us => Us.all (HeapExpressionRules.tyArrayOrNonObj G)
    | none => false
  ⟨fun r s => spineQ.disjoint r s || match cellSite r, cellSite s with
    | some (x, px), some (y, py) =>
      decide (px.length ≤ 2) && decide (py.length ≤ 2) &&
      isPlain x px && isPlain y py &&
      HeapExpressionRules.typesPathSpinesApart G Γ x px y py
    | _, _ => false⟩

/-- Whether every occurrence of `.project .length []` in a linear clause has a
negative coefficient (a lower bound such as `1 <= elem.length`), which is
monotone under `.extend` of element spines. -/
def onlyLowerElemLengthLinear : LinearClause HeapKnowledge.Bound → Bool
  | .atom (.le form _) => form.all fun (b, c) => b != .project .length [] || c < 0
  | .atom (.ne form _) => form.all fun (b, _) => b != .project .length []
  | .either A B => onlyLowerElemLengthLinear A && onlyLowerElemLengthLinear B

/-- Whether every occurrence of `.project .length []` in a quantified body
clause is a monotone lower bound (preserved when element spines extend). -/
def onlyLowerElemLengthBody : BodyClause → Bool
  | .clause c => onlyLowerElemLengthLinear c
  | .guarded _ _ b => onlyLowerElemLengthBody b
  | .either A B => onlyLowerElemLengthBody A && onlyLowerElemLengthBody B

/-- The facts of the call's entry that every effect of `effs` keeps, past
the call's result. The effects are the components of one call's effect
(its union), or of several calls the layer cannot tell apart: the facts
every one keeps survive. -/
def keptBy {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι))
    (effs : List CallEff) (stable : Nat → String → Bool) (k : Knowledge) : Knowledge :=
  let c : Footprints.ReadContext :=
    { (Footprints.ReadContext.ofFirst stable) with arrayPath := HeapExpressionRules.arrayPathOf G Γ }
  let typeQ := typeRegionQuery G Γ
  let combine := fun (q : Footprints.SepQuery) => (⟨fun r s => q.disjoint r s || typeQ.disjoint r s⟩ : Footprints.SepQuery)
  let baseQ := combine (Footprints.knowledgeQuery k)
  let sameSlot := fun (x y : Nat) => x == y || (HeapLinks.aliases k.links x).contains y
  let prepared := effs.map fun c => (c, inReach (reachPairs k c.roots))
  let keeps := fun (q : Footprints.SepQuery) (S : Footprints.Footprint) => !prepared.isEmpty && prepared.all fun (c, reach) =>
    S.all (keepsPair q sameSlot c.fresh c.bound c.otherwise reach c.modChange c.fieldsChange)
  let rec keepsFact (gs : List (Nat × GuardTag)) : IndexFact → Bool
    | .guarded s [] t B => keepsFact ((s, t) :: gs) B
    | F =>
      let q := if gs.isEmpty then baseQ else combine (Footprints.knowledgeQueryUnder k gs)
      match F.support? c with
      | some S =>
        let S := match F with
          | .every s p _ _ body =>
            if body.all onlyLowerElemLengthBody then
              S.map fun (r, ch) => if r == .elemSpines s p && ch == .keep then (r, .extend) else (r, ch)
            else S
          | _ => S
        keeps q S
      | none => false
  let idx := k.indices.filter fun a => !a.fact.envOnly && keepsFact [] a.fact
  let cells := k.cells.filter fun f => keeps baseQ [(Footprints.Region.field f.slot f.field, .keep)]
  -- A read link `y = x.f` holds while the field location of `x` at `f`
  -- keeps its contents: its support is that location at `keep`. An alias
  -- link reads no heap, and the ordinary output keeps it.
  let links := k.links.filter fun l => !l.alias && keeps baseQ [(Footprints.Region.path l.cell [] l.field, .keep)]
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

/-- The largest change stated for named object fields `"fields"` in a list
of entries (`keep` when none). -/
def fieldsChangeOf (es : List (Nat × Key × Footprints.Change)) : Footprints.Change :=
  es.foldl (fun acc (_, key, ch) => match key with | .allFields => acc.max ch | _ => acc) .keep

/-- At a call of a bounded callback parameter: the callback's effect is
the variable, within the bound (Bound) and within `{old: any}` (Anch). -/
def kept {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι))
    (u : Unit) (b : Bound) (stable : Nat → String → Bool) (d : Nat) (k : Knowledge) : Knowledge :=
  let roots := reachRoots (b.entries.map fun (p, key, c) => (slotOf u d p, key, c))
  let eff : CallEff := {
    fresh := freshSlots k, bound := boundAt u d b, otherwise := b.otherwise, roots := roots,
    modChange := modChangeOf b.entries, fieldsChange := fieldsChangeOf b.entries
  }
  keptBy G Γ [eff] stable k

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
    let paramEntries := pe.entries.filter fun (_, key, _) => key != .moduleState && key != .views && key != .allFields
    let viewEntries := pe.entries.filterMap fun (_, key, ch) =>
      if key == .views then some (Footprints.Region.cls .views, ch) else none
    let esOpt ← paramEntries.mapM fun (p, key, ch) => (entrySlot p).map fun oa => oa.map fun a => (a, key, ch)
    let es := esOpt.filterMap id
    let bound := viewEntries ++ es.filterMap fun (a, key, ch) => (keyRegion a key).map (·, ch)
    pure { fresh := [], bound, otherwise := pe.otherwise, roots := reachRoots es,
           modChange := modChangeOf pe.entries, fieldsChange := fieldsChangeOf pe.entries }
  let callerEffs := c.callerComponents.map fun pe =>
    let paramEntries := pe.entries.filter fun (_, key, _) => key != .moduleState && key != .views && key != .allFields
    let viewEntries := pe.entries.filterMap fun (_, key, ch) =>
      if key == .views then some (Footprints.Region.cls .views, ch) else none
    let es := paramEntries.map fun (p, key, ch) => (slotOf u d p, key, ch)
    let bound := viewEntries ++ es.filterMap fun (a, key, ch) => (keyRegion a key).map (·, ch)
    { fresh := [], bound, otherwise := pe.otherwise, roots := reachRoots es,
      modChange := modChangeOf pe.entries, fieldsChange := fieldsChangeOf pe.entries : CallEff }
  pure (calleeEffs ++ callerEffs)

/-- Whether a callee slot holds an intrinsic exact-write operation (such as
`%SetIndex%`), never a user-annotated call. -/
def isExactWriteCallee {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (s : Nat) : Bool :=
  match Γ[s]? with
  | some F => match PositiveRules.expand G F with
    | [PositiveNormalization.Clause.arrs L _] | [PositiveNormalization.Clause.callable _ _ L _ _] =>
        L.any fun p => (PromiseCalls.exactWriteOf p.effect).isSome
    | _ => false
  | none => false

/-- Whether any required dense-write span in `u.denseWrites` has no lowered
`.writeAt` site in `u.sites` (soundly refusing unmatched spans). -/
def hasMissingDenseSite (u : Unit) : Bool :=
  u.denseWrites.any fun sp =>
    !u.sites.any fun (t, _, s) => s == some sp && match t with | .writeAt .. => true | _ => false

/-- The layer's step: the ordinary checker's output, certifying any required
in-bounds `Dense` writes (`u.denseWrites`) via `ExpressionEffects.denseWriteStep`,
and at a call of a bounded callback parameter or annotated callee adding the
facts the rules keep to it. -/
def run {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} (u : Unit)
    (base : Checker G images) (j : Sequent ι) (k : Knowledge) (e : StepEvidence ι) (codes : CodeEntry ι → Bool)
    (sums : List (ReadSummary ι)) : CheckResult ι Knowledge :=
  if u.missingDenseSite then failure else
  let r := base.run j k e codes sums
  if base.normal j k e codes sums == .empty then r else
  match j.term with
  | .writeAt .. =>
    let isDenseSite := !u.denseWrites.isEmpty && u.sites.any fun (t, w, sp) =>
      t == j.term && w == j.context.length && sp.any (u.denseWrites.contains ·)
    if isDenseSite && !ExpressionEffects.denseWriteStep G j.context k j.term then failure else r
  | .invoke (.var s) _ args =>
    let d := j.context.length
    -- The callee is the parameter's slot or a copy of it (an alias link).
    let aliases := fun (x : Nat) => x == s || k.links.any fun l => l.alias &&
      ((l.cell == s && l.value == x) || (l.cell == x && l.value == s))
    let add := fun (add : Knowledge) => r.map fun out =>
      { out with cells := out.cells ++ add.cells, indices := out.indices ++ add.indices,
                 links := (out.links ++ add.links).eraseDups }
    match u.bounds.find? (fun b => aliases (slotOf u d b.callback)) with
    | some b => add (kept G j.context u b (stableFirst G j.context) d k)
    | none =>
      if isExactWriteCallee G j.context s then r else
      let spans := u.sites.filterMap fun (t, w, sp) =>
        if t == j.term && w == d then
          match sp with
          | some p => if u.calls.any (·.span == p) || u.unannotatedCalls.contains p then some (some p) else none
          | none => none
        else none
      let effs := spans.map fun sp => sp.bind fun sp => (u.calls.find? (·.span == sp)).bind (atCall u d · args)
      match (effs.mapM id).map List.flatten with
      | some (c :: cs) => add (keptBy G j.context (c :: cs) (stableFirst G j.context) k)
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
a slot or a write, when every dense-write span matches a site. -/
theorem run_eq_base {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} (u : Unit)
    (base : Checker G images) {j : Sequent ι} {k e codes sums}
    (hmiss : u.missingDenseSite = false)
    (h : (base.normal j k e codes sums == .empty) = true ∨
      ((∀ s t args, j.term ≠ .invoke (.var s) t args) ∧ (∀ f o v, j.term ≠ .writeAt f o v))) :
    run u base j k e codes sums = base.run j k e codes sums := by
  unfold run
  simp only [hmiss, Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · rename_i hne
    have ⟨hnotI, hnotW⟩ := h.resolve_left hne
    split
    · rename_i f o v heq; exact absurd heq (hnotW f o v)
    · rename_i s t args heq; exact absurd heq (hnotI s t args)
    · rfl

/-- The layer: a checker whose `run` is the rules' step, and whose normal
effect is the ordinary checker's wherever the ordinary checker is pure or
at every step it leaves to that checker. -/
def layer {ι : Type} [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G} (u : Unit)
    (base : Checker G images) : Checker G images where
  run := run u base
  sound := paperKeptFactsSurvive u base
  normal := fun j k e codes sums =>
    if u.missingDenseSite then Footprints.Closed.top
    else if base.normal j k e codes sums == .empty then base.normal j k e codes sums
    else match j.term with
      | .invoke (.var _) _ _ | .writeAt .. => Footprints.Closed.top
      | _ => base.normal j k e codes sums
  normal_sound := by
    intro j k e out codes sums hrun hc hs ε ρ n W h henv hk hW hok hrefs hn
    split at hn
    · exact absurd hn Footprints.Closed.top_ne_empty
    · rename_i hmiss
      have hmiss' : u.missingDenseSite = false := by cases h : u.missingDenseSite <;> simp_all
      split at hn
      · rename_i hemp
        have heq := run_eq_base u base (j := j) (k := k) (e := e) (codes := codes) (sums := sums) hmiss' (.inl hemp)
        rw [heq] at hrun
        exact base.normal_sound hrun hc hs henv hk hW hok hrefs hn
      · split at hn
        · exact absurd hn Footprints.Closed.top_ne_empty
        · exact absurd hn Footprints.Closed.top_ne_empty
        · rename_i hnotI hnotW
          have heq := run_eq_base u base (j := j) (k := k) (e := e) (codes := codes) (sums := sums) hmiss'
            (.inr ⟨fun s t args hj => hnotI s t args hj, fun f o v hj => hnotW f o v hj⟩)
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
  let splitPath := fun (s : String) => match s.splitOn "." with
    | r :: p => (params.idxOf? r).map (·, p)
    | [] => none
  if key == "@state" then some (0, .moduleState)
  else if key == "views" then some (0, .views)
  else if key == "fields" then some (0, .allFields)
  else if key.endsWith ".**" then do
    let acc ← reach key
    (params.idxOf? (root 3)).map (·, .reach acc)
  else if key.endsWith "[*]" then (splitPath (root 3)).map fun (i, p) => (i, .spine p)
  else if key.endsWith "[#]" then (splitPath (root 3)).map fun (i, p) => (i, .cells p)
  else if key.endsWith ".*" then (splitPath (root 2)).map fun (i, p) => (i, .fields p)
  else match key.splitOn "." with
    | r :: rest => match rest.reverse with
      | f :: pr => (params.idxOf? r).map (·, .field pr.reverse f)
      | [] => none
    | [] => none

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
  let mut namePositions : Std.HashMap String (Nat × Nat) := {}
  for (name, info) in kvs.toArray do
    if let .ok np := info.getObjVal? "namePos" then
      if let (.ok s, .ok e) := (np.getArrVal? 0 >>= (·.getNat?), np.getArrVal? 1 >>= (·.getNat?)) then
        namePositions := namePositions.insert name (s, e)
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
    let denseWrites ← match info.getObjVal? "denseWrites" with
      | .ok dw =>
        let arr ← dw.getArr?
        arr.toList.mapM fun sp => do
          pure (← (← sp.getArrVal? 0).getNat?, ← (← sp.getArrVal? 1).getNat?)
      | .error _ => pure []
    if (readable && !bounds.isEmpty) || !denseWrites.isEmpty then
      out := out.insert name {
        namePos := namePositions.get? name,
        bounds := if readable then bounds else [],
        denseWrites,
        params := params.length
      }
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
  -- Unannotated call spans per unit, to guard against span collisions.
  let unann ← match side.getObjVal? "unannotatedCalls" with
    | .ok a => a.getArr?
    | .error _ => pure #[]
  for item in unann do
    let caller ← (← item.getObjVal? "caller").getStr?
    let span ← item.getObjVal? "span"
    let span : Nat × Nat := (← (← span.getArrVal? 0).getNat?, ← (← span.getArrVal? 1).getNat?)
    let u := (out.get? caller).getD { bounds := [], params := 0 }
    out := out.insert caller { u with unannotatedCalls := u.unannotatedCalls ++ [span] }
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
        S.all (keepsPair q sameSlot ce.fresh ce.bound ce.otherwise (inReach (reachPairs k ce.roots)) ce.modChange ce.fieldsChange)
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
    | some u =>
      let u' := { u with inputs, sites }
      HeapExpressionRules.PaperRules.layer { u' with missingDenseSite := HeapExpressionRules.PaperRules.hasMissingDenseSite u' } base
    | none => base
  wantsClosure := HeapExpressionRules.PaperRules.wantsClosure units
  closureFacts := HeapExpressionRules.PaperRules.closureFacts units

/-- Each selected unit's group checked by the pass with the layer; a verdict
line per unit, accepted ones naming the assumption. -/
def checkFile (units : Std.HashMap String HeapExpressionRules.PaperRules.Unit) (astPath fileKey : String) (fuel : Nat)
    (interfacesPath : String) (prof : Bool := false) : IO UInt32 := do
  match ← RequestCli.prepareUnitsFile astPath fileKey fuel none {} interfacesPath true with
  | .error e => RequestCli.refuse e
  | .ok p =>
    if prof then SinglePass.profiling.set true
    let isPaperWalker (name : String) (namePos : Nat × Nat) : Bool :=
      match units.get? name with
      | some u => !u.bounds.isEmpty && u.namePos == some namePos
      | none => false
    let paperWalkers : List (String × Option SourceClaimJson.StandIn) :=
      p.fr.units.filterMap fun
        | (fn, _, none) => if isPaperWalker fn.name fn.namePos then some (fn.name, none) else none
        | _ => none
    -- Pre-seed `p.proposals` for groups containing a paper-rules callback
    -- walker (keyed by `(name, namePos)`) so `p.known` does not spend time
    -- running ordinary `PassProposals` on walkers that require the paper layer.
    for j in List.range p.fr.units.length do
      if let some (fn, _, none) := p.fr.units[j]? then
        if isPaperWalker fn.name fn.namePos then
          let g := ((p.fr.group j).head?).getD j
          let entries := (p.fr.group j).filterMap fun m => match p.fr.units[m]? with
            | some (u, _, none) => some (u.name, none)
            | _ => none
          p.proposals.modify (·.insert g entries)
    for i in p.units do
      let known ← p.known i
      let known := known ++ paperWalkers ++ (p.fr.group i).filterMap fun j => match p.fr.units[j]? with
        | some (f, _, none) => some (f.name, none)
        | _ => none
      let memo ← p.memo.get
      let unit := p.fr.unitId i
      match p.plan i known memo with
      | .error reason => IO.println (Json.compress (Json.mkObj [("unit", unit), ("refusal", reason)]))
      | .ok f =>
        let t0 ← if prof then IO.monoNanosNow else pure 0
        -- The verifier's own route (`PreparedFile.check`): the pass over the
        -- group with inferred loop-head facts, here with the layer.
        let (diagLines, verdict, _, _) := f.passGroupMode8 true p.force (f.givenAt p.givenLines) fuel (p.fr.group i)
          (located := true) (layer := some (layerOf units))
        if prof then
          let t1 ← IO.monoNanosNow
          IO.eprintln s!"profile unit {unit}: {(t1 - t0) / 1000000} ms"
        -- The unsafe assumes the group's units rely on, by issue and line.
        let assumes := (p.fr.group i).flatMap fun j => match p.fr.units[j]? with
          | some (fn, _, _) => ((units.get? fn.name).map (·.assumes)).getD []
          | none => []
        let assumesJson := Json.arr (assumes.map fun a => Json.str s!"{a.issue} at line {a.line}").toArray
        -- Every verdict accepted by the prototype stays its own and names the
        -- prototype's axiom (including when imported dependencies were
        -- established via `--module-interface` under the paper's rules).
        match verdict with
        | .ok _ => IO.println (Json.compress (Json.mkObj
            [("unit", unit), ("acceptedUnderPaperRules", true), ("assumed", "paperKeptFactsSurvive"),
             ("assumes", assumesJson)]))
        | .error reason =>
          let full := (← IO.getEnv "PAPER_TRACE").isSome
          if full then
            for dl in diagLines do IO.eprintln s!"diag {unit}: {dl}"
          let msg := if full then reason else (reason.take 400).toString
          IO.println (Json.compress (Json.mkObj [("unit", unit), ("refusal", msg)]))
    return 0

/-- Prototype module-interface step mirroring `SourceClaimJson.establishStep`,
skipping ordinary footprint proposals for functions with paper-rules callback
bounds (which ordinary `SinglePass` cannot establish without the paper layer). -/
def establishStepPaper (budget : PositiveCertificates.SearchBudget) (force : List String)
    (knownFor : String → List (String × Option SourceClaimJson.StandIn))
    (prepare : String → SourceClaimJson.FilePlans → SourceClaimJson.FilePlans)
    (check : SourceClaimJson.FilePlans → List Nat → List String × Except String (List String))
    (established : SourceClaimJson.Established) (tables : List (String × SourceClaimJson.RowTable))
    (m : SourceClaimJson.ModuleNeed) :
    SourceClaimJson.Established × List SourceClaimJson.ModuleVerdict × List String × List (String × SourceClaimJson.RowTable) :=
  let location := m.module.location
  let foreign := m.reads.filter (·.location != location)
  let rs := SourceClaimJson.readsOf foreign established
  let forced : SourceClaimJson.StandIns := if force.contains "imports" then
      { functions := m.names.map fun n => SourceClaimJson.StandIn.ofFormat n ⟨.keep, .keep, .keep⟩ true } else {}
  let planned := SinglePass.timedKind "lower: modules' plans" fun _ =>
    SourceClaimJson.fragmentPlansCore m.module.document location budget (some m.names) forced force (rs.map (·.1)) (rs.map (·.2))
      (closure := true) (proposed := true) (interfaceSlots := true) (known := knownFor location)
  match planned with
  | .error e => ([], [], [s!"{location}: its plans: {e.take 200}"], [])
  | .ok fm =>
    let fm := (prepare location fm).refuseRows foreign established tables
    let toCheck := SourceClaimJson.establishChecked m fm
    let checkedNotes := (toCheck.flatMap fm.fr.group).filterMap fun j => match fm.fr.units[j]? with
      | some (g, _, none) => (fm.fr.d.functions.find? fun c => c.name == g.name && c.namePos == g.namePos).map fun c =>
        s!"{location}#{g.name}: checked at {(toJson c.footprint).compress} onThrow {c.onThrow}"
      | _ => none
    let wire := fun (d : String) => if d.startsWith "module:" then d else SourceClaimJson.moduleUnitId location d
    let verdicts := toCheck.map fun l =>
      let group := fm.fr.group l
      let (lines, v) := SinglePass.timedKind "modules: pass" fun _ => check fm group
      (⟨SourceClaimJson.moduleUnitId location (fm.fr.unitId l), group.map (fun j => SourceClaimJson.moduleUnitId location (fm.fr.unitId j)),
        lines, v.map (·.map wire)⟩ : SourceClaimJson.ModuleVerdict)
    let accepted := verdicts.filterMap fun mv => match mv.verdict with
      | .ok deps => some (mv.unit, deps)
      | .error _ => none
    let ok := SourceClaimJson.establishedUnits accepted (established.map (·.2.2))
    let entries := m.names.map (SourceClaimJson.establishEntry location fm ok)
    let candidates := entries.filterMap (·.toOption)
    let ifaces := candidates.filterMap fun e => (fm.slots.lookup e.1.2).map (e.1.2, ·)
    let (rows, ifs, pos) := SourceClaimJson.encodeRowTableWithMap fm.F.store ifaces
    let table := SourceClaimJson.decodeRowTable rows ifs
    let tableOk := match table with
      | .ok t => SinglePass.work "rows: publication check" (SourceClaimJson.fileItem fm.fr.ast) fun _ =>
          SourceClaimJson.checkModuleTable fm.F.store t pos
      | .error _ => false
    let (laid, outsideD) := fm.laidOut
    let checked := candidates.map fun e => if !laid.contains e.1.2 then
        Except.error s!"{location}#{e.1.2}: not laid out: {((outsideD.find? (·.1 == e.1.2)).map (·.2)).getD ""}"
      else match fm.slots.lookup e.1.2, table with
      | some I, .ok t =>
        if (tableOk && SourceClaimJson.checkModuleEntry t pos e.1.2 I) ||
            (SinglePass.work "rows: publication check" (fm.fr.nameItem e.1.2) fun _ =>
              SourceClaimJson.moduleRowsAgree fm.F.store t e.1.2 I) then Except.ok e
        else .error s!"{location}#{e.1.2}: its interface rows refused by the store-map check"
      | none, _ => .error s!"{location}#{e.1.2}: no interface type"
      | _, .error w => .error s!"{location}#{e.1.2}: its interface rows: {w}"
    let published := checked.filterMap (·.toOption)
    (published, verdicts, checkedNotes ++ (entries ++ checked).filterMap (fun
      | .error e => if e.isEmpty then none else some e
      | .ok _ => none), match table with
      | .ok t => if published.isEmpty then [] else [(location, t)]
      | .error _ => [])

def establishModulesPaper (needs : List SourceClaimJson.ModuleNeed) (budget : PositiveCertificates.SearchBudget)
    (force : List String) (incoming : SourceClaimJson.Established)
    (knownFor : String → List (String × Option SourceClaimJson.StandIn))
    (prepare : String → SourceClaimJson.FilePlans → SourceClaimJson.FilePlans)
    (check : SourceClaimJson.FilePlans → List Nat → List String × Except String (List String))
    (incomingTables : List (String × SourceClaimJson.RowTable) := []) :
    Except String (SourceClaimJson.Established × List SourceClaimJson.ModuleVerdict × List String × List (String × SourceClaimJson.RowTable)) :=
  .ok (needs.foldl (fun (est, vs, ns, ts) m =>
    let (es, vs', ns', ts') := establishStepPaper budget force knownFor prepare check est (incomingTables ++ ts) m
    (est ++ es, vs ++ vs', ns ++ ns', ts ++ ts')) (incoming, [], [], []))

/-- A component interface established under the paper's rules, mirroring
`RequestCli.interfaceFile` with `layerOf` per module location. Modules with
unsafe `paperAssume`s are refused. -/
def interfaceFile (sideMap : Std.HashMap String (Std.HashMap String HeapExpressionRules.PaperRules.Unit))
    (path : String) (budget : PositiveCertificates.SearchBudget) : IO UInt32 := do
  let request ← RequestCli.readJson path
  let parsed : Except String (Json × List SourceClaimJson.ModuleVerdict × List String) := do
    let j ← request
    fieldsExactly j ["modules", "names", "dependencies", "force", "fuel", "mode"]
    let members ← jArr j "modules"
    let ds ← jArr j "dependencies"
    Fragment.symbolNumbersApart (members ++ ds.flatMap fun d =>
      (((d.getObjValD "interface").getObjValAs? (Array Json) "modules").toOption.getD #[]).toList.map
        (·.getObjValD "module"))
    let modules ← members.mapM fun m => do Fragment.decodeModule (← Fragment.canonicalSymbols m)
    let mut imported : List Fragment.ModuleAst := []
    for d in ds do
      fieldsExactly d ["key", "interface"]
      let _ ← d.getObjValAs? String "key"
      let i ← jField d "interface"
      fieldsExactly i ["modules"]
      for row in ← jArr i "modules" do
        let m ← Fragment.decodeModule (← Fragment.canonicalSymbols (← jField row "module"))
        if modules.any (·.location == m.location) || imported.any (·.location == m.location) then
          throw "component dependency overlaps"
        imported := imported ++ [m]
    let sc : SourceClaimJson.ImportScope := ⟨modules ++ imported, SourceClaimJson.ModuleCode.of (modules ++ imported)⟩
    let item := (modules.head?.map fun m => SourceClaimJson.fileItem m.document).getD ""
    let decoded ← ds.mapM fun (d : Json) => SinglePass.work "rows: decode interfaces" item fun _ =>
      SourceClaimJson.decodeInterfaces sc (d.getObjValD "interface")
    let incoming := decoded.flatMap (·.1)
    let incomingTables := decoded.flatMap (·.2)
    let rawNames ← jArr j "names"
    let mut requested : List (String × List String) := []
    for entry in rawNames do
      fieldsExactly entry ["location", "names"]
      let loc ← entry.getObjValAs? String "location"
      let ns : List String ← fromJson? (← jField entry "names")
      if requested.any (·.1 == loc) then throw s!"duplicate requested module {loc}"
      if !modules.any (·.location == loc) then throw s!"requested names for unknown module {loc}"
      requested := requested ++ [(loc, ns.eraseDups.mergeSort (· ≤ ·))]
    let own ← modules.mapM fun m => do
      let some ns := requested.lookup m.location | throw s!"missing requested names for {m.location}"
      let declared ← (← jArr m.document "functions").mapM fun f => f.getObjValAs? String "name"
      if ns.any (fun n => !declared.contains n) then throw s!"requested unknown function in {m.location}"
      let reads ← SourceClaimJson.moduleReads sc m ns
      return ({ module := m, names := ns, reads } : SourceClaimJson.ModuleNeed)
    let given : Std.HashMap String Json := {}
    let force : List String ← fromJson? (← jField j "force")
    let fuel ← j.getObjValAs? Nat "fuel"
    let mode ← j.getObjValAs? Nat "mode"
    if mode != 8 then throw "interface mode must be 8"
    let infer := true
    let prepare := fun location (f : SourceClaimJson.FilePlans) =>
      SinglePass.work "prepare: head facts" (SourceClaimJson.fileItem f.fr.ast) fun _ =>
      { f.withHeadFacts (RequestCli.forModule location given) false (inferred := infer) with proposalRefused := [] }
    let check := fun (f : SourceClaimJson.FilePlans) group =>
      SinglePass.work "check: group" (f.fr.workItem (group.headD 0)) fun _ =>
      let sha := (f.fr.ast.getObjValAs? String "sourceSha256").toOption
      let loc := (modules.find? fun m =>
        sha.isSome && (m.document.getObjValAs? String "sourceSha256").toOption == sha).map (·.location)
        |>.getD ((f.fr.ast.getObjValAs? String "location").toOption.getD
          ((f.fr.ast.getObjValAs? String "file").toOption.getD ""))
      let units := (sideMap.get? loc).getD {}
      let r := f.passGroupMode8 infer force (fun _ => []) fuel group
        (given := some (RequestCli.moduleGiven f.fr.ast given))
        (layer := some (layerOf units))
      (r.1, r.2.1)
    let knownFor := fun (loc : String) =>
      ((sideMap.get? loc).getD {}).toList.filterMap fun (name, u) => if !u.bounds.isEmpty then some (name, none) else none
    let (est, verdicts, notes, tables) ← establishModulesPaper
      (own.mergeSort (fun a b => a.module.location ≤ b.module.location)) budget force incoming knownFor prepare check incomingTables
    let encoded ← SourceClaimJson.encodeInterfaces modules est tables
    return (encoded, verdicts, notes)
  match parsed with
  | .error e => RequestCli.refuse e
  | .ok (j, verdicts, notes) =>
    if (← IO.getEnv "PAPER_TRACE").isSome then
      for mv in verdicts do
        match mv.verdict with
        | .ok _ => pure ()
        | .error e => IO.eprintln s!"paper-interface refused {mv.unit}: {(e.take 300).toString}"
      for n in notes do
        IO.eprintln s!"paper-interface note: {(n.take 300).toString}"
    match EffectCodec.document j with
    | .ok j => IO.println j.compress; return 0
    | .error e => RequestCli.refuse e

def parseSideMap (j : Json) : Except String (Std.HashMap String (Std.HashMap String HeapExpressionRules.PaperRules.Unit)) := do
  let .obj kvs := j | throw "side map: an object"
  let mut out : Std.HashMap String (Std.HashMap String HeapExpressionRules.PaperRules.Unit) := {}
  for (loc, side) in kvs.toArray do
    let units ← HeapExpressionRules.PaperRules.unitsOf side
    for (name, u) in units.toArray do
      if !u.assumes.isEmpty then
        throw s!"{loc}#{name}: module interface refused because it contains paperAssume"
    out := out.insert loc units
  return out

def main (args : List String) : IO UInt32 := do
  let prof := (← IO.getEnv "PAPER_PROFILE").isSome || (← IO.getEnv "TSCERT_PROFILE").isSome
  SinglePass.profiling.set prof
  let code ← match args with
    | ["--module-interface", sideMapPath, requestPath] =>
      let text ← IO.FS.readFile sideMapPath
      match Json.parse text >>= parseSideMap with
      | .error e => IO.eprintln s!"side map: {e}"; pure 2
      | .ok sideMap => interfaceFile sideMap requestPath {}
    | [side, ast, interfaces, key, depth] =>
      let some fuel := depth.toNat? | do IO.eprintln "usage: depth is a number"; pure 2
      let text ← IO.FS.readFile side
      match Json.parse text >>= HeapExpressionRules.PaperRules.unitsOf with
      | .error e => IO.eprintln s!"side file: {e}"; pure 2
      | .ok units =>
        -- The parsed file with its unsafe assumes read as guards, beside it.
        match Json.parse (← IO.FS.readFile ast) with
        | .error e => IO.eprintln s!"parsed file: {e}"; pure 2
        | .ok parsed =>
          let assumed := "fragment-assumed.json"
          IO.FS.writeFile assumed (HeapExpressionRules.PaperRules.assumedFile parsed).compress
          checkFile units assumed key fuel interfaces prof
    | _ =>
      IO.eprintln "usage: paper-rules-prototype <side.json> <ast.json> <interfaces.json> <file-key> <depth>"
      IO.eprintln "       paper-rules-prototype --module-interface <side-map.json> <request.json>"
      pure 2
  if prof then
    let kinds ← SinglePass.kindNanos.get
    let sorted := kinds.toList.mergeSort fun a b => a.2.1 ≥ b.2.1
    for (k, t, n) in sorted.take 25 do
      IO.eprintln s!"profile kind {t / 1000000} ms ({n}x): {k}"
  return code
