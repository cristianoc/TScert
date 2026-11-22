import Verification.Semantics.CallbackDemands
import Verification.Source.Claims.Json
import Verification.Source.Claims.MemberSettle
import Verification.Source.SourceRequests

/-! # Support-parametric callback demands: specification, inference, and caller discharge

General, shape-independent checker and inference for callback demands over
any `SourceRequest` and its `CodeRequest`s:

1. **Forward slot-origin analysis (`computeOrigins`)** over any
   `ControlFlow.Program`, tracking entry parameters (`param`), fresh local
   allocations (`fresh`), module siblings (`sibling`), field paths from
   parameters (`path`), closure literals (`closure`), and primitives (`prim`).
2. **Producer verification (`CallbackDemandSpec.checkProducer`)**:
   - Locally confined allocations (`isConfinedAlloc`) never escape into any
     call, non-confined write, closure capture, or return, so their fields
     are preserved unconditionally across any callback call
     (`CallbackDemands.valRun_preserves_ge_of_deep`).
   - Parameter-rooted regions project onto outer `callEnv` positions (`1 + i`)
     as published `CallbackDemand`s, with prefix-field stability checked across
     the producer's steps.
3. **Caller discharge & adapting-closure forwarding (`checkCallerDemands`)**:
   - At every call to a sibling carrying published `CallbackDemand`s, checks
     the actual callback argument:
     - Direct forwarding of an enclosing callback parameter;
     - Closure literal whose `CodeRequest` writes only fresh allocations
       (disjoint from all pre-existing parameter paths by
       `CallbackDemands.region_mem_lt_length` + `supportedAt_of_write_ge`) or
       respects the demand's regions/changes, and optionally invokes an
       enclosing callback parameter (forwarding the demand onto the caller's
       own parameter, as in `walkLines` / `walkRichInlineLineRanges`). -/

namespace Verification.SourceClaimJson
open Lean Verification ControlFlow ProgramTyping PositiveGraphs PositiveRules LabelStore
open CallbackDemands

/-! ## Forward slot-origin analysis -/

/-- What a slot holds in a program graph: an entry parameter, a fresh local
allocation at `allocNode`, a module sibling by name, a field path read from an
entry parameter, a closure literal `(codeIdx, captureOrigins)`, a primitive
value, or unknown. -/
inductive SlotOrigin where
  | param (p : Nat)
  | fresh (allocNode : Nat)
  | callerFresh (allocNode : Nat)
  | sibling (name : String)
  | path (p : Nat) (fs : List String)
  | closure (codeIdx : Nat) (caps : List SlotOrigin)
  | prim
  | unknown
  deriving Repr, BEq

/-- Join two origins at a control-flow merge. -/
def SlotOrigin.join (a b : SlotOrigin) : SlotOrigin :=
  if a == b then a else .unknown

/-- Join two slot-origin vectors point-wise. -/
def joinOrigins (a b : List SlotOrigin) : List SlotOrigin :=
  if a.length == b.length then (a.zip b).map fun (x, y) => x.join y
  else List.replicate (min a.length b.length) .unknown

/-- Look up the origin of slot `s` in `env`. -/
def originAt (env : List SlotOrigin) (s : Nat) : SlotOrigin :=
  env.getD s .unknown

/-- Whether an expression always evaluates to a primitive (location-free)
value. -/
def isPrimExpr : Tm → Bool
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _
  | .test .. | .arith .. | .lenOf .. => true
  | _ => false

/-- Match a closure allocation expression against a request's `codes` list. -/
def matchCodeIdx {ι : Type} (codes : List (RequestJson.CodeRequest ι)) (ar : Nat)
    (E : List Tm) (K : List (Continuation × Option Target)) (s : Nat) : Option Nat :=
  (codes.zipIdx.find? fun (q, _) =>
    q.entry.arity == ar && q.entry.exprs == E && q.entry.conts == K && q.entry.start == s).map (·.2)

/-- Whether an expression allocates a fresh plain object or array (including
a `.letE`-wrapped array literal `.letE (.arrLit ...) (.makeAt .absent ...)`). -/
def isFreshAllocExpr : Tm → Bool
  | .makeAt .absent _ _ | .arrLit _ => true
  | .letE _ b => isFreshAllocExpr b
  | _ => false

/-- Compute the origin of expression `e` at node `l` in slot environment `env`. -/
def exprOrigin {ι : Type} (codes : List (RequestJson.CodeRequest ι)) (l : Nat)
    (env : List SlotOrigin) : Tm → SlotOrigin
  | .var s => originAt env s
  | .letE a b =>
    let aOrig := exprOrigin codes l env a
    exprOrigin codes l (aOrig :: env) b
  | .readAt (.str f) (.var s) =>
    match originAt env s with
    | .param p => .path p [f]
    | .path p fs => .path p (fs ++ [f])
    | _ => .unknown
  | .makeAt (.graph ar E K s caps _ _ _) _ _ =>
    match matchCodeIdx codes ar E K s with
    | some ci =>
      let capOrigins := caps.map fun c => match c with
        | .var i => originAt env i
        | t => if isPrimExpr t then .prim else .unknown
      .closure ci capOrigins
    | none => .unknown
  | .makeAt .absent _ _ | .arrLit _ => .fresh l
  | .elemAt _ _ => .unknown
  | t => if isPrimExpr t then .prim else .unknown

/-- Apply a `Target`'s slot mapping to an environment (optionally with `pushed`
prepended at slot `0`). -/
def applyTargetMap (env : List SlotOrigin) (pushed : Option SlotOrigin) (tgt : Target) : List SlotOrigin :=
  let src := match pushed with
    | some v => v :: env
    | none => env
  match tgt.mapping with
  | none => src
  | some m => m.map fun i => originAt src i

/-- Successor transitions `(targetLabel, targetEnv)` of node `l`. -/
def nodeSuccessors (n : Node) (env : List SlotOrigin) (res : SlotOrigin) : List (Nat × List SlotOrigin) :=
  let main := match n.continuation with
    | .ret => []
    | .bind t => [(t.label, applyTargetMap env (some res) t)]
    | .effect t => [(t.label, applyTargetMap env none t)]
    | .branch y no => [(y.label, applyTargetMap env none y), (no.label, applyTargetMap env none no)]
    | .branchBind y no => [(y.label, applyTargetMap env (some .prim) y), (no.label, applyTargetMap env (some .prim) no)]
    | .tagBind _ y no => [(y.label, applyTargetMap env (some res) y), (no.label, applyTargetMap env (some res) no)]
  let h := match n.handler with
    | none => []
    | some ht => [(ht.label, applyTargetMap env (some .unknown) ht)]
  main ++ h

/-- Forward fixpoint origin analysis over a program graph `P` starting from
`start` with initial slot origins `initEnv`. -/
def computeOrigins {ι : Type} (codes : List (RequestJson.CodeRequest ι)) (P : Program)
    (start : Nat) (initEnv : List SlotOrigin) : Array (Option (List SlotOrigin)) := Id.run do
  let n := P.length
  let mut table : Array (Option (List SlotOrigin)) := Array.replicate n none
  if start < n then
    table := table.set! start (some initEnv)
  let rounds := (n + 1) * 4
  for _ in List.range rounds do
    let mut changed := false
    for l in List.range n do
      let some env := table[l]! | continue
      let some node := P[l]? | continue
      let res := exprOrigin codes l env node.expression
      for (tgt, nextEnv) in nodeSuccessors node env res do
        if tgt < n then
          match table[tgt]! with
          | none =>
            table := table.set! tgt (some nextEnv)
            changed := true
          | some prev =>
            let merged := joinOrigins prev nextEnv
            if merged != prev then
              table := table.set! tgt (some merged)
              changed := true
    if !changed then break
  return table

/-- Initial slot origins for a `SourceRequest` at `r.start`. -/
def requestInitOrigins {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceElaboration.SourceRequest σ ι) :
    List SlotOrigin :=
  let paramCount := r.inputs.length - r.siblings.length
  let paramOrigins :=
    if r.receiver then
      .unknown :: (List.range (paramCount - 1)).map .param
    else
      (List.range paramCount).map .param
  paramOrigins ++ r.siblings.map .sibling

/-- Compute per-node slot origins for a `SourceRequest`. -/
def requestOrigins {σ ι : Type} [Labels ι] [StoreView σ ι] (r : SourceElaboration.SourceRequest σ ι) :
    Array (Option (List SlotOrigin)) :=
  computeOrigins r.codes r.program r.start (requestInitOrigins r)

/-! ## Local confinement and term inspection -/

/-- Whether a term mentions a slot whose origin is `.fresh allocNode`. -/
def mentionsFresh (env : List SlotOrigin) (allocNode : Nat) : Tm → Bool
  | .var s => originAt env s == .fresh allocNode
  | .invoke f r args => mentionsFresh env allocNode f || mentionsFresh env allocNode r || args.any (mentionsFresh env allocNode)
  | .construct f args => mentionsFresh env allocNode f || args.any (mentionsFresh env allocNode)
  | .letE a b => mentionsFresh env allocNode a || mentionsFresh (.unknown :: env) allocNode b
  | .makeAt (.graph _ _ _ _ caps _ _ _) _ xs => caps.any (mentionsFresh env allocNode) || xs.any (mentionsFresh env allocNode)
  | .makeAt _ _ xs | .arrLit xs => xs.any (mentionsFresh env allocNode)
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => mentionsFresh env allocNode a
  | .indexAt a b | .writeAt _ a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
      mentionsFresh env allocNode a || mentionsFresh env allocNode b
  | .ite c a b | .setElem c a b =>
      mentionsFresh env allocNode c || mentionsFresh env allocNode a || mentionsFresh env allocNode b
  | _ => false

/-- Whether `allocNode`'s fresh local object is confined to `P`:
1. `allocNode` allocates a fresh plain object or array literal (`.makeAt .absent` or `.arrLit`)
   whose initializers do not escape another fresh object;
2. No node stores a `.fresh allocNode` value into any object whose origin is not `.fresh allocNode`;
3. No node passes a `.fresh allocNode` value to any `.invoke` or `.construct`;
4. No node captures a `.fresh allocNode` value in a closure (`.makeAt (.graph ...)`), merges it,
   throws it, or returns it. -/
def isConfinedAlloc (P : Program) (origins : Array (Option (List SlotOrigin))) (allocNode : Nat) : Bool :=
  match P[allocNode]? with
  | some n =>
    isFreshAllocExpr n.expression && (List.range P.length).all fun l =>
      match P[l]?, origins[l]?.join with
      | some node, some env =>
        let okExpr := match node.expression with
          | .var _ | .readAt _ _ => true
          | .writeAt _ target val =>
            -- Writing a field of the confined object itself (with a non-escaping value) is fine;
            -- storing the confined object into another object escapes it.
            !mentionsFresh env allocNode val || (match target with
              | .var s => originAt env s == .fresh allocNode
              | _ => false)
          | .setElem arr _ val =>
            !mentionsFresh env allocNode val || (match arr with
              | .var s => originAt env s == .fresh allocNode
              | _ => false)
          | .invoke f r args =>
            !mentionsFresh env allocNode f && !mentionsFresh env allocNode r && !args.any (mentionsFresh env allocNode)
          | .construct f args =>
            !mentionsFresh env allocNode f && !args.any (mentionsFresh env allocNode)
          | .makeAt (.graph _ _ _ _ caps _ _ _) _ xs =>
            !caps.any (mentionsFresh env allocNode) && !xs.any (mentionsFresh env allocNode)
          | .makeAt _ _ xs | .arrLit xs => !xs.any (mentionsFresh env allocNode)
          | .throw e | .spread e => !mentionsFresh env allocNode e
          | .merge _ a b | .makeKey a b => !mentionsFresh env allocNode a && !mentionsFresh env allocNode b
          | _ => true
        let okRet := match node.continuation with
          | .ret => !mentionsFresh env allocNode node.expression
          | _ => true
        okExpr && okRet
      | _, _ => true
  | none => false

/-- Whether `allocNode`'s fresh object/array in a caller is never stored into
any non-fresh object (e.g. `visited = []` or `walked = []` only captured by
closures and/or returned, never stored into `xs` or `prepared`). -/
def isFreshUnaliased (P : Program) (origins : Array (Option (List SlotOrigin))) (allocNode : Nat) : Bool :=
  match P[allocNode]? with
  | some n =>
    isFreshAllocExpr n.expression && (List.range P.length).all fun l =>
      match P[l]?, origins[l]?.join with
      | some node, some env =>
        match node.expression with
        | .writeAt _ target val =>
          !mentionsFresh env allocNode val || (match target with
            | .var s => originAt env s == .fresh allocNode
            | _ => false)
        | .setElem arr _ val =>
          !mentionsFresh env allocNode val || (match arr with
            | .var s => originAt env s == .fresh allocNode
            | _ => false)
        | _ => true
      | _, _ => true
  | none => false

/-! ## Region projection and prefix-stability checks -/

/-- Result of projecting a node-local support region `(r, δ)` at a callback
call node:
- `confined`: rooted at a locally confined allocation (discharged locally);
- `demand e`: projected onto outer `callEnv` parameter positions (`1 + p`);
- `unsupported`: cannot be discharged locally or projected cleanly. -/
inductive ProjectedEntry where
  | confined
  | demand (entry : Footprints.Region × Footprints.Change)
  | unsupported
  deriving Repr, DecidableEq

/-- Project a single region entry `(r, δ)` from node slot origins into either
locally confined or outer `callEnv` positions (`1 + p`). -/
def projectEntry (env : List SlotOrigin) (confined : List Nat) :
    Footprints.Region × Footprints.Change → ProjectedEntry
  | (.inCls r _, δ) => projectEntry env confined (r, δ)
  | (.field x k, δ) =>
    match originAt env x with
    | .fresh a => if confined.contains a then .confined else .unsupported
    | .param p => .demand (.field (p + 1) k, δ)
    | .path p fs => .demand (.path (p + 1) fs k, δ)
    | _ => .unsupported
  | (.fields x, δ) =>
    match originAt env x with
    | .fresh a => if confined.contains a then .confined else .unsupported
    | .param p => .demand (.fields (p + 1), δ)
    | .path p fs => .demand (.pathFields (p + 1) fs, δ)
    | _ => .unsupported
  | (.cells x, δ) =>
    match originAt env x with
    | .fresh a => if confined.contains a then .confined else .unsupported
    | .param p => .demand (.cells (p + 1), δ)
    | .path p fs => .demand (.pathCells (p + 1) fs, δ)
    | _ => .unsupported
  | (.path x p k, δ) =>
    match originAt env x with
    | .fresh a => if confined.contains a && p.isEmpty then .confined else .unsupported
    | .param q => .demand (if p.isEmpty then .field (q + 1) k else .path (q + 1) p k, δ)
    | .path q fs => .demand (.path (q + 1) (fs ++ p) k, δ)
    | _ => .unsupported
  | (.pathFields x p, δ) =>
    match originAt env x with
    | .fresh a => if confined.contains a && p.isEmpty then .confined else .unsupported
    | .param q => .demand (if p.isEmpty then .fields (q + 1) else .pathFields (q + 1) p, δ)
    | .path q fs => .demand (.pathFields (q + 1) (fs ++ p), δ)
    | _ => .unsupported
  | (.pathCells x p, δ) =>
    match originAt env x with
    | .fresh a => if confined.contains a && p.isEmpty then .confined else .unsupported
    | .param q => .demand (if p.isEmpty then .cells (q + 1) else .pathCells (q + 1) p, δ)
    | .path q fs => .demand (.pathCells (q + 1) (fs ++ p), δ)
    | _ => .unsupported
  | (.spine x p, δ) =>
    match originAt env x with
    | .fresh a => if confined.contains a && p.isEmpty then .confined else .unsupported
    | .param q => .demand (.spine (q + 1) p, δ)
    | .path q fs => .demand (.spine (q + 1) (fs ++ p), δ)
    | _ => .unsupported
  | (.cls _, _) | (.all, _) => .unsupported

/-- Extract every prefix field key read by a path-based region in `S`. -/
def prefixFieldsOf : Footprints.Region → List String
  | .path _ p _ | .pathFields _ p | .pathCells _ p | .spine _ p => p
  | .inCls r _ => prefixFieldsOf r
  | _ => []

private def prefixKeepGo (x : Nat) (acc : List String) : List String → List (Footprints.Region × Footprints.Change)
  | [] => []
  | f :: rest =>
    let r := if acc.isEmpty then Footprints.Region.field x (.str f)
             else Footprints.Region.path x acc (.str f)
    (r, .keep) :: prefixKeepGo x (acc ++ [f]) rest

/-- Prefix-preservation entries required alongside any path region so that
`readPath h₁ (ρ₀ x) p = readPath h₀ (ρ₀ x) p` holds across callback calls. -/
def prefixKeepEntries : Footprints.Region → List (Footprints.Region × Footprints.Change)
  | .path x p _ | .pathFields x p | .pathCells x p | .spine x p => prefixKeepGo x [] p
  | .inCls r _ => prefixKeepEntries r
  | _ => []

/-- Check that `P` does not mutate any prefix field of `support` on any
non-confined object (and makes no unframed non-pure call other than framed
callback nodes and pure intrinsics like `%ElementAt%`). -/
def checkPrefixPreserved {ι : Type} [Labels ι] (G : NormalGraph ι) (P : Program)
    (claims : List (CertificateProducer.PointClaim ι))
    (origins : Array (Option (List SlotOrigin))) (confined : List Nat)
    (framedNodes : List Nat) (support : Footprints.Footprint) : Bool :=
  let keys := (support.flatMap fun e => prefixFieldsOf e.1).eraseDups
  if keys.isEmpty then true
  else (List.range P.length).all fun l =>
    if framedNodes.contains l then true
    else match P[l]?, origins[l]?.join with
      | some node, some env =>
        match node.expression with
        | .writeAt (.str f) target _ =>
          !keys.contains f || (match target with
            | .var s => match originAt env s with
              | .fresh a => confined.contains a
              | _ => false
            | _ => false)
        | .writeAt _ _ _ => true
        | .invoke .. =>
          -- A non-framed call inside the producer preserves prefix fields if its
          -- stated/inferred effect respects `(cls values, keep)` (e.g. `%ElementAt%` is pure).
          match claims[l]? with
          | some c =>
            match callEffectAt G c node.expression with
            | some Φ => Φ.all fun (_, ch) => ch == .keep
            | none => false
          | none => false
        | .construct .. => false
        | _ => true
      | _, _ => true

/-- Merge a footprint entry into a demand list, strengthening change with `min`
(i.e. keeping the stronger / smaller change requirement: `keep < init < scalar < extend < grow < any`). -/
def changeMin (a b : Footprints.Change) : Footprints.Change :=
  if a.le b then a else b

def addDemandEntry (ds : List CallbackDemand) (param : Nat) (e : Footprints.Region × Footprints.Change) :
    List CallbackDemand :=
  let insertEntry (S : Footprints.Footprint) (e : Footprints.Region × Footprints.Change) : Footprints.Footprint :=
    if S.any (·.1 == e.1) then
      S.map fun (r, ch) => if r == e.1 then (r, changeMin ch e.2) else (r, ch)
    else S ++ [e]
  if ds.any (·.param == param) then
    ds.map fun d => if d.param == param then { d with support := insertEntry d.support e } else d
  else ds ++ [⟨param, [e]⟩]

/-- Whether slot `fnSlot` at claim `c` has a plain arrow type with no explicit
`Modifies<...>` effect (`Effect.ordinary` on every signature). Explicit
`Modifies<...>` contracts are left to stated-effect / read-only-frame checking. -/
def isOrdinaryCallbackSlot {ι : Type} [Labels ι] (G : NormalGraph ι)
    (c : CertificateProducer.PointClaim ι) (fnSlot : Nat) : Bool :=
  match c.context[fnSlot]? with
  | some T => match PositiveRules.expand G T with
    | [PositiveNormalization.Clause.arrs L S] | [PositiveNormalization.Clause.callable _ _ L S _] =>
      !L.isEmpty && S.isEmpty && L.all fun a => a.effect == CallEffects.Effect.ordinary
    | _ => false
  | none => false

/-- Find all nodes in `r.program` that directly invoke an unannotated callback
parameter `p` (returning `(nodeLabel, callEnvParamPos)` where `callEnvParamPos = p + 1`). -/
def findCallbackCallNodes {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceElaboration.SourceRequest σ ι) (origins : Array (Option (List SlotOrigin))) :
    List (Nat × Nat) :=
  let G := RequestJson.graph r.toRequest
  (List.range r.program.length).filterMap fun l =>
    match r.program[l]?, r.claims[l]?, origins[l]?.join with
    | some node, some c, some env =>
      match node.expression with
      | .invoke (.var fnSlot) _ _ =>
        match originAt env fnSlot with
        | .param p => if isOrdinaryCallbackSlot G c fnSlot then some (l, p + 1) else none
        | _ => none
      | _ => none
    | _, _, _ => none

/-- **Decidable producer check for `CallbackDemandSpec`**: verifies that:
1. Every allocation in `spec.confined` is locally confined (`isConfinedAlloc`);
2. Every framed node `(l, Ss)` in `spec.framed` is a direct call to its
   callback parameter `p` in `spec.calls`, passing no confined allocation;
3. Every entry of every support `S ∈ Ss` projects cleanly to either a confined
   allocation or an entry covered by `spec.demands` for parameter `p`;
4. Prefix fields of every path region in `spec.demands` are preserved across
   all non-framed steps of `r.program`. -/
def CallbackDemandSpec.checkProducer {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceElaboration.SourceRequest σ ι) (spec : CallbackDemandSpec) : Bool :=
  let G := RequestJson.graph r.toRequest
  let origins := requestOrigins r
  let confinedOk := spec.confined.all (isConfinedAlloc r.program origins)
  let framedNodes := spec.framed.map (·.1)
  let callsOk := spec.framed.all fun (l, Ss) =>
    match spec.calls.find? (·.1 == l), r.program[l]?, origins[l]?.join with
    | some (_, paramPos), some node, some env =>
      let isParamCall := match node.expression with
        | .invoke (.var fnSlot) recv args =>
          originAt env fnSlot == .param (paramPos - 1) &&
          spec.confined.all fun a => !mentionsFresh env a recv && !args.any (mentionsFresh env a)
        | _ => false
      let dem := (spec.demands.find? (·.param == paramPos)).map (·.support) |>.getD []
      let supportsOk := Ss.all fun S => S.all fun entry =>
        match projectEntry env spec.confined entry with
        | .confined => true
        | .demand (r', δ') => dem.any fun (rd, δd) => rd == r' && δd.le δ'
        | .unsupported => false
      isParamCall && supportsOk
    | _, _, _ => false
  let prefixOk := spec.demands.all fun d =>
    checkPrefixPreserved G r.program r.claims origins spec.confined framedNodes d.support
  confinedOk && callsOk && prefixOk

/-! ## Precise call effect extraction (sharpening `Array.prototype.push` via `statesExtension`) -/

/-- Extract the effective footprint of a call node `e` at claim `c`,
sharpening `(.field x arraySpineKey, .any)` to `(.field x arraySpineKey, .extend)`
whenever the selected signature states `statesExtension eff = true` (e.g.
`Array.prototype.push`, proved by `PromiseCalls.statesExtension_grows`). -/
def preciseCallEffectAt {ι : Type} [Labels ι] (G : NormalGraph ι)
    (c : CertificateProducer.PointClaim ι) (e : Tm) : Option Footprints.Footprint :=
  match e with
  | .invoke (.var j) _ _ => (c.context[j]?).bind fun T => match PositiveRules.expand G T with
    | [PositiveNormalization.Clause.arrs L S] | [PositiveNormalization.Clause.callable _ _ L S _] =>
      let effs := L.map (·.effect) ++ S.map (·.effect)
      if effs.isEmpty then none
      else some (effs.flatMap fun eff =>
        let fp := PromiseCalls.callerFrame eff e
        if PromiseCalls.statesExtension eff then
          fp.map fun (r, ch) => match r with
            | .field _ k => if k == arraySpineKey then (r, .extend) else (r, ch)
            | _ => (r, ch)
        else fp)
    | _ => none
  | _ => none

/-! ## Caller discharge & adapting-closure demand forwarding -/

/-- Origin-rooted region representation used to compare a closure's writes
against a callee's `CallbackDemand` instantiated at the caller's actuals. -/
inductive OriginRegion where
  | fresh (allocId : Int)       -- fresh allocation (negative = inside closure, non-neg = caller allocNode)
  | rootField (orig : SlotOrigin) (k : PropKey)
  | rootPath (orig : SlotOrigin) (p : List String) (k : PropKey)
  | rootFields (orig : SlotOrigin) (p : List String)
  | rootCells (orig : SlotOrigin) (p : List String)
  | rootSpine (orig : SlotOrigin) (p : List String)
  | cls (s : Footprints.Selector)
  | all
  deriving Repr, BEq

/-- Resolve a node-local `Footprints.Region` using `env` and an optional fresh
origin predicate (`isFreshOk`) into an `OriginRegion`. -/
def resolveOriginRegion (env : List SlotOrigin) (isClosureFresh : Nat → Bool)
    (isCallerFresh : Nat → Bool) : Footprints.Region → OriginRegion
  | .inCls r _ => resolveOriginRegion env isClosureFresh isCallerFresh r
  | .field x k =>
    match originAt env x with
    | .fresh a =>
      if isClosureFresh a then .fresh (-(a : Int) - 1)
      else .rootField (.fresh a) k
    | .callerFresh a =>
      if isCallerFresh a then .fresh (a : Int)
      else .rootField (.callerFresh a) k
    | .path p fs => .rootPath (.param p) fs k
    | o => .rootField o k
  | .fields x =>
    match originAt env x with
    | .fresh a =>
      if isClosureFresh a then .fresh (-(a : Int) - 1)
      else .rootFields (.fresh a) []
    | .callerFresh a =>
      if isCallerFresh a then .fresh (a : Int)
      else .rootFields (.callerFresh a) []
    | .path p fs => .rootFields (.param p) fs
    | o => .rootFields o []
  | .cells x =>
    match originAt env x with
    | .fresh a =>
      if isClosureFresh a then .fresh (-(a : Int) - 1)
      else .rootCells (.fresh a) []
    | .callerFresh a =>
      if isCallerFresh a then .fresh (a : Int)
      else .rootCells (.callerFresh a) []
    | .path p fs => .rootCells (.param p) fs
    | o => .rootCells o []
  | .path x p k =>
    match originAt env x with
    | .fresh a =>
      if p.isEmpty && isClosureFresh a then .fresh (-(a : Int) - 1)
      else .rootPath (.fresh a) p k
    | .callerFresh a =>
      if p.isEmpty && isCallerFresh a then .fresh (a : Int)
      else .rootPath (.callerFresh a) p k
    | .path q fs => .rootPath (.param q) (fs ++ p) k
    | o => if p.isEmpty then .rootField o k else .rootPath o p k
  | .pathFields x p =>
    match originAt env x with
    | .path q fs => .rootFields (.param q) (fs ++ p)
    | o => .rootFields o p
  | .pathCells x p =>
    match originAt env x with
    | .path q fs => .rootCells (.param q) (fs ++ p)
    | o => .rootCells o p
  | .spine x p =>
    match originAt env x with
    | .fresh a =>
      if p.isEmpty && isClosureFresh a then .fresh (-(a : Int) - 1)
      else .rootSpine (.fresh a) p
    | .callerFresh a =>
      if p.isEmpty && isCallerFresh a then .fresh (a : Int)
      else .rootSpine (.callerFresh a) p
    | .path q fs => .rootSpine (.param q) (fs ++ p)
    | o => .rootSpine o p
  | .cls s => .cls s
  | .all => .all

/-- Instantiate a callee demand region (rooted at `callEnv`: `1 + i` = actual `i`)
into the caller's `OriginRegion`s using the origins of the actual arguments passed
at the call site. -/
def instantiateDemandRegion (actualOrigins : List SlotOrigin) : Footprints.Region → Option OriginRegion
  | .inCls r _ => instantiateDemandRegion actualOrigins r
  | .field pos k =>
    if pos == 0 then none
    else match actualOrigins[pos - 1]? with
      | some (.path p fs) => some (.rootPath (.param p) fs k)
      | some o => some (.rootField o k)
      | none => none
  | .fields pos =>
    if pos == 0 then none
    else match actualOrigins[pos - 1]? with
      | some (.path p fs) => some (.rootFields (.param p) fs)
      | some o => some (.rootFields o [])
      | none => none
  | .cells pos =>
    if pos == 0 then none
    else match actualOrigins[pos - 1]? with
      | some (.path p fs) => some (.rootCells (.param p) fs)
      | some o => some (.rootCells o [])
      | none => none
  | .path pos p k =>
    if pos == 0 then none
    else match actualOrigins[pos - 1]? with
      | some (.path q fs) => some (.rootPath (.param q) (fs ++ p) k)
      | some o => some (if p.isEmpty then .rootField o k else .rootPath o p k)
      | none => none
  | .pathFields pos p =>
    if pos == 0 then none
    else match actualOrigins[pos - 1]? with
      | some (.path q fs) => some (.rootFields (.param q) (fs ++ p))
      | some o => some (.rootFields o p)
      | none => none
  | .pathCells pos p =>
    if pos == 0 then none
    else match actualOrigins[pos - 1]? with
      | some (.path q fs) => some (.rootCells (.param q) (fs ++ p))
      | some o => some (.rootCells o p)
      | none => none
  | .spine pos p =>
    if pos == 0 then none
    else match actualOrigins[pos - 1]? with
      | some (.path q fs) => some (.rootSpine (.param q) (fs ++ p))
      | some o => some (.rootSpine o p)
      | none => none
  | .cls _ | .all => none

/-- Whether a `SlotOrigin` is pre-existing at caller entry (so every location
reachable from it at any path lies strictly below any fresh allocation mark
`allocNode`, by `CallbackDemands.region_mem_lt_length`). -/
def isPreExistingOrigin : SlotOrigin → Bool
  | .param _ | .path _ _ => true
  | _ => false

/-- Root origin of an `OriginRegion`. -/
def originRegionRoot : OriginRegion → Option SlotOrigin
  | .rootField o _ | .rootPath o _ _ | .rootFields o _ | .rootCells o _ | .rootSpine o _ => some o
  | _ => none

/-- Whether a write `(writeReg, writeCh)` respects a demanded support entry
`(supReg, supCh)`:
1. `writeCh.le supCh` (change tolerance, e.g. `extend ⊑ grow`); OR
2. `writeReg` is a fresh allocation (inside the closure or an unaliased fresh
   allocation in the caller) while `supReg` is rooted at a pre-existing
   parameter/path (`CallbackDemands.region_mem_lt_length` +
   `supportedAt_of_write_ge`); OR
3. Disjoint keys (a named field write `k₁ ≠ k₂` vs a field/spine read); OR
4. Disjoint location classes (value field vs array spine). -/
def writeRespectsSupport (writeReg : OriginRegion) (writeCh : Footprints.Change)
    (supReg : OriginRegion) (supCh : Footprints.Change) : Bool :=
  if writeCh.le supCh then true
  else match writeReg, supReg with
    | .fresh _, _ =>
      match originRegionRoot supReg with
      | some o => isPreExistingOrigin o
      | none => false
    | .rootField _ k₁, .rootField _ k₂ => k₁ != k₂
    | .rootField _ k₁, .rootPath _ _ k₂ => k₁ != k₂
    | .rootPath _ _ k₁, .rootField _ k₂ => k₁ != k₂
    | .rootPath _ _ k₁, .rootPath _ _ k₂ => k₁ != k₂
    | .rootField _ k₁, .rootSpine _ _ => k₁ != arraySpineKey
    | .rootPath _ _ k₁, .rootSpine _ _ => k₁ != arraySpineKey
    | .rootSpine _ _, .rootField _ k₂ => k₂ != arraySpineKey
    | .rootSpine _ _, .rootPath _ _ k₂ => k₂ != arraySpineKey
    | .rootFields _ _, .rootSpine _ _ | .rootSpine _ _, .rootFields _ _ => true
    | .rootFields _ _, .rootCells _ _ | .rootCells _ _, .rootFields _ _ => true
    | .rootSpine _ _, .rootCells _ _ | .rootCells _ _, .rootSpine _ _ => true
    | .cls s, .rootSpine _ _ => !s.array && !s.view
    | .cls s, .rootField _ k₂ => if k₂ == arraySpineKey then !s.array && !s.view else !s.value
    | .cls s, .rootPath _ _ k₂ => if k₂ == arraySpineKey then !s.array && !s.view else !s.value
    | _, _ => false

/-- Project an `OriginRegion` back into the enclosing caller's `callEnv`
positions (`1 + p`) for forwarding a demand onto the caller's own callback
parameter. -/
def originRegionToCallerDemand : OriginRegion → Option Footprints.Region
  | .rootField (.param p) k => some (.field (p + 1) k)
  | .rootPath (.param p) fs k => some (.path (p + 1) fs k)
  | .rootFields (.param p) fs => some (if fs.isEmpty then .fields (p + 1) else .pathFields (p + 1) fs)
  | .rootCells (.param p) fs => some (if fs.isEmpty then .cells (p + 1) else .pathCells (p + 1) fs)
  | .rootSpine (.param p) fs => some (.spine (p + 1) fs)
  | _ => none

/-- Whether an expression performs no writes to existing heap storage (only
reads, arithmetic, conditionals, lets, or fresh allocations), so every step
keeps `h.IsPrefix h'` (`CallbackDemands.supportedAt_of_prefix`). -/
def isReadOnlyOrAllocExpr : Tm → Bool
  | .var _ | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => true
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => isReadOnlyOrAllocExpr a
  | .indexAt a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
      isReadOnlyOrAllocExpr a && isReadOnlyOrAllocExpr b
  | .ite c a b => isReadOnlyOrAllocExpr c && isReadOnlyOrAllocExpr a && isReadOnlyOrAllocExpr b
  | .letE a b => isReadOnlyOrAllocExpr a && isReadOnlyOrAllocExpr b
  | .makeAt .absent _ xs | .arrLit xs => xs.all isReadOnlyOrAllocExpr
  | .makeAt (.graph _ _ _ _ caps _ _ _) _ xs =>
      caps.all isReadOnlyOrAllocExpr && xs.all isReadOnlyOrAllocExpr
  | _ => false

private def originName : SlotOrigin → String
  | .param p => s!"param {p}"
  | .fresh a => s!"fresh@{a}"
  | .callerFresh a => s!"callerFresh@{a}"
  | .sibling nm => nm
  | .path p fs => s!"param {p}.{String.intercalate "." fs}"
  | .closure ci _ => s!"closure#{ci}"
  | .prim => "prim"
  | .unknown => "unknown"

private def keyName : PropKey → String
  | .str s => s
  | .sym i => s!"symbol({i})"

private def originRegionText : OriginRegion → String
  | .fresh a => s!"fresh({a})"
  | .rootField o k => s!"{originName o}.{keyName k}"
  | .rootPath o p k => s!"{originName o}.{String.intercalate "." p}.{keyName k}"
  | .rootFields o p => if p.isEmpty then s!"{originName o}.*" else s!"{originName o}.{String.intercalate "." p}.*"
  | .rootCells o p => if p.isEmpty then s!"{originName o}[*]" else s!"{originName o}.{String.intercalate "." p}[*]"
  | .rootSpine o p => if p.isEmpty then s!"{originName o}.[]" else s!"{originName o}.{String.intercalate "." p}.[]"
  | .cls s => s!"class(v={s.value},a={s.array},w={s.view})"
  | .all => "all"

private def changeName : Footprints.Change → String
  | .keep => "keep"
  | .init => "init"
  | .scalar => "scalar"
  | .extend => "extend"
  | .grow => "grow"
  | .any => "any"

/-- Result of checking one closure literal against an instantiated demand:
either a refusal message, or the list of enclosing caller callback parameters
(`callEnv` positions `1 + p`) onto which the demand must be forwarded. -/
def checkClosureAgainstDemand {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceElaboration.SourceRequest σ ι)
    (callerOrigins : Array (Option (List SlotOrigin)))
    (codeIdx : Nat) (capOrigins : List SlotOrigin)
    (instSupport : List (OriginRegion × Footprints.Change)) :
    Except String (List Nat) := do
  let G := RequestJson.graph r.toRequest
  let some q := r.codes[codeIdx]? | throw s!"callback closure code {codeIdx} not found"
  let qProg := GraphCode.program q.entry.exprs q.entry.conts
  -- Slot layout of a CodeEntry at q.entry.start: [receiver, param_0..param_{arity-1}, cap_0..cap_{k-1}]
  let taggedCaps := capOrigins.map fun o => match o with
    | .fresh a => .callerFresh a
    | other => other
  let initEnv : List SlotOrigin :=
    .unknown :: List.replicate q.entry.arity .unknown ++ taggedCaps
  let qOrigins := computeOrigins r.codes qProg q.entry.start initEnv
  -- A closure-local allocation is fresh inside the closure if `isFreshAllocExpr` holds
  let isClosureFresh (a : Nat) : Bool :=
    match qProg[a]? with
    | some n => isFreshAllocExpr n.expression
    | none => false
  -- A caller allocation is fresh & unaliased if `isFreshUnaliased` holds in the caller
  let isCallerFresh (a : Nat) : Bool := isFreshUnaliased r.program callerOrigins a
  let mut forwardedParams : List Nat := []
  for nl in List.range qProg.length do
    let some node := qProg[nl]? | continue
    let some env := qOrigins[nl]?.join | continue
    if isFreshAllocExpr node.expression then
      -- Fresh local allocation inside closure: preserves all pre-existing heap (`supportedAt_of_prefix`).
      continue
    match node.expression with
    | .writeAt k target _ =>
      let wReg := match target with
        | .var s => resolveOriginRegion env isClosureFresh isCallerFresh (.field s k)
        | _ => .all
      for (supReg, supCh) in instSupport do
        if !writeRespectsSupport wReg .any supReg supCh then
          throw s!"callback writes {originRegionText wReg} (any), violating demanded {originRegionText supReg} ({changeName supCh})"
    | .setElem arr _ _ =>
      let wReg := match arr with
        | .var s => resolveOriginRegion env isClosureFresh isCallerFresh (.cells s)
        | _ => .all
      for (supReg, supCh) in instSupport do
        if !writeRespectsSupport wReg .any supReg supCh then
          throw s!"callback writes {originRegionText wReg} (any), violating demanded {originRegionText supReg} ({changeName supCh})"
    | .invoke (.var fnSlot) _ _ =>
      match originAt env fnSlot with
      | .param callerParam =>
        -- Forwarding call to enclosing caller's own callback parameter!
        let pos := callerParam + 1
        if !forwardedParams.contains pos then
          forwardedParams := forwardedParams ++ [pos]
      | _ =>
        -- Known-effect call (e.g. `visited.push(i)`, `walked.push(w)`, `xs.pop()`, `prepared.widths.push(w)`)
        match q.claims[nl]?.bind fun c => preciseCallEffectAt G c node.expression with
        | some Φ =>
          for (wR, wCh) in Φ do
            let wOrig := resolveOriginRegion env isClosureFresh isCallerFresh wR
            for (supReg, supCh) in instSupport do
              if !writeRespectsSupport wOrig wCh supReg supCh then
                throw s!"callback call modifies {originRegionText wOrig} ({changeName wCh}), violating demanded {originRegionText supReg} ({changeName supCh})"
        | none =>
          throw s!"callback invokes function at node {nl} with unknown effect, violating demanded preservation"
    | .invoke .. | .construct .. =>
      throw s!"callback makes an unanalyzed call at node {nl}, violating demanded preservation"
    | e =>
      if !isReadOnlyOrAllocExpr e then
        throw s!"callback executes effectful term at node {nl}, violating demanded preservation"
  return forwardedParams

/-- Whether a term references any sibling in `demandedNames` (used to prevent
first-class escape of internal functions carrying callback demands). -/
def mentionsDemandedSibling (env : List SlotOrigin) (demandedNames : List String) : Tm → Bool
  | .var s => match originAt env s with | .sibling nm => demandedNames.contains nm | _ => false
  | .invoke f r args => mentionsDemandedSibling env demandedNames f ||
      mentionsDemandedSibling env demandedNames r || args.any (mentionsDemandedSibling env demandedNames)
  | .construct f args => mentionsDemandedSibling env demandedNames f ||
      args.any (mentionsDemandedSibling env demandedNames)
  | .letE a b => mentionsDemandedSibling env demandedNames a ||
      mentionsDemandedSibling (.unknown :: env) demandedNames b
  | .makeAt (.graph _ _ _ _ caps _ _ _) _ xs =>
      caps.any (mentionsDemandedSibling env demandedNames) || xs.any (mentionsDemandedSibling env demandedNames)
  | .makeAt _ _ xs | .arrLit xs => xs.any (mentionsDemandedSibling env demandedNames)
  | .readAt _ a | .test _ a | .lenOf a | .spread a | .throw a => mentionsDemandedSibling env demandedNames a
  | .indexAt a b | .writeAt _ a b | .arith _ a b | .elemAt a b | .merge _ a b | .makeKey a b =>
      mentionsDemandedSibling env demandedNames a || mentionsDemandedSibling env demandedNames b
  | .ite c a b | .setElem c a b =>
      mentionsDemandedSibling env demandedNames c || mentionsDemandedSibling env demandedNames a ||
      mentionsDemandedSibling env demandedNames b
  | _ => false

/-- **Caller demand discharge & forwarding**: checks every call in `r.program`
to any sibling in `calleeDemands`, and forbids first-class escape of any
demanded sibling outside direct calls. Returns either a refusal diagnostic or
any demands that `r` itself must publish by forwarding. -/
def checkCallerDemands {σ ι : Type} [Labels ι] [StoreView σ ι]
    (r : SourceElaboration.SourceRequest σ ι)
    (calleeDemands : List (String × List CallbackDemand)) :
    Except String (List CallbackDemand) := do
  let activeDemands := calleeDemands.filter fun (_, ds) => !ds.isEmpty
  if activeDemands.isEmpty then return []
  let demandedNames := activeDemands.map (·.1)
  let G := RequestJson.graph r.toRequest
  let origins := requestOrigins r
  let mut forwarded : List CallbackDemand := []
  for l in List.range r.program.length do
    let some node := r.program[l]? | continue
    let some env := origins[l]?.join | continue
    -- Ensure no demanded sibling escapes via return, storage, closure capture, or as an argument
    match node.continuation with
    | .ret =>
      if mentionsDemandedSibling env demandedNames node.expression then
        throw s!"function with callback demand escapes via return at node {l}"
    | _ => pure ()
    match node.expression with
    | .invoke (.var fnSlot) recv args =>
      if mentionsDemandedSibling env demandedNames recv || args.any (mentionsDemandedSibling env demandedNames) then
        throw s!"function with callback demand escapes as call operand at node {l}"
      match originAt env fnSlot with
      | .sibling calleeName =>
        match activeDemands.find? (·.1 == calleeName) with
        | none => pure ()
        | some (_, demands) =>
          let actualOrigins := args.map fun a => exprOrigin r.codes l env a
          for d in demands do
            if d.param == 0 then
              throw s!"callee '{calleeName}' has malformed receiver callback demand"
            let cbIdx := d.param - 1
            let some cbOrig := actualOrigins[cbIdx]?
              | throw s!"call to '{calleeName}' omits callback parameter {cbIdx} required by demand"
            -- Instantiate d.support at this call site's actual origins
            let mut instSupport : List (OriginRegion × Footprints.Change) := []
            for (reg, ch) in d.support do
              match instantiateDemandRegion actualOrigins reg with
              | some oReg => instSupport := instSupport ++ [(oReg, ch)]
              | none => throw s!"call to '{calleeName}' cannot instantiate demanded region {reprStr reg}"
            -- Discharge via closure literal or direct forwarding
            let fwdParams ← match cbOrig with
              | .closure ci capOrigins =>
                checkClosureAgainstDemand r origins ci capOrigins instSupport
              | .param pCaller =>
                pure [pCaller + 1]
              | _ =>
                throw s!"call to '{calleeName}' passes a callback whose effect cannot be verified against its preservation demand"
            -- Forward demand onto any invoked caller callback parameters
            for pPos in fwdParams do
              for (oReg, ch) in instSupport do
                match originRegionToCallerDemand oReg with
                | some callerReg =>
                  forwarded := addDemandEntry forwarded pPos (callerReg, ch)
                  for pe in prefixKeepEntries callerReg do
                    forwarded := addDemandEntry forwarded pPos pe
                | none =>
                  throw s!"call to '{calleeName}' cannot forward demand on non-parameter region {reprStr oReg} to caller callback parameter {pPos}"
      | _ => pure ()
    | e =>
      if mentionsDemandedSibling env demandedNames e then
        match e with
        | .var _ => pure ()
        | _ => throw s!"function with callback demand escapes at node {l}"
  -- Check that any forwarded path demands have their prefix fields preserved by `r`
  let allConfined := (List.range r.program.length).filter (isConfinedAlloc r.program origins)
  let calleeCallNodes := (List.range r.program.length).filter fun l =>
    match r.program[l]?, origins[l]?.join with
    | some node, some env => match node.expression with
      | .invoke (.var fnSlot) _ _ => match originAt env fnSlot with
        | .sibling nm => calleeDemands.any (·.1 == nm)
        | _ => false
      | _ => false
    | _, _ => false
  for d in forwarded do
    if !checkPrefixPreserved G r.program r.claims origins allConfined calleeCallNodes d.support then
      throw s!"forwarded callback demand on parameter {d.param} cannot guarantee prefix stability in caller"
  return forwarded

/-! ## Producer demand inference (discovering kept supports from `SinglePass`) -/

/-- Observe the supports of entry facts at each callback call node `l` in `r`,
filter to those cleanly projectable (locally confined or parameter-rooted),
and build a `CallbackDemandSpec`. Returns `none` if the function has no
direct callback call nodes or no projectable supports. -/
def FilePlans.inferCallbackDemandSpec (f : FilePlans) (fuel i : Nat) : Option CallbackDemandSpec := Id.run do
  let some (.ok (.graph _ _ r)) := f.plans[i]? | return none
  let origins := requestOrigins r
  let cbCalls := findCallbackCallNodes r origins
  if cbCalls.isEmpty then return none
  let confined := (List.range r.program.length).filter (isConfinedAlloc r.program origins)
  let mut framed : List (Nat × List Footprints.Footprint) := []
  let mut demands : List CallbackDemand := []
  -- Observe entry facts' supports at each callback call node (2 fixpoint rounds)
  for _ in cbCalls do
    let start := framed
    for (l, paramPos) in cbCalls do
      let others := framed.filter (·.1 != l)
      match f.passMember fuel i (observe := some s!"node:{l}") (framed := others) with
      | .ok run =>
        match (run.main.map (·.outcome)).getD run.outcome with
        | .observed o =>
          let some env := origins[l]?.join | continue
          let Ss := o.before.indices.filterMap fun a => a.fact.support? {}
          let mut kept : List Footprints.Footprint := []
          for S in Ss do
            let projs := S.map (projectEntry env confined)
            if projs.all (· != .unsupported) then
              if !kept.contains S then kept := kept ++ [S]
              for pe in projs do
                match pe with
                | .demand e =>
                  demands := addDemandEntry demands paramPos e
                  for pk in prefixKeepEntries e.1 do
                    demands := addDemandEntry demands paramPos pk
                | _ => pure ()
          framed := others ++ [(l, kept)]
        | _ => pure ()
      | .error _ => pure ()
    if framed == start then break
  let finalFramed := framed.filter fun (_, Ss) => !Ss.isEmpty
  if finalFramed.isEmpty then return none
  let spec : CallbackDemandSpec := ⟨finalFramed, cbCalls, confined, demands⟩
  if CallbackDemandSpec.checkProducer r spec then some spec else none

end Verification.SourceClaimJson
