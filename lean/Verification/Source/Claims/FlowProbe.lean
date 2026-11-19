import Verification.Source.Claims.Json
import Verification.Source.EffectCodec
import Verification.Semantics.Survival
import Verification.Paper.TolerantFrames.ReadOnlyFlowSolve
import Verification.Paper.TolerantFrames.ReadOnlyCallFrame

/-! # The flow of a unit's codes, probed

A diagnostic (`TSCERT_FLOW_PROBE`): for each member of a group, the flow the
read-only frame's checks read (`ReadOnly.SolveStart.propose`, the flow
`ReadOnly.solveFlow` proposes) of its component's codes and the closures
they create, and, at the marks the flow gives (`FFlow.MarksFrom`), whether
its checks hold (`ReadOnly.FFlow.check`, the nodes they refuse), each
entry's start (`FFlow.entryB`) and the marks' conditions (`FFlow.marksB`).
With `TSCERT_FRAME_PROBE` naming a
file of facts, at each call of outside code it names, the frame's check
(`frameCheckAt`) of each fact's support (`Footprints.linearSupport`), part
by part. It decides nothing a verdict reads. -/
namespace Verification.SourceClaimJson
open Lean Verification.TolerantFrames.ReadOnly ControlFlow

/-- The package a unit's probe reads: sites numbered, the code of the
component `C` the tags `ofC` names. -/
abbrev probePackage (ofC : ComponentTag → Bool) : TolerantFrames.ReadOnly.Package :=
  ⟨Nat, fun _ => .released, ofC⟩

/-- **The package at the marks a flow gives**: a site of `O` released, every
other site local (`FFlow.MarksFrom`). -/
abbrev markedPackage (ofC : ComponentTag → Bool) (O : List (Option Nat)) : TolerantFrames.ReadOnly.Package :=
  ⟨Nat, let sites := Std.HashSet.ofList O; fun s => if sites.contains (some s) then .released else .local, ofC⟩

/-- A code's finite proposal read at the marks a flow's `O` gives. -/
def remarkCode {ofC : ComponentTag → Bool} (F : FFlow (probePackage ofC)) (c : FCode (probePackage ofC)) :
    FCode (markedPackage ofC F.O) :=
  let node (x : FNode (probePackage ofC)) : FNode (markedPackage ofC F.O) := ⟨x.env, x.dflt, x.val, x.fn, x.vfn, x.cx, x.out⟩
  ⟨c.nodes.map node, node c.dflt, ⟨c.alloc.obj, c.alloc.arr⟩, c.sigs, c.ret, c.tok, c.allocs⟩

/-- A finite flow read at the marks its `O` gives. -/
def remark {ofC : ComponentTag → Bool} (F : FFlow (probePackage ofC)) : FFlow (markedPackage ofC F.O) :=
  ⟨F.O, F.heap, F.codes.map fun (m, cs) => (m, cs.map fun (k, c) => (k, remarkCode F c)), F.outsideRow⟩

theorem remark_marksFrom {ofC : ComponentTag → Bool} (F : FFlow (probePackage ofC)) : (remark F).MarksFrom := by
  intro s
  by_cases h : some s ∈ F.O <;> simp [markedPackage, remark, h]

/-! ## The frame at a call, probed -/

section frames
variable {P : TolerantFrames.ReadOnly.Package} [DecidableEq P.Site] [Hashable P.Site]

/-- **Every site a flow names**, and outside storage: `O`, the heap of
sites' rows, and each code's tokens, allocation sites, return sets and
node sets. The charges of a write whose receiver has no computed set are
at all of them. -/
def flowSites (F : FFlow P) : Sites P :=
  let fromCode (c : FCode P) : Sites P :=
    c.tok :: c.alloc.obj :: c.alloc.arr :: c.ret ++ c.allocs.flatMap (fun (_, o, a) => [o, a]) ++
      (c.dflt :: c.nodes.toList).flatMap fun x => x.val ++ x.dflt ++ x.env.toList.flatten
  (Std.HashSet.ofList (none :: F.O ++ F.heap.flatMap (fun (s, S) => s :: S) ++
    F.codes.flatMap fun (_, cs) => cs.flatMap fun (_, c) => fromCode c)).toList

mutual
/-- **The charged writes of a term at a node's slots** (`writesT`, the
draft "Framed acceptance", "Charges"): for each write, the sites of the
written location (its object's, or its spine's for an element write) and
the kinds it may have: a slot under a key, a field or a cell, or the array
spine under the spine key (`slotBound`); an element cell. A receiver with
no computed set, and a `letE` body under a bound term with none, are read
at `top`, every site of the flow. Structural over the term and its
argument lists. -/
def writesT (F : FFlow P) (top : Sites P) (τ : Nat → Sites P) (φ : Nat → Option FnSig) (a : FrameAt P) (κ : Nat)
    (d : Nat) (Γ : Nat → Option (Sites P)) : Tm → List (Sites P × List (Option Verification.Kind))
  | .writeAt k x y => [((syn F τ φ a κ d Γ x).getD top, roleKinds (Footprints.slotBound k))] ++
      writesT F top τ φ a κ d Γ x ++ writesT F top τ φ a κ d Γ y
  | .setElem x i v => [((syn F τ φ a κ d Γ x).getD top, [some .elem])] ++
      writesT F top τ φ a κ d Γ x ++ writesT F top τ φ a κ d Γ i ++ writesT F top τ φ a κ d Γ v
  | .letE x b => writesT F top τ φ a κ d Γ x ++
      writesT F top τ φ a κ (d + 1) (consSites ((syn F τ φ a κ d Γ x).getD top) Γ) b
  | .invoke f r args => writesT F top τ φ a κ d Γ f ++ writesT F top τ φ a κ d Γ r ++ writesTs F top τ φ a κ d Γ args
  | .construct f args => writesT F top τ φ a κ d Γ f ++ writesTs F top τ φ a κ d Γ args
  | .makeAt _ _ inits | .arrLit inits => writesTs F top τ φ a κ d Γ inits
  | .indexAt x y | .arith _ x y | .elemAt x y | .merge _ x y | .makeKey x y =>
    writesT F top τ φ a κ d Γ x ++ writesT F top τ φ a κ d Γ y
  | .ite x y z => writesT F top τ φ a κ d Γ x ++ writesT F top τ φ a κ d Γ y ++ writesT F top τ φ a κ d Γ z
  | .readAt _ x | .test _ x | .lenOf x | .spread x | .throw x => writesT F top τ φ a κ d Γ x
  | _ => []
/-- The charged writes of a list of terms. -/
def writesTs (F : FFlow P) (top : Sites P) (τ : Nat → Sites P) (φ : Nat → Option FnSig) (a : FrameAt P) (κ : Nat)
    (d : Nat) (Γ : Nat → Option (Sites P)) : List Tm → List (Sites P × List (Option Verification.Kind))
  | [] => []
  | x :: xs => writesT F top τ φ a κ d Γ x ++ writesTs F top τ φ a κ d Γ xs
end

/-- **The charges of one code** `Ch({m})`: the charged writes of each node
of the code at each of its contexts. -/
def codeWrites (F : FFlow P) (top : Sites P) (m : Code) (cs : List (Nat × FCode P)) :
    List (Sites P × List (Option Verification.Kind)) :=
  cs.flatMap fun (_, c) => (m.1.zip m.2).zipIdx.flatMap fun ((e, kx), l) =>
    writesT F top (c.node l).envAt (fun i => c.sigAt ((c.node l).fnAt i)) (c.flow.at l kx) (c.node l).cx 0 (fun _ => none) e

/-- The charges of every code of a flow, `Ch` of all codes of `C`. -/
def flowWrites (F : FFlow P) : List (Sites P × List (Option Verification.Kind)) :=
  let top := flowSites F
  F.codes.flatMap fun (m, cs) => codeWrites F top m cs

/-- **The sites a code's closures may capture**: the sites of each capture
slot at the code's entry at each of its contexts, its layout its arity, its
rest, its number of captures and its entry label. -/
def codeCaptureSites (cs : List (Nat × FCode P)) (lay : Nat × Bool × Nat × Nat) : Sites P :=
  let (ar, rest, n, s) := lay
  cs.flatMap fun (_, c) => (List.range n).flatMap fun i => (c.node s).envAt (capSlot ar rest i)

/-- **The sites a closure of the flow's codes may capture**: the union of
each code's `codeCaptureSites`. -/
def captureSites (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) : Sites P :=
  (F.codes.zip lay).flatMap fun ((_, cs), l) => codeCaptureSites cs l

/-- **The closure of sites** $`\overline{S}`$ (`capClose`, the draft's
"Definitions"): the least superset of `S` closed under the heap of sites'
contents and under captures (for each code token in it, the sites of that
code's capture slots at every context, `caps`). Iterated to its fixpoint:
each round adds sites of `flowSites F ∪ S ∪ caps`, so it stops within
their number of rounds. -/
def capClose (F : FFlow P) (caps : Option P.Site → Sites P) (S : Sites P) : Sites P :=
  let step (S : Std.HashSet (Option P.Site)) : Std.HashSet (Option P.Site) :=
    S.toList.foldl (fun acc s => (F.contents s ++ caps s).foldl (·.insert ·) acc) S
  let rec go : Nat → Std.HashSet (Option P.Site) → Std.HashSet (Option P.Site)
    | 0, S => S
    | n + 1, S => let S' := step S; if S'.size == S.size then S else go n S'
  (go ((flowSites F).length + S.length + 1) (Std.HashSet.ofList S)).toList

/-- **The calls of a term** at a node's slots: for each `invoke` and
`construct`, the callee's set, the receiver's and the arguments', each
`top` where it has no computed set. -/
partial def callSets (F : FFlow P) (top : Sites P) (τ : Nat → Sites P) (φ : Nat → Option FnSig) (a : FrameAt P)
    (κ : Nat) (d : Nat) (Γ : Nat → Option (Sites P)) : Tm → List (Sites P × Sites P × List (Sites P))
  | .invoke f r args =>
    let set (x : Tm) := (syn F τ φ a κ d Γ x).getD top
    (set f, set r, args.map set) :: callSets F top τ φ a κ d Γ f ++ callSets F top τ φ a κ d Γ r ++
      args.flatMap (callSets F top τ φ a κ d Γ)
  | .construct f args =>
    let set (x : Tm) := (syn F τ φ a κ d Γ x).getD top
    (set f, [], args.map set) :: callSets F top τ φ a κ d Γ f ++ args.flatMap (callSets F top τ φ a κ d Γ)
  | .letE x b => callSets F top τ φ a κ d Γ x ++
      callSets F top τ φ a κ (d + 1) (consSites ((syn F τ φ a κ d Γ x).getD top) Γ) b
  | .makeAt _ _ inits | .arrLit inits => inits.flatMap (callSets F top τ φ a κ d Γ)
  | .indexAt x y | .writeAt _ x y | .arith _ x y | .elemAt x y | .merge _ x y | .makeKey x y =>
    callSets F top τ φ a κ d Γ x ++ callSets F top τ φ a κ d Γ y
  | .ite x y z | .setElem x y z =>
    callSets F top τ φ a κ d Γ x ++ callSets F top τ φ a κ d Γ y ++ callSets F top τ φ a κ d Γ z
  | .readAt _ x | .test _ x | .lenOf x | .spread x | .throw x => callSets F top τ φ a κ d Γ x
  | _ => []

/-- The calls of every node of a code at each of its contexts. -/
def codeCalls (F : FFlow P) (top : Sites P) (m : Code) (cs : List (Nat × FCode P)) :
    List (Sites P × Sites P × List (Sites P)) :=
  cs.flatMap fun (_, c) => (m.1.zip m.2).zipIdx.flatMap fun ((e, kx), l) =>
    callSets F top (c.node l).envAt (fun i => c.sigAt ((c.node l).fnAt i)) (c.flow.at l kx) (c.node l).cx 0 (fun _ => none) e

/-- **The segment's codes** $`\mathrm{seg}(c)`$ of a call whose callee's set
is `Sf` (`segCodes`, the draft's "Definitions"): the least set of the
flow's codes (by index) holding each code whose token `Sf` holds, closed
under the same at every call of its members, and under the tokens of the
arguments of each call of a native step model (`host`) its members make. -/
def segCodes (F : FFlow P) (top : Sites P) (host : Nat → Bool) (Sf : Sites P) : List Nat :=
  let toks : List (Nat × Sites P) := F.codes.zipIdx.map fun ((_, cs), i) => (i, cs.map (·.2.tok))
  let holding (S : Sites P) : List Nat := toks.filterMap fun (i, ts) => if ts.any (S.contains ·) then some i else none
  let calls : Array (List (Sites P × Sites P × List (Sites P))) :=
    (F.codes.map fun (m, cs) => codeCalls F top m cs).toArray
  let rec go : Nat → List Nat → List Nat → List Nat
    | 0, seen, _ => seen
    | _ + 1, seen, [] => seen
    | n + 1, seen, i :: work =>
      if seen.contains i then go n seen work else
      let next := (calls.getD i []).flatMap fun (f, _, args) =>
        holding f ++ (if (holding f).any host then args.flatMap holding else [])
      go n (i :: seen) (next ++ work)
  let n := F.codes.length
  go (n * n + n + 1) [] (holding Sf)

/-- **Whether a call reaches outside code** (`reachesOut`): its callee's set
holds outside storage, or a call of a code of its segment has a callee
whose set does. -/
def reachesOut (F : FFlow P) (top : Sites P) (seg : List Nat) (Sf : Sites P) : Bool :=
  Sf.contains none || seg.any fun i => match F.codes[i]? with
    | some (m, cs) => (codeCalls F top m cs).any fun (f, _, _) => f.contains none
    | none => false

structure ProtocolIndex (P : TolerantFrames.ReadOnly.Package) [DecidableEq P.Site] [Hashable P.Site] where
  captures : Std.HashSet (Option P.Site)
  writes : Std.HashMap (Option P.Site) (List (Option Verification.Kind))

/-- Index each write's kinds by the sites its receiver may reach. -/
def ProtocolIndex.ofWrites (W : List (Sites P × List (Option Verification.Kind))) (held : Sites P) : ProtocolIndex P :=
  ⟨Std.HashSet.ofList held, W.foldl (fun m (sites, ks) =>
    sites.foldl (fun m s => m.insert s ((ks ++ m.getD s []).eraseDups)) m) {}⟩

/-- **A protocol from charges**: a part changed by any change where a
charged write `W` may reach it, at its site and kind; kept where none may,
and kept at a local site outside `held`. -/
def ProtocolIndex.query (idx : ProtocolIndex P) : Protocol P := fun p =>
  if p.site.any (fun s => P.mark s = .local) && !idx.captures.contains p.site then .keep
  else if (idx.writes.getD p.site []).contains p.kind then .any else .keep

def probeProtocol (W : List (Sites P × List (Option Verification.Kind))) (held : Sites P) : Protocol P :=
  (ProtocolIndex.ofWrites W held).query

/-- The capture sites of the codes whose closures a token stands for. -/
def tokenCaps (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (t : Option P.Site) : Sites P :=
  if t.isNone then [] else
  (F.codes.zip lay).flatMap fun ((_, cs), l) => if cs.any (·.2.tok == t) then codeCaptureSites cs l else []

/-- **The protocol** $`\Psi_C`$ (the draft's "Charges"): `Ch` of every code
of `C` at every part but a local part whose site is outside the closure of
the capture sites and `O`, which is kept. -/
def componentProtocol (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) : Protocol P :=
  probeProtocol (flowWrites F) (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O))

/-- **The reach of a call** $`L(c)`$: the closure of its callee's,
receiver's and arguments' sets and the capture sites of its segment's
codes. -/
def callReach (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (seg : List Nat) (Sf Sr : Sites P)
    (args : List (Sites P)) : Sites P :=
  capClose F (tokenCaps F lay) (Sf ++ Sr ++ args.flatten ++ seg.flatMap fun i =>
    match (F.codes.zip lay)[i]? with
    | some ((_, cs), l) => codeCaptureSites cs l
    | none => [])

/-- **The depth charges** $`W_c`$ of a call: `Ch(seg(c))` at every part but
a local part whose site is outside $`L(c)`$, which is kept. -/
def depthCharges (F : FFlow P) (seg : List Nat) (L : Sites P) : Protocol P :=
  let top := flowSites F
  probeProtocol (seg.flatMap fun i => match F.codes[i]? with
    | some (m, cs) => codeWrites F top m cs
    | none => []) L

end frames

def markName {ofC : ComponentTag → Bool} {O : List (Option Nat)} (s : Option Nat) : String :=
  match s with
  | none => "outside"
  | some n => match (markedPackage ofC O).mark n with
    | .local => s!"{n} local" | .released => s!"{n} released" | .internal => s!"{n} internal"
    | .exposed => s!"{n} exposed"

/-- A fact of the frame probe: a linear fact over source variables. -/
structure FrameFact where
  name : String
  terms : List (String × List String × HeapKnowledge.Term.Kind × Int)
  bound : Int
  ne : Bool

/-- The frame probe's request for a member: the source offset of the calls
it reads (the start of the call's node), the call's effect, the facts. -/
structure FrameSpec where
  unit : String
  at_ : Nat
  effect : Footprints.Footprint
  facts : List FrameFact
  /-- Also evaluate the predicate at the named call when no outside-call
  obligation arises there. -/
  inspect : Bool := false

def frameSpecs (j : Json) : Except String (List FrameSpec) := do
  let arr ← j.getArr?
  arr.toList.mapM fun u => do
    let facts ← (← u.getObjVal? "facts").getArr?
    let facts ← facts.toList.mapM fun f => do
      let terms ← (← f.getObjVal? "terms").getArr?
      let terms ← terms.toList.mapM fun t => do
        let path ← (← t.getObjVal? "path").getArr?
        pure (← t.getObjValAs? String "var", ← path.toList.mapM (·.getStr?),
          ← EffectCodec.kindOf (← t.getObjVal? "kind"), ← t.getObjValAs? Int "coeff")
      pure ⟨← f.getObjValAs? String "name", terms, ← f.getObjValAs? Int "bound",
        (f.getObjValAs? Bool "ne").toOption.getD false⟩
    pure ⟨← u.getObjValAs? String "unit", ← u.getObjValAs? Nat "at",
      ← EffectCodec.frameOf 64 (← u.getObjVal? "effect"), facts, (u.getObjValAs? Bool "inspect").toOption.getD false⟩

/-- **The frame's check at each call the spec names**, in the code `c` of a
flow, of graph `m` and source map `sm` (`frameCheckAt`, at the class
query, the probe's protocol and the keys `noKeys`, no region read as
protected): per call node, per fact, its result, and each part its
support's regions may have that fails, with the check it fails. The check
is required at each node of the call node's continuation and handler (a
frame of that node runs at one of them, `NodeOf`) where the node may call
outside code (`CodeFlow.out`, `ClientFrame.framed_at_call`), read at that
node's slots; elsewhere it is not required. -/
def probeFrames {ofC : ComponentTag → Bool} (O : List (Option Nat)) (F : FFlow (markedPackage ofC O))
    (ΨC : Protocol (markedPackage ofC O)) (lay : List (Nat × Bool × Nat × Nat)) (host : Nat → Bool)
    (c : FCode (markedPackage ofC O)) (m : Code)
    (sm : RequestJson.SourceMap) (sp : FrameSpec) : List String :=
  let top := flowSites F
  -- the calls of a node: its callee's, receiver's and arguments' sets
  let callsAt (l : Nat) : List (Sites (markedPackage ofC O) × Sites (markedPackage ofC O) × List (Sites (markedPackage ofC O))) :=
    match m.1[l]?, m.2[l]? with
    | some e, some kx => callSets F top (c.node l).envAt (fun i => c.sigAt ((c.node l).fnAt i)) (c.flow.at l kx)
        (c.node l).cx 0 (fun _ => none) e
    | _, _ => []
  -- a framed call: a call of the node reaches outside code
  let framedAt (l : Nat) : Bool := (callsAt l).any fun (f, _, _) => reachesOut F top (segCodes F top host f) f
  let names (l : Nat) : List String := ((sm[l]?).bind id).map (·.context.map (·.name)) |>.getD []
  let calls := m.1.zipIdx.filterMap fun (e, l) => match e with
    | .invoke (.var j) _ _ => if ((c.node l).fnAt j).isNone then some (l, j) else none
    | _ => none
  let pos (l : Nat) : String := match (sm[l]?).bind id with
    | some en => s!"{en.pos}"
    | none => "none"
  s!"frame probe, {sp.unit}: calls of a slot naming no signature (node, callee slot, source span) {calls.map fun (l, j) => (l, j, pos l)}" ::
  m.1.zipIdx.flatMap fun (e, l₀) => match e with
    | .invoke _ _ _ =>
      let pos := ((sm[l₀]?).bind id).map (·.pos.1)
      if pos != some sp.at_ then [] else
      -- the nodes a frame of this node's continuation and handler may run at
      let kx := m.2[l₀]?
      let sharing := (List.range m.2.length).filter fun l => m.2[l]? == kx
      let required := sharing.filter fun l => (c.node l).out || framedAt l
      let slotOf (x : String) : Option Nat := (names l₀).idxOf? x
      -- the call's protocol Ψ_c = Ψ_C ⊔ Θ_C ⊔ W_c, at Θ_C = keep (no `@clients` row)
      let (Sf, Sr, args) := (callsAt l₀).head?.getD ([], [], [])
      let seg := segCodes F top host Sf
      let L := callReach F lay seg Sf Sr args
      let Wc := depthCharges F seg L
      let Ψ : Protocol (markedPackage ofC O) := fun p => Footprints.Change.max (ΨC p) (Wc p)
      s!"frame probe, {sp.unit}, at node {l₀} (nodes of its continuation and handler {sharing}, which may call outside code or make a framed call {required}; framed {framedAt l₀}; seg {seg}; L(c) {(L.map (markName (ofC := ofC) (O := O)))})" ::
      if required.isEmpty && !sp.inspect then
        sp.facts.map fun ff => s!"  {ff.name}: not required, no node of the call's continuation and handler may call outside code here"
      else (if required.isEmpty then [l₀] else required).flatMap fun l =>
      let τ := (c.node l).envAt
      let slotSites := (List.range (names l₀).length).map fun i => ((names l₀)[i]?.getD "", τ i)
      (if required.isEmpty then s!"frame probe, {sp.unit}, inspected at node {l}"
       else s!"frame probe, {sp.unit}, read at node {l}: slots {repr slotSites}") ::
      sp.facts.map fun ff =>
        match ff.terms.mapM (fun (x, p, k, a) => (slotOf x).map fun i => (HeapKnowledge.Term.now k i p, a)) with
        | none => s!"  {ff.name}: a variable is not a slot here"
        | some G =>
          let fact : Linear.Fact HeapKnowledge.Term := if ff.ne then .ne G ff.bound else .le G ff.bound
          let S := Footprints.linearSupport {} fact
          let ok := frameCheckAt classQuery Ψ sp.effect S F.flow.H τ noKeys (fun _ => false)
          let per := S.map fun (r, δ) =>
            match regionSites F.flow.H τ r with
            | none => s!"{repr r} at {repr δ}: no sites"
            | some T =>
              let parts := callParts F.flow.H τ noKeys r
              let reasons (p : Part (markedPackage ofC O)) :=
                (p.mayIn && !(Ψ p).le δ,
                  p.mayOut false && sp.effect.any fun f => !(f.2.le δ) && !classQuery.disjoint r f.1)
              let describe (p : Part (markedPackage ofC O)) :=
                let (inside, outside) := reasons p
                s!"part ({markName (ofC := ofC) (O := O) p.site}, {repr p.kind}) fails {if inside then s!"Ψ = {repr (Ψ p)}" else ""}{if outside then " the call's effect" else ""}"
              if required.isEmpty then
                let witnesses := [(true, false), (false, true), (true, true)].filterMap fun pair =>
                  (parts.find? (fun p => reasons p == pair)).map describe
                s!"{repr r} at {repr δ}: {(Std.HashSet.ofList T).size} sites{if witnesses.isEmpty then ", passes" else s!", {witnesses}"}"
              else
                let bad := parts.filterMap fun p => if reasons p == (false, false) then none else some (describe p)
                s!"{repr r} at {repr δ}: sites {T.map (markName (ofC := ofC) (O := O))}{if bad.isEmpty then ", passes" else s!", {bad}"}"
          let obligation := if required.isEmpty then "not required; diagnostic " else ""
          s!"  {ff.name}: {obligation}frameCheckAt {ok}; support {per}"
    | _ => []

/-- **A module function's closure code** (`PassUnit.dropReceiver`): the
request's node lists behind one prologue node, appended, evaluating
`undefined` and continuing at the request's start with the frame past the
receiver; its arity, the module values it names (its captures) and its
component. A function declaring `this` or collecting a rest parameter has
none here. -/
structure ProbeModule where
  name : String
  code : Code
  ar : Nat
  siblings : List String
  comp : ComponentTag
  sm : RequestJson.SourceMap := []

def ProbeModule.ofRequest {σ ι : Type} [LabelStore.Labels ι] [LabelStore.StoreView σ ι] (name : String)
    (r : SourceExtraction.SourceRequest σ ι) : Option ProbeModule :=
  if r.receiver || r.restParam then none else
  let ar := r.inputs.length - r.siblings.length
  let ncaps := r.siblings.length
  let exprs := r.program.map (·.expression)
  let conts := r.program.map fun n => (n.continuation, n.handler)
  some ⟨name, (exprs ++ [.undef], conts ++ [(.effect ⟨r.start, some ((List.range (ar + ncaps + 1)).map (· + 1))⟩, none)]),
    ar, r.siblings, r.comp, r.sourceMap⟩

/-- The signature of a module function's closure. -/
def ProbeModule.sig (g : ProbeModule) : FnSig := ⟨g.code, g.ar, g.code.1.length - 1, false, g.siblings.length⟩

/-- **A native's step model** (the contract of an audited native, as code
of the component): the graph whose run the native's call performs, with its
arity. The rule `Read-only frame` reads an audited native at its audited
effect, not as code that is not `C`'s; its call is then a call of a
closure of a known signature (`Fits.invokeC`), its actuals at its entry's
slots, its value at its return set. Each row is trusted input, audited
against the native's definition:

- `%ElementAt%(xs, k)`: the element of `xs`'s spine at `k`, `undefined`
  where none (`tools/intrinsics.mts`: on an array of the program the read
  runs no code; no accessor or proxy, DESIGN.md "Trust surface"). Of an
  array or a tuple only: the model reads the spine field. -/
def hostModel? (name : String) : Option (Code × Nat) :=
  if name == "%ElementAt%" then
    some (([.elemAt (.readAt arraySpineKey (.var 1)) (.var 2)], [(.ret, none)]), 2)
  else none

/-- The module functions whose closures are values: those on no cycle of
the module's names (a cycle's closures capture each other). -/
def closable (mods : List ProbeModule) : List ProbeModule :=
  mods.filter fun g =>
    let rec reach : Nat → List String → List String → List String
      | 0, seen, _ => seen
      | _ + 1, seen, [] => seen
      | n + 1, seen, x :: work =>
        if seen.contains x then reach n seen work
        else reach n (x :: seen) (((mods.find? (·.name == x)).map (·.siblings)).getD [] ++ work)
    !(reach (mods.length * mods.length + mods.length + 1) [] g.siblings).contains g.name

/-- **The probe of a member at a component**, timed: the solver's, the
merge's and the check's milliseconds. The component `C` is a set of modules
(the tags `ofC` names) entered through its entries `E` (`entry`, by the
module functions' names); every module function of `C`'s modules a probe
reaches is a code of the flow, and the closures of `C`'s code they create.
An entry's closure is held by outside code (its token in `O`): outside
code may call it, at any time, with what it holds (`OpenAt`), and each
execution starts at a call of one (`EntryShape`, decided by `FFlow.entryB`
at the entry's first node). A module function no entry names is entered
only by `C`'s code that names it. The member is the module function
`member`, read at its closure's code. -/
def probeProgram (ofC : ComponentTag → Bool) (member : String) (mods : List ProbeModule)
    (specs : List FrameSpec := []) (entryNames : List String := []) : IO String := do
  let P := probePackage ofC
  let mods := mods.filter fun g => P.ofC g.comp
  let closed := closable mods
  let found := mods.flatMap fun g => g.code.1.flatMap (closureLayouts P.ofC)
  let closures := found.foldl (fun acc c => if acc.any (·.1 == c.1) then acc else acc ++ [c]) []
  let alloc : Nat → Alloc P := fun i => ⟨some (3 * i), some (3 * i + 1)⟩
  let tok (i : Nat) : Option P.Site := some (3 * i + 2)
  -- the natives with a step model the module functions name
  let hostNames := (mods.flatMap (·.siblings)).filter (fun x => (hostModel? x).isSome) |>.eraseDups
  let hosts : List (String × Code × Nat) := hostNames.filterMap fun x => (hostModel? x).map fun (c, ar) => (x, c, ar)
  let hostSig (x : String) : Option FnSig :=
    (hosts.find? (·.1 == x)).map fun (_, c, ar) => ⟨c, ar, 0, false, 0⟩
  let sibSig (x : String) : Option FnSig :=
    ((closed.find? (·.name == x)).map ProbeModule.sig).orElse fun _ => hostSig x
  let modCodes : List (SolveCode P) := mods.zipIdx.map fun (g, i) =>
    let c0 := capSlot g.ar false 0
    let seeds := (List.range (c0 + g.siblings.length)).map fun j =>
      if c0 ≤ j then (g.siblings[j - c0]?).bind sibSig else none
    ⟨g.code, g.ar, false, g.siblings.length, g.code.1.length - 1, seeds, alloc i, true, tok i, entryCx,
      fun _ => alloc i, entryNames.contains g.name⟩
  let hostCodes : List (SolveCode P) := hosts.zipIdx.map fun ((_, c, ar), i) =>
    ⟨c, ar, false, 0, 0, [], alloc (i + mods.length), true, tok (i + mods.length), entryCx,
      fun _ => alloc (i + mods.length), false⟩
  let base' := mods.length + hosts.length
  let cs : List (SolveCode P) := modCodes ++ hostCodes ++ closures.zipIdx.map fun ((c, ar, rest, n, s), i) =>
    ⟨c, ar, rest, n, s, [], alloc (i + base'), true, tok (i + base'), entryCx, fun _ => alloc (i + base'), false⟩
  -- each node's allocation sites: one object site and one array site per
  -- continuation and handler of a code, numbered past the codes' sites
  let offs := (cs.map fun c => c.code.2.length).foldl (fun (acc : List Nat) n => acc ++ [acc.getLast?.getD 0 + n]) [0]
  let cs : List (SolveCode P) := cs.zipIdx.map fun (c, i) =>
    -- (each continuation and handler's first node, read once per code)
    let first : Std.HashMap NodeKey Nat := c.code.2.zipIdx.foldl
      (fun m (kx, l) => if m.contains kx then m else m.insert kx l) {}
    { c with allocAt := fun kx => match first[kx]? with
      | some l => let k := 3 * cs.length + 2 * (offs.getD i 0 + l); ⟨some k, some (k + 1)⟩
      | none => c.alloc }
  let entries := (mods.zip modCodes).filter fun (g, _) => entryNames.contains g.name
  let t0 ← IO.monoNanosNow
  let s : SolveStart P ← IO.lazyPure fun _ => solveStart cs
  let _ ← IO.lazyPure fun _ => (s.fns.map fun ns => (ns.map fun x => x.size).sum).sum + s.succ.size
  let ts ← IO.monoNanosNow
  IO.eprintln s!"flow probe, start: {s.cs.size} copies of {cs.length} codes, {(s.codes.toList.map (·.1.size)).sum} nodes over the copies, {s.st.classes.size} slot and value occurrences, {s.succ.size} variables, {(ts - t0) / 1000000} ms"
  let fuel := ((← IO.getEnv "TSCERT_PROBE_FUEL").bind String.toNat?).getD 10000000
  let (st, rounds, batches) ← IO.lazyPure fun _ => solveLoop s fuel s.st
  let _ ← IO.lazyPure fun _ => st.sites.size + st.stores.size + st.vars.size
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"flow probe, solve: {(t1 - ts) / 1000000} ms, {rounds} copies, {batches} node evaluations"
  let F ← IO.lazyPure fun _ => s.propose st
  let _ ← IO.lazyPure fun _ => F.O.length + F.heap.length + (F.codes.map fun c => (c.2.map (·.2.nodes.size)).sum).sum
  let t2 ← IO.monoNanosNow
  -- (the checks at the marks the flow gives: a bound function's and a
  -- closure of outside code's parts reach no local site, which the marks
  -- decide)
  IO.eprintln s!"flow probe, merge: {(t2 - t1) / 1000000} ms"
  let marked := remark F
  let ok ← IO.lazyPure fun _ => marked.check
  let t3 ← IO.monoNanosNow
  IO.eprintln s!"flow probe, check: {ok} {(t3 - t2) / 1000000} ms"
  let nodes := (cs.map fun c => c.code.1.length).sum
  let names := mods.map (·.name) ++ hosts.map (·.1) ++ closures.map fun _ => "closure"
  let named : List (String × Code × RequestJson.SourceMap) := mods.map fun g => (g.name, g.code, g.sm)
  -- the call site a context stands for (the first of its class): its caller and the caller's source span
  let siteOf (κ : Nat) : String :=
    if κ == entryCx then " (entry)" else
    match (s.nodeCx.toList.zipIdx.flatMap fun (row, b) =>
        row.toList.zipIdx.filterMap fun (k, l) => if k == κ then some (b, l) else none).head? with
    | some (b, l) =>
      let pos := match (named[b]?).bind fun (_, _, msm) => (msm[l]?).bind id with
        | some en => s!"{en.pos}"
        | none => "none"
      s!" (call site: {names.getD b "?"} node {l} at {pos})"
    | none => ""
  let report (tag : String) : String :=
    -- each entry's start: its first node, the closure's prologue
    let entryOk := entryNames.map fun name =>
      (name, (entries.find? fun (g, _) => g.name == name).any fun (g, c) => F.entryB g.code c.start)
    let F' := marked
    let marks := F'.marksB
    -- (the refused nodes are read again only where the check fails)
    let bad := if ok then [] else F.codes.zipIdx.flatMap fun ((code, cs), ci) => cs.flatMap fun (κ, c) =>
      (code.1.zip code.2).zipIdx.filterMap fun ((e, k, x), l) =>
        if nodeAtB F' (remarkCode F c) l e k x then none else some s!"{ci}@{κ}:{l}"
    let contexts := (F.codes.map (·.2.length)).sum
    let ctxNodes := (F.codes.map fun (m, cs) => m.1.length * cs.length).sum
    let lay := cs.map fun c => (c.ar, c.rest, c.ncaps, c.start)
    let held := (Std.HashSet.ofList (captureSites F' lay)).toList
    let host (i : Nat) : Bool := mods.length ≤ i && i < mods.length + hosts.length
    let frames := String.join <| specs.flatMap fun sp => match named.zipIdx.find? (·.1.1 == sp.unit) with
      | some ((_, mc, msm), ci) => match (F'.codes[ci]?).map (·.2) with
        | some cxs => cxs.flatMap fun (κ, c) =>
          s!"\nframe probe, {sp.unit}: {tag} context {κ}{siteOf κ}" :: (probeFrames F.O F' (componentProtocol F' lay) lay host c mc msm sp).map ("\n" ++ ·)
        | none => []
      | none => []
    s!"{tag}: {contexts} contexts, {ctxNodes} nodes over the contexts; entry {entryOk.all (·.2)}; entries {entryOk}; at the marks O gives: marks {marks}; refused nodes {bad}; captured {repr held}{frames}"
  let present := if mods.any (·.name == member) then "" else s!" (the member {member} has no closure code here)"
  return s!"flow probe: {cs.length} codes {names}, {nodes} nodes{present}; siblings {mods.map fun g => (g.name, g.siblings)}; solve {(t1 - t0) / 1000000} ms (signatures {(ts - t0) / 1000000} ms, {rounds} copies, {batches} nodes run); merge {(t2 - t1) / 1000000} ms; check {ok} {(t3 - t2) / 1000000} ms; O {repr F.O} (code i's closures 3i+2; a node's object site 3n+2k, array site 3n+2k+1, n codes, k the first node of its continuation and handler over all codes)\n{report "proposed"}"

/-- The probe of each member of a group, the component's module functions'
codes `mods`, its tags `ofC` and its entries `entry`. -/
def FilePlans.flowProbe (f : FilePlans) (group : List Nat) (mods : List ProbeModule)
    (ofC : ComponentTag → Bool) (entryNames : List String) : IO (List String) := do
  let specs ← match ← IO.getEnv "TSCERT_FRAME_PROBE" with
    | some path => do
      match Json.parse (← IO.FS.readFile path) >>= frameSpecs with
      | .ok sp => pure sp
      | .error e => IO.eprintln s!"frame probe: {e}"; pure []
    | none => pure []
  group.filterMapM fun j => match (f.plans.drop j).head? with
    | some (.ok p) => match p with
      | .graph name _ _ => do
        let line ← probeProgram ofC name mods specs entryNames
        return some s!"{name}: {line}"
    | _ => return none

/-- The module codes of a file's planned members. -/
def FilePlans.moduleCodes (f : FilePlans) (units : List Nat) : List ProbeModule :=
  units.filterMap fun j => match (f.plans.drop j).head? with
    | some (.ok (.graph name _ r)) => if name.isEmpty then none else ProbeModule.ofRequest name r
    | _ => none

/-- The siblings of a file's planned members. -/
def FilePlans.siblingsOf (f : FilePlans) (units : List Nat) : List String :=
  units.flatMap fun j => match (f.plans.drop j).head? with
    | some (.ok (.graph _ _ r)) => r.siblings
    | _ => []

/-- The module codes of the groups planned so far in this process, where
the probe is on. -/
initialize probeModulesSeen : IO.Ref (List ProbeModule) ← IO.mkRef []

/-- Keep a planned group's module codes for the probe. -/
def FilePlans.keepModuleCodes (f : FilePlans) (units : List Nat) : IO Unit := do
  let found := f.moduleCodes units
  probeModulesSeen.modify fun seen => seen ++ found.filter fun m => !seen.any (·.name == m.name)

end Verification.SourceClaimJson
