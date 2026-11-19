import Verification.Paper.TolerantFrames.ReadOnlyCharges
import Verification.Paper.TolerantFrames.ReadOnlyClaim
import Verification.Semantics.ClosedFootprints
import Verification.Source.EffectCodec

/-! # A component's flow, as a framed plan reads it

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The plan" and "What the pass
checks"). The flow the solver proposes for a component's codes has
numbered sites, each released where the flow's `O` holds it and local
otherwise (`markedPackage`, `remark`). A framed plan reads it twice:

- **As the pass's check reads it**: the framed call nodes of a code
  (`framedCallNodes`), a call of node `l` framed where the call's callee
  set reaches outside code at some context; and the supports each keeps
  (`framedSupportsAt`), those passing `frameCheckAt` at the call's
  protocol $`\Psi_c = \Psi_C \sqcup \Theta_C \sqcup W_c`$ and the callee's
  effect, at every context and every node of the call's continuation and
  handler that may call outside code.
- **As the frame reads it**: the same flow over the sites of a numbered
  family with one component $`C`$ (`oneComponent`, each site of `C` with
  the mark the flow gives it), its sites renamed (`FFlow.mapSites`).

The client obligation $`\Theta_C`$ (`clientsProtocol`) is the join over
the component's exported types of each `@clients` row's change per kind,
read at its class entries. -/

namespace Verification.SourceClaimJson
open Lean Verification.TolerantFrames.ReadOnly ControlFlow Footprints

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

/-! ## Sites renamed -/

section
variable {P Q : TolerantFrames.ReadOnly.Package} (f : P.Site → Q.Site)

/-- A set of sites, each renamed by `f`. -/
def sitesMap (S : Sites P) : Sites Q := S.map (·.map f)

/-- A node of a finite proposal, its sites renamed. -/
def _root_.Verification.TolerantFrames.ReadOnly.FNode.mapSites (x : FNode P) : FNode Q :=
  ⟨x.env.map (sitesMap f), sitesMap f x.dflt, sitesMap f x.val, x.fn, x.vfn, x.cx, x.out⟩

/-- A code's finite proposal, its sites renamed. -/
def _root_.Verification.TolerantFrames.ReadOnly.FCode.mapSites (c : FCode P) : FCode Q :=
  ⟨c.nodes.map (FNode.mapSites f), c.dflt.mapSites f, ⟨c.alloc.obj.map f, c.alloc.arr.map f⟩, c.sigs,
    sitesMap f c.ret, c.tok.map f, c.allocs.map fun (k, o, a) => (k, o.map f, a.map f)⟩

/-- **A finite flow, its sites renamed** by `f`, the outside row read
through `g`, the renaming's inverse. -/
def _root_.Verification.TolerantFrames.ReadOnly.FFlow.mapSites (g : Q.Site → P.Site) (F : FFlow P) : FFlow Q :=
  ⟨sitesMap f F.O, F.heap.map (fun (s, S) => (s.map f, sitesMap f S)),
    F.codes.map (fun (m, cs) => (m, cs.map fun (k, c) => (k, c.mapSites f))), fun s => F.outsideRow (s.map g)⟩
end

/-! ## The family of one component -/

/-- **The numbered family of one component** `C`: nesting is equality,
every site's code is `C`'s, each site marked by `mark`. -/
def oneComponent (C : Nat) (mark : Nat → Mark) : NumberedFamily where
  nested a b := a = b
  refl _ := rfl
  trans _ _ _ h h' := h.trans h'
  laminar a b := if h : a = b then .inl h else .inr (.inr fun _ hc => h (hc.1.symm.trans hc.2))
  siteOf _ := some C
  mark s _ := mark s

/-- Every numbered site is a site of the component's code. -/
def oneComponent.site (C : Nat) (mark : Nat → Mark) (s : Nat) : ((oneComponent C mark).family.at C).Site :=
  ⟨s, ⟨C, rfl, rfl⟩⟩

/-! ## The client obligation -/

/-- **The client obligation of a component's `@clients` rows**, read at
their class entries (the draft, `clientsB`): at a part, the join of each
entry's change whose class may hold the part's contents: a field, cell or
element location's value; a spine location's array or view length; every
category at a part of no kind or an identity. -/
def clientsProtocol {P : TolerantFrames.ReadOnly.Package} (rows : List Footprint) : Protocol P := fun p =>
  let Φ := rows.flatten
  match p.kind with
  | some .field | some .cell | some .elem => Footprint.changeAt Φ .value
  | some .spine => (Footprint.changeAt Φ .array).max (Footprint.changeAt Φ .view)
  | _ => ((Footprint.changeAt Φ .value).max (Footprint.changeAt Φ .array)).max (Footprint.changeAt Φ .view)

/-- A `@clients` entry is a class entry: its region names locations by
their class alone. -/
def classEntry (e : Region × Change) : Bool :=
  match e.1 with
  | .cls _ | .all => true
  | _ => false

/-! ## The framed calls and the supports they keep -/

section
variable {P : TolerantFrames.ReadOnly.Package} [DecidableEq P.Site] [Hashable P.Site]

/-- The call sets of node `l` of code `m` at a context `c` of a flow. -/
def callsAtNode (F : FFlow P) (c : FCode P) (m : Code) (l : Nat) :
    List (Sites P × Sites P × List (Sites P)) :=
  match m.1[l]?, m.2[l]? with
  | some e, some kx => callSets F (flowSites F) (c.node l).envAt (fun i => c.sigAt ((c.node l).fnAt i))
      (c.flow.at l kx) (c.node l).cx 0 (fun _ => none) e
  | _, _ => []

/-- **A framed call** (`probeFrames`'s): a call of node `l` reaches outside
code at the context `c`. -/
def framedNodeAt (F : FFlow P) (host : Nat → Bool) (c : FCode P) (m : Code) (l : Nat) : Bool :=
  (callsAtNode F c m l).any fun (f, _, _) => reachesOut F (flowSites F) (segCodes F (flowSites F) host f) f

/-- **The framed call nodes of a code**: its call nodes framed at some
context of the code in the flow. -/
def framedCallNodes (F : FFlow P) (host : Nat → Bool) (m : Code) : List Nat :=
  (List.range m.1.length).filter fun l => (match m.1[l]? with | some (.invoke ..) => true | _ => false) &&
    (F.ctxs m).any fun (_, c) => framedNodeAt F host c m l

/-- **The supports a framed call keeps** (`probeFrames`'s check, decided):
of the supports `Ss` over node `l`'s slots, those passing `frameCheckAt` at
the call's protocol $`\Psi_c`$ (`componentProtocol` joined with the client
obligation `Θ` and the depth charges of the call's reach) and the callee's
effect `Φ`, at every context of code `m` and every node of the call's
continuation and handler that may call outside code or makes a framed call
(the node itself where none does). -/
def framedSupportsAt (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (host : Nat → Bool) (Θ : Protocol P)
    (m : Code) (l : Nat) (Φ : Footprint) (Ss : List Footprint) : List Footprint :=
  let top := flowSites F
  let kx := m.2[l]?
  let sharing := (List.range m.2.length).filter fun l' => m.2[l']? == kx
  Ss.filter fun S => (F.ctxs m).all fun (_, c) =>
    let required := sharing.filter fun l' => (c.node l').out || framedNodeAt F host c m l'
    let (Sf, Sr, args) := (callsAtNode F c m l).head?.getD ([], [], [])
    let seg := segCodes F top host Sf
    let L := callReach F lay seg Sf Sr args
    let Wc := depthCharges F seg L
    let Ψ : Protocol P := fun p => ((componentProtocol F lay p).max (Θ p)).max (Wc p)
    (if required.isEmpty then [l] else required).all fun l' =>
      frameCheckAt classQuery Ψ Φ S F.flow.H (c.node l').envAt noKeys (fun _ => false)

/-- **A flow holding a second code with the proposals of a first** at each
of its contexts: the request's code beside its realized code, whose nodes
below the request's length are the request's (`realizedFlowB`). -/
def _root_.Verification.TolerantFrames.ReadOnly.FFlow.withCode (F : FFlow P) (m₁ m₂ : Code) : FFlow P :=
  if (F.codes.any fun e => decide (e.1 = m₂)) then F else { F with codes := F.codes ++ [(m₂, F.ctxs m₁)] }
end

/-- **A framed plan's document** (the producer's inputs, the draft's
plan on the wire): the component, its entries, and each framed call node
with the supports its frame keeps. -/
def framedDocument (C : Nat) (entries : List String) (framed : List (Nat × List Footprints.Footprint)) : Json :=
  Json.mkObj [("component", toJson C), ("entries", toJson entries),
    ("framed", Json.arr (framed.map fun (l, Ss) => Json.mkObj [("node", toJson l),
      ("supports", Json.arr (Ss.map EffectCodec.frameJ).toArray)]).toArray)]

end Verification.SourceClaimJson
