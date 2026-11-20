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

The wire states the client obligation $`\Theta_C`$ by kind
(`protocolOfKinds`) and the component's protocol $`\Psi_C`$ by numbered
site and kind (`protocolOfParts`). -/

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

/-! ## Protocols on the wire -/

/-- A kind of location on the wire: its name, `null` for none. -/
def kindNameJ : Option Verification.Kind → Json
  | none => .null
  | some .field => "field" | some .cell => "cell" | some .elem => "elem" | some .spine => "spine"
  | some .identity => "identity"

def kindNameOf (j : Json) : Except String (Option Verification.Kind) := do
  match j with
  | .null => pure none
  | .str "field" => pure (some .field) | .str "cell" => pure (some .cell) | .str "elem" => pure (some .elem)
  | .str "spine" => pure (some .spine) | .str "identity" => pure (some .identity)
  | _ => throw s!"{j.compress} is no kind of location"

/-- **A protocol by kind**, as the wire states one: the change each listed
kind has, `keep` at a kind it does not list. -/
def protocolOfKinds {P : TolerantFrames.ReadOnly.Package} (tab : List (Option Verification.Kind × Change)) :
    Protocol P := fun p =>
  ((tab.find? fun e => decide (e.1 = p.kind)).map (·.2)).getD .keep

/-- A kind of location's number, as an index's key reads it. -/
def kindCode : Option Verification.Kind → Nat
  | none => 0 | some .field => 1 | some .cell => 2 | some .elem => 3 | some .spine => 4
  | some .identity => 5

/-- **A protocol by numbered site, kind and key, indexed**: each listed
part's change (the first listing of a part), by the part's site number,
kind and key. -/
def partsIndex (tab : List (Option Nat × Option Verification.Kind × Option PropKey × Change)) :
    Std.HashMap (Option Nat × Nat × Option PropKey) Change :=
  tab.foldl (fun m (s, k, key, c) => if m.contains (s, kindCode k, key) then m else m.insert (s, kindCode k, key) c) {}

/-- The keys a protocol by parts lists, and `none`. -/
def partsKeys (tab : List (Option Nat × Option Verification.Kind × Option PropKey × Change)) : List (Option PropKey) :=
  (none :: tab.map (·.2.2.1)).eraseDups

/-- **A protocol by numbered site, kind and key**, as the wire states one,
read through its index (`partsIndex`): the change each listed part (a
site's number, `none` outside storage, a kind and a key) has, `keep` at a
part it does not list. -/
def protocolOfParts {P : TolerantFrames.ReadOnly.Package} (num : P.Site → Nat)
    (idx : Std.HashMap (Option Nat × Nat × Option PropKey) Change) : Protocol P := fun p =>
  idx.getD (p.site.map num, kindCode p.kind, p.key) .keep

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

/-- **A call of a value of outside code**: node `l` of code `m` calls a
callee that is no slot naming a code's signature at the context `c` (a
parameter's value, a callback, a computed callee), as the flow's
signatures read it. -/
def outsideCalleeAt (c : FCode P) (m : Code) (l : Nat) : Bool :=
  match m.1[l]? with
  | some (.invoke (.var j) _ _) => ((c.node l).fnAt j).isNone
  | some (.invoke ..) => true
  | _ => false

/-- **The framed call nodes of a code**: its call nodes framed at some
context of the code in the flow. -/
def framedCallNodes (F : FFlow P) (host : Nat → Bool) (m : Code) : List Nat :=
  (List.range m.1.length).filter fun l => (match m.1[l]? with | some (.invoke ..) => true | _ => false) &&
    (F.ctxs m).any fun (_, c) => framedNodeAt F host c m l

/-- **The supports a framed call keeps** (`probeFrames`'s check, decided):
of the supports `Ss` over node `l`'s slots, those passing `frameCheckAt` at
the call's protocol $`\Psi_c`$ (the component's protocol `ΨC` joined with
the client obligation `Θ` and the depth charges of the call's reach) and
the callee's effect `Φ`, at every context of code `m` and every node of the
call's continuation and handler that may call outside code or makes a
framed call (the node itself where none does). The call's reach $`L(c)`$
is that of the call sets of every node sharing the call's continuation and
handler, at every context: the proved check records a frame's node by its
continuation and handler alone (`Fits.frameC`, `NodeOf`). -/
def framedSupportsAt (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (host : Nat → Bool) (ΨC Θ : Protocol P)
    (m : Code) (l : Nat) (Φ : Footprint) (prot : Region → Bool) (Ss : List Footprint) : List Footprint :=
  let kx := m.2[l]?
  let sharing := (List.range m.2.length).filter fun l' => m.2[l']? == kx
  -- (the call sets of every node sharing the continuation and handler, at
  -- every context, joined: callee, receiver and each argument position)
  let sets := (F.ctxs m).flatMap fun (_, c) => sharing.flatMap fun l' => callsAtNode F c m l'
  let Sf := sets.flatMap (·.1)
  let Sr := sets.flatMap (·.2.1)
  let width := (sets.map (·.2.2.length)).foldl max 0
  let args := (List.range width).map fun i => sets.flatMap fun s => s.2.2.getD i []
  let L := callReach F lay Sf Sr args
  let Wc := depthCharges F L
  let Ψ : Protocol P := fun p => ((ΨC p).max (Θ p)).max (Wc p)
  -- (at each context, the nodes the check reads)
  let required := (F.ctxs m).map fun (_, c) =>
    let req := sharing.filter fun l' => (c.node l').out || framedNodeAt F host c m l'
    (c, if req.isEmpty then [l] else req)
  Ss.filter fun S => required.all fun (c, req) => req.all fun l' =>
    frameCheckAt classQuery Ψ Φ S F.flow.H (c.node l').envAt prot

/-- **A flow holding a second code with the proposals of a first** at each
of its contexts: the request's code beside its realized code, whose nodes
below the request's length are the request's (`realizedFlowB`). -/
def _root_.Verification.TolerantFrames.ReadOnly.FFlow.withCode (F : FFlow P) (m₁ m₂ : Code) : FFlow P :=
  if (F.codes.any fun e => decide (e.1 = m₂)) then F else { F with codes := F.codes ++ [(m₂, F.ctxs m₁)] }
end

/-- **A framed plan's document** (the producer's inputs, the draft's
plan on the wire): the component, its entries, the client obligation by
kind and the component's protocol by numbered site, kind and key (each change
but `keep`), and each framed call node with the supports its frame keeps. -/
def framedDocument (C : Nat) (entries : List String) (theta : List (Option Verification.Kind × Change))
    (psi : List (Option Nat × Option Verification.Kind × Option PropKey × Change)) (framed : List (Nat × List Footprints.Footprint)) :
    Json :=
  Json.mkObj [("component", toJson C), ("entries", toJson entries),
    ("theta", Json.arr (theta.map fun (k, c) => Json.arr #[kindNameJ k, EffectCodec.changeJ c]).toArray),
    ("protocol", Json.arr (psi.map fun (s, k, key, c) =>
      Json.arr #[toJson s, kindNameJ k, (key.map EffectCodec.keyJ).getD .null, EffectCodec.changeJ c]).toArray),
    ("framed", Json.arr (framed.map fun (l, Ss) => Json.mkObj [("node", toJson l),
      ("supports", Json.arr (Ss.map EffectCodec.frameJ).toArray)]).toArray)]

end Verification.SourceClaimJson
