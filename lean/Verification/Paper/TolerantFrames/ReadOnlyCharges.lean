import Verification.Paper.TolerantFrames.ReadOnlyFlowSolve
import Verification.Paper.TolerantFrames.ReadOnlyCallFrame

/-! # Read-only handles: the charges of a component's code

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "Definitions" and "Charges"). The
charges the frame's protocols read, computed from a finite flow
(`FFlow`) and the lowered node expressions it holds:

- **The kinds a term's writes may change** (`writesK`): for each write,
  the kinds its written location may have; total, structural over the
  term. **The charges of a set of codes** `Ch(M)` (`codeKinds`,
  `codesKinds`, `flowKinds`): the kinds of each node's writes.
- **The closure of sites** $`\overline{S}`$ (`capClose`): the least superset
  closed under the heap of sites' contents and under captures, computed by
  iteration and checked closed (`capClosedB`, `capClosedB_sound`).
- **The calls of a term** (`callSets`, structural) and **the segment's
  codes** $`\mathrm{seg}(c)`$ (`segCodes`), computed and checked closed
  (`segClosedB`, `segClosedB_sound`); **a framed call** (`reachesOut`).
- **The protocols**: $`\Psi_C`$ (`componentProtocol`), the reach of a call
  $`L(c)`$ (`callReach`) and the depth charges $`W_c`$ (`depthCharges`, at
  every code of the flow), each a protocol from charges (`probeProtocol`): a
  part changed by any change at a charged kind, kept at a local site outside
  the held set. -/
namespace Verification.TolerantFrames.ReadOnly
open Verification ControlFlow

variable {P : Package} [DecidableEq P.Site] [Hashable P.Site]

/-! ## The charges of a term -/

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
/-- **The kinds a term's writes may change** (`writesK`, the draft "Framed
acceptance", "Charges"): for each field write the kinds a slot under its
key may have (`slotBound`), for each element store an element cell, at
every position of the term that its own steps evaluate. It reads no
closure's code, no bound function's parts and no run (`goto`, `frame`):
those are evaluated in other frames, or are values. Structural over the
term and its argument lists. -/
def writesK : Tm → List (Option Verification.Kind)
  | .writeAt k x y => roleKinds (Footprints.slotBound k) ++ writesK x ++ writesK y
  | .setElem x i v => [some .elem] ++ writesK x ++ writesK i ++ writesK v
  | .letE x b => writesK x ++ writesK b
  | .invoke f r args => writesK f ++ writesK r ++ writesKs args
  | .construct f args => writesK f ++ writesKs args
  | .makeAt _ _ inits | .arrLit inits => writesKs inits
  | .indexAt x y | .arith _ x y | .elemAt x y | .merge _ x y | .makeKey x y => writesK x ++ writesK y
  | .ite x y z => writesK x ++ writesK y ++ writesK z
  | .readAt _ x | .test _ x | .lenOf x | .spread x | .throw x => writesK x
  | _ => []
/-- The kinds the writes of a list of terms may change. -/
def writesKs : List Tm → List (Option Verification.Kind)
  | [] => []
  | x :: xs => writesK x ++ writesKs xs
end

@[simp] theorem writesKs_eq (xs : List Tm) : writesKs xs = xs.flatMap writesK := by
  induction xs <;> simp_all [writesKs]

/-- **The charges of one code** `Ch({m})`: the kinds the writes of each of
its node expressions may change. -/
def codeKinds (m : Code) : List (Option Verification.Kind) := m.1.flatMap writesK

/-- The charges of a set of the flow's codes, by index. -/
def codesKinds (F : FFlow P) (M : List Nat) : List (Option Verification.Kind) :=
  M.flatMap fun i => match F.codes[i]? with
    | some (m, _) => codeKinds m
    | none => []

/-- The charges of every code of a flow, `Ch` of all codes of `C`. -/
def flowKinds (F : FFlow P) : List (Option Verification.Kind) := F.codes.flatMap fun (m, _) => codeKinds m

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

mutual
/-- **The calls of a term** at a node's slots: for each `invoke` and
`construct`, the callee's set, the receiver's and the arguments', each
`top` where it has no computed set. Structural over the term and its
argument lists. -/
def callSets (F : FFlow P) (top : Sites P) (τ : Nat → Sites P) (φ : Nat → Option FnSig) (a : FrameAt P)
    (κ : Nat) (d : Nat) (Γ : Nat → Option (Sites P)) : Tm → List (Sites P × Sites P × List (Sites P))
  | .invoke f r args =>
    let set (x : Tm) := (syn F τ φ a κ d Γ x).getD top
    (set f, set r, args.map set) :: callSets F top τ φ a κ d Γ f ++ callSets F top τ φ a κ d Γ r ++
      callSetsAll F top τ φ a κ d Γ args
  | .construct f args =>
    let set (x : Tm) := (syn F τ φ a κ d Γ x).getD top
    (set f, [], args.map set) :: callSets F top τ φ a κ d Γ f ++ callSetsAll F top τ φ a κ d Γ args
  | .letE x b => callSets F top τ φ a κ d Γ x ++
      callSets F top τ φ a κ (d + 1) (consSites ((syn F τ φ a κ d Γ x).getD top) Γ) b
  | .makeAt _ _ inits | .arrLit inits => callSetsAll F top τ φ a κ d Γ inits
  | .indexAt x y | .writeAt _ x y | .arith _ x y | .elemAt x y | .merge _ x y | .makeKey x y =>
    callSets F top τ φ a κ d Γ x ++ callSets F top τ φ a κ d Γ y
  | .ite x y z | .setElem x y z =>
    callSets F top τ φ a κ d Γ x ++ callSets F top τ φ a κ d Γ y ++ callSets F top τ φ a κ d Γ z
  | .readAt _ x | .test _ x | .lenOf x | .spread x | .throw x => callSets F top τ φ a κ d Γ x
  | _ => []
/-- The calls of a list of terms. -/
def callSetsAll (F : FFlow P) (top : Sites P) (τ : Nat → Sites P) (φ : Nat → Option FnSig) (a : FrameAt P)
    (κ : Nat) (d : Nat) (Γ : Nat → Option (Sites P)) : List Tm → List (Sites P × Sites P × List (Sites P))
  | [] => []
  | x :: xs => callSets F top τ φ a κ d Γ x ++ callSetsAll F top τ φ a κ d Γ xs
end

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

/-- **A protocol from charges** (`probeProtocol`): a part changed by any
change where its kind is among the charged kinds `K`; kept at a local site
outside `held`, and at every other kind. -/
def probeProtocol (K : List (Option Verification.Kind)) (held : Sites P) : Protocol P :=
  let hs : Std.HashSet (Option P.Site) := Std.HashSet.ofList held
  fun p => if p.site.any (fun s => P.mark s = .local) && !hs.contains p.site then .keep
    else if K.contains p.kind then .any else .keep

/-- The capture sites of the codes whose closures a token stands for. -/
def tokenCaps (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (t : Option P.Site) : Sites P :=
  if t.isNone then [] else
  (F.codes.zip lay).flatMap fun ((_, cs), l) => if cs.any (·.2.tok == t) then codeCaptureSites cs l else []

/-- **The protocol** $`\Psi_C`$ (the draft's "Charges"): `Ch` of every code
of `C` at every part but a local part whose site is outside the closure of
the capture sites and `O`, which is kept. -/
def componentProtocol (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) : Protocol P :=
  probeProtocol (flowKinds F) (capClose F (tokenCaps F lay) (captureSites F lay ++ F.O))

/-- **The reach of a call** $`L(c)`$: the closure of its callee's,
receiver's and arguments' sets. -/
def callReach (F : FFlow P) (lay : List (Nat × Bool × Nat × Nat)) (Sf Sr : Sites P) (args : List (Sites P)) :
    Sites P :=
  capClose F (tokenCaps F lay) (Sf ++ Sr ++ args.flatten)

/-- **The depth charges** $`W_c`$ of a call: `Ch` of every code of the flow
at every part but a local part whose site is outside $`L(c)`$, which is
kept. -/
def depthCharges (F : FFlow P) (L : Sites P) : Protocol P :=
  probeProtocol (flowKinds F) L


/-! ## The closures, checked -/

/-- **A set closed under contents and captures, holding `S`**, decided. -/
def capClosedB (F : FFlow P) (caps : Option P.Site → Sites P) (S T : Sites P) : Bool :=
  S.all (T.contains ·) && T.all fun s => (F.contents s ++ caps s).all (T.contains ·)

omit [Hashable P.Site] in
/-- **The closure check is sound** (proved): a set passing it holds `S` and
is closed under the heap of sites' contents and under captures. -/
theorem capClosedB_sound {F : FFlow P} {caps : Option P.Site → Sites P} {S T : Sites P}
    (h : capClosedB F caps S T = true) :
    Sub S T ∧ ∀ s ∈ T, Sub (F.contents s) T ∧ Sub (caps s) T := by
  simp only [capClosedB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.mem_append] at h
  exact ⟨fun s hs => h.1 s hs, fun s hs => ⟨fun s' h' => h.2 s hs s' (.inl h'), fun s' h' => h.2 s hs s' (.inr h')⟩⟩

/-- The codes of a flow whose closures a set may hold: those whose token,
at some context, the set holds. -/
def holdingCodes (F : FFlow P) (S : Sites P) : List Nat :=
  (F.codes.zipIdx.map fun (p : (Code × List (Nat × FCode P)) × Nat) => (p.2, p.1.2.map (·.2.tok))).filterMap
    fun (i, ts) => if ts.any (S.contains ·) then some i else none

/-- **A set of codes closed under a call's segment**, decided: it holds each
code whose token `Sf` holds, and, for each call of each of its codes, each
code whose token the callee's set holds, and, where that callee is a
native step model (`host`), each code whose token an argument's set
holds. -/
def segClosedB (F : FFlow P) (top : Sites P) (host : Nat → Bool) (Sf : Sites P) (seg : List Nat) : Bool :=
  (holdingCodes F Sf).all (seg.contains ·) && seg.all fun i => match F.codes[i]? with
    | some (m, cs) => (codeCalls F top m cs).all fun (f, _, args) =>
        (holdingCodes F f).all (seg.contains ·) &&
          (!(holdingCodes F f).any host || (args.flatMap (holdingCodes F)).all (seg.contains ·))
    | none => true

/-- **The segment check is sound** (proved): a list passing it holds every
code whose token the call's callee set holds, and is closed under the
calls of its codes, through native step models' arguments too. -/
theorem segClosedB_sound {F : FFlow P} {top : Sites P} {host : Nat → Bool} {Sf : Sites P} {seg : List Nat}
    (h : segClosedB F top host Sf seg = true) :
    (∀ i ∈ holdingCodes F Sf, i ∈ seg) ∧
      ∀ i ∈ seg, ∀ m cs, F.codes[i]? = some (m, cs) → ∀ c ∈ codeCalls F top m cs,
        (∀ j ∈ holdingCodes F c.1, j ∈ seg) ∧
          ((holdingCodes F c.1).any host = true → ∀ S ∈ c.2.2, ∀ j ∈ holdingCodes F S, j ∈ seg) := by
  simp only [segClosedB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  refine ⟨fun i hi => h.1 i hi, fun i hi m cs hc c hcc => ?_⟩
  have h2 := h.2 i hi
  rw [hc] at h2
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at h2
  obtain ⟨hf, ha⟩ := h2 c hcc
  refine ⟨fun j hj => hf j hj, fun hh S hS j hj => ?_⟩
  rcases ha with hn | ha
  · exact absurd hh (by simpa [holdingCodes] using hn)
  · exact ha j (List.mem_flatMap.mpr ⟨S, hS, hj⟩)

end Verification.TolerantFrames.ReadOnly
