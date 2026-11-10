import Verification.Programs.CertificateProducer

namespace Verification.SinglePassStats
open ProgramTyping ControlFlow CertificateProducer

def termKind : Tm → String
  | .var _ => "var" | .invoke .. => "invoke" | .construct .. => "construct" | .letE .. => "letE"
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => "lit"
  | .objAt .. => "objAt" | .makeAt .. => "makeAt" | .readAt .. => "readAt" | .indexAt .. => "indexAt"
  | .writeAt .. => "writeAt" | .test .. => "test" | .ite .. => "ite" | .arith .. => "arith"
  | .arr _ => "arr" | .arrLit _ => "arrLit" | .elemAt .. => "elemAt" | .setElem .. => "setElem"
  | .lenOf _ => "lenOf" | .spread _ => "spread" | .throw _ => "throw" | .merge .. => "merge"
  | .makeKey .. => "makeKey" | .goto .. => "goto" | .frame .. => "frame"

private unsafe def samePtrImpl {α : Type} (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b
/-- Whether two values are one object (a measurement; false when unknown). -/
@[implemented_by samePtrImpl] def samePtr {α : Type} (_a _b : α) : Bool := false

def bump (m : Std.HashMap String Nat) (k : String) (n : Nat := 1) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + n)

def showCounts (m : Std.HashMap String Nat) : String :=
  ", ".intercalate ((m.toList.mergeSort fun a b => a.2 ≥ b.2).map fun (k, n) => s!"{k} {n}")

/-- A map as runs `target..+len <- source`. -/
def runs (slots : List Nat) : String := Id.run do
  let mut out : List String := []
  let mut start := 0
  let mut i := 0
  let arr := slots.toArray
  while i < arr.size do
    let s0 := arr[i]!
    let mut j := i + 1
    while j < arr.size && arr[j]! == s0 + (j - i) do j := j + 1
    out := out ++ [s!"{i}+{j-i}<-{s0}"]
    i := j
  let _ := start
  start := 0
  return " ".intercalate out

/-- Shape statistics of a graph: what a single forward pass must handle. -/
instance : Inhabited Node := ⟨⟨.nul, .ret, none⟩⟩

def stats (P : Program) (claims : List (PointClaim ι)) (cuts : List Nat)
    (assertions : List (Nat × HeapKnowledge.Knowledge)) : String := Id.run do
  let widths := (claims.map (·.context.length)).toArray
  let mut kinds : Std.HashMap String Nat := {}
  let mut conts : Std.HashMap String Nat := {}
  let mut maps : Std.HashMap String Nat := {}
  let mut preds : Array Nat := Array.replicate P.length 0
  let mut handlers := 0
  let mut moved := 0
  let mut samples : List String := []
  for (node, l) in P.zipIdx do
    kinds := bump kinds (termKind node.expression)
    conts := bump conts (match node.continuation with
      | .ret => "ret" | .bind _ => "bind" | .effect _ => "effect" | .branch .. => "branch"
      | .branchBind .. => "branchBind" | .tagBind .. => "tagBind")
    if node.handler.isSome then handlers := handlers + 1
    let pushed := match node.continuation with | .effect _ | .branch .. => false | _ => true
    let src := widths.getD l 0 + (if pushed then 1 else 0)
    for t in successors node.continuation ++ node.handler.toList do
      preds := preds.modify t.label (· + 1)
      let w := widths.getD t.label 0
      match t.mapping with
      | none => maps := bump maps (if w == src then "none-same" else "none-diff")
      | some slots =>
        let ident := slots == List.range slots.length
        maps := bump maps (if ident && w == src then "some-ident"
          else if ident then "some-prefix" else "some-perm")
        if !ident && samples.length < 12 then
          samples := samples ++ [s!"[{l} {termKind node.expression} src {src} -> {t.label} w {w}: {runs slots}]"]
        if !ident then
          moved := moved + ((slots.zipIdx.filter fun (s, i) => s != i).length)
  -- Sharing between claims: slot types and context tails that are one object.
  let mut sameSlots := 0
  let mut allSlots := 0
  let mut sameTails := 0
  let mut edgesNone := 0
  for (node, l) in P.zipIdx do
    let some c := claims[l]? | continue
    for t in successors node.continuation do
      let some d := claims[t.label]? | continue
      if t.mapping.isNone then
        edgesNone := edgesNone + 1
        let src := match node.continuation with | .effect _ | .branch .. => c.context | _ => c.type :: c.context
        if samePtr src d.context || (match src, d.context with | _ :: a, _ :: b => samePtr a b | _, _ => false) then sameTails := sameTails + 1
        for (A, B) in src.zip d.context do
          allSlots := allSlots + 1
          if samePtr A B then sameSlots := sameSlots + 1
  let merges := preds.foldl (fun n p => if p > 1 then n + 1 else n) 0
  let atoms := assertions.foldl (fun n (_, k) => n + k.indices.length + k.cells.length + k.values.length
    + k.links.length + k.elems.length) 0
  let meanW := (widths.foldl (· + ·) 0) / (max widths.size 1)
  return s!"nodes {P.length}; mean width {meanW}; cuts {cuts.length}; merges {merges}; handlers {handlers}; assertions {assertions.length} ({atoms} atoms)\n  kinds: {showCounts kinds}\n  continuations: {showCounts conts}\n  mappings: {showCounts maps}; slots moved by permuting maps {moved}; identity edges {edgesNone}, sharing a tail {sameTails}; slot types one object {sameSlots} of {allSlots}\n  {"\n  ".intercalate samples}"

/-- The chain of predecessors of a node, `depth` steps back (the first
predecessor each time). -/
def trace (P : Program) (claims : List (PointClaim ι)) (cuts : List Nat) (l : Nat) (depth : Nat) : String := Id.run do
  let mut preds : Array (List (Nat × Target)) := Array.replicate P.length []
  for (node, k) in P.zipIdx do
    for t in successors node.continuation ++ node.handler.toList do
      if t.label < preds.size then preds := preds.modify t.label ((k, t) :: ·)
  let mut out : List String := []
  let mut cur := l
  for _ in List.range depth do
    let ps := preds.getD cur []
    let some (p, t) := ps.head? | break
    let node := P[p]!
    let w := (claims[p]?).map (·.context.length) |>.getD 0
    out := out ++ [s!"{p}{if cuts.contains p then "(cut)" else ""} [{ps.length} preds of {cur}] w{w} {(reprStr node.expression).take 160} -> {match t.mapping with | none => "id" | some m => runs m}"]
    cur := p
  return "\n".intercalate out

end Verification.SinglePassStats
