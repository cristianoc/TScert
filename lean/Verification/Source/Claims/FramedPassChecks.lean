import Verification.Source.Claims.FramedBinding
import Verification.Source.ComponentChecks

/-! # The binding checks a framed plan's pass reads from its component

The draft "Accepting a unit through the read-only frame"
(`docs/drafts/framed-acceptance.md`, "The binding checks",
"Initialization" and "The plan"). Beside the checks over the plan's flow
(`ReadOnlyBinding`, `FramedBinding`), the pass reads from the component
family the declaration document describes:

- **The `@clients` rows** (`componentRows`): the rows of the exported
  types of `C`'s module, which `clientsB` compares with the wire's
  $`\Theta_C`$.
- **The checks (S), (K) and (O)** (`componentFrameDiags`): their failures
  at `C`'s bodies (`ComponentChecks.suspensionDiags`, `marksDiags`,
  `ownershipDiags`), each rendered with its module and span.
- **The read-only types** (`readOnlyInputs`, `readOnlyB`): an input of the
  member is read-only where its entry code's declared shape is read-only
  throughout (`ComponentChecks.readOnlyShape`); `readOnlyB` decides that
  every type a plan reads read-only is one.
- **The initialization** (`initB`): the initialization's code allocates,
  node by node, each module function's closure once, in an order where
  every linked capture is the slot holding the closure of the function the
  capture's name names, allocated earlier, and every other capture an
  identity of the realm's heap; its continuations bind each closure in
  turn and return; its last node is the array of the entries' closures,
  each read at the slot holding it. -/

namespace Verification.SourceClaimJson
open Lean ProgramTyping SourceExtraction ControlFlow LabelStore
open Verification.TolerantFrames.ReadOnly

/-- **The `@clients` rows of a component**: the rows of the exported types
of its module. -/
def componentRows (F : ComponentWire.Components) (C : Nat) : List ComponentWire.Clients :=
  match F.components[C]? with
  | some k => F.clients.filter (·.module == k.location)
  | none => []

/-- **The failures of the checks (S), (K) and (O) at a component's bodies**,
as the component's outcome renders them (`ComponentChecks.familyOutcome`). -/
def componentFrameDiags (F : ComponentWire.Components) (file : String) (fns : List (String × Span × Bool))
    (C : Nat) : List String :=
  let cx := ComponentChecks.Ctx.of F
  let cx := { cx with escaped := cx.escaping }
  let boundary := cx.boundaryValues
  let quiet := cx.quiet cx.runsOutside
  ((ComponentChecks.suspensionDiags cx file fns ++ ComponentChecks.marksDiags cx ++
    ComponentChecks.ownershipDiags cx boundary quiet).filter (·.component == C)).map ComponentChecks.Diag.render
    |>.eraseDups

/-- **The declared shapes of a member's parameters**: those of the code its
component's interface names under the member's name; none where no entry
names it. -/
def memberShapes (F : ComponentWire.Components) (C : Nat) (member : String) : List (Option ComponentWire.Shape) :=
  match (F.components[C]?).map ComponentWire.Component.interface with
  | some (ComponentWire.Interface.known es) => match es.find? (·.name == member) with
    | some e => match F.codes.find? fun c => c.module == e.module && c.pos == e.pos with
      | some c => c.params.map (·.2.2)
      | none => []
    | none => []
  | _ => []

/-- A declared shape read-only throughout (`ComponentChecks.readOnlyShape`);
a position with no declared shape is writable. -/
def shapeReadOnly (F : ComponentWire.Components) : Option ComponentWire.Shape → Bool
  | some t => ComponentChecks.readOnlyShape F.types (ComponentWire.shapeLimit * (F.types.length + 1)) [] t
  | none => false

section
variable {ι : Type} [Labels ι]

/-- **The read-only inputs of a member**: each input whose parameter's
declared shape is read-only throughout. -/
def readOnlyInputs (F : ComponentWire.Components) (C : Nat) (member : String) (inputs : List (Ty ι)) :
    List (Ty ι) :=
  (inputs.zip (memberShapes F C member)).filterMap fun (T, s) => if shapeReadOnly F s then some T else none

/-- **The read-only types check** (`ro_of_readOnlyShape`'s premise),
decided: every type the plan reads read-only is a read-only input. -/
def readOnlyB (F : ComponentWire.Components) (C : Nat) (member : String) (inputs readOnly : List (Ty ι)) : Bool :=
  let ro := readOnlyInputs F C member inputs
  readOnly.all (ro.contains ·)
end

/-- **The initialization check** (`initB`, the draft "Initialization"): the
code `(E, K)` of the initialization of a component whose module functions
have the codes `codes` and the names, arities and slot names `names`
(parallel lists), whose realm's heap has `realmN` identities and whose
entries are `entries`. Node `k` below the last allocates a closure of
`C`'s code (`ofC`) of one module function's code, entered at its last node
(the realized code's prologue), with no field and no initializer; each
capture whose name names a module function is the slot holding the closure
of that function, allocated at an earlier node (the slots after node `k`'s
predecessors bound are their closures, the latest first), and every other
capture an identity of the realm's heap. Each function's closure is
allocated once. Each node's continuation binds its value and continues at
the next node, the last's returns; the last node is the array of the
entries' closures, each read at the slot holding it. -/
def initB (ofC : ComponentTag → Bool) (realmN : Nat) (codes : List Code) (names : List (String × Nat × List String))
    (entries : List String) (E : List Tm) (K : List (Continuation × Option Target)) : Bool :=
  let n := names.length
  -- (the module function whose code node `k` closes over)
  let fnAt (k : Nat) : Option Nat := match E[k]? with
    | some (.makeAt (.graph _ E' K' _ _ _ _ _) _ _) => codes.findIdx? (· == (E', K'))
    | _ => none
  let nameAt (k : Nat) : Option String := (fnAt k).bind fun g => (names[g]?).map (·.1)
  -- (slot `v` at node `k` holds the closure node `k - 1 - v` allocated)
  let slotName (k v : Nat) : Option String := if v < k then nameAt (k - 1 - v) else none
  let capOk (k : Nat) (x : String) (c : Tm) : Bool :=
    if names.any (·.1 == x) then (match c with | .var v => slotName k v == some x | _ => false)
    else (match c with | .objAt [] _ loc => decide (loc < realmN) | _ => false)
  E.length == n + 1 && codes.length == n &&
  K == ((List.range n).map fun k => (Continuation.bind ⟨k + 1, none⟩, (none : Option Target))) ++ [(.ret, none)] &&
  (List.range n).all (fun k => match E[k]?, fnAt k with
    | some (.makeAt (.graph ar E' _ s caps inv rest tag) fs inits), some g => match names[g]? with
      | some (_, ar', sib) => ar == ar' && s + 1 == E'.length && ofC tag && fs.isEmpty && inits.isEmpty &&
          inv == .call && !rest && caps.length == sib.length && (sib.zip caps).all fun (x, c) => capOk k x c
      | none => false
    | _, _ => false) &&
  ((List.range n).filterMap fnAt).eraseDups.length == n &&
  match E[n]? with
  | some (.arrLit xs) => xs.length == entries.length && (xs.zip entries).all fun (c, x) => match c with
    | .var v => slotName n v == some x
    | _ => false
  | _ => false

/-- **The body of a code of a component** (the draft, "One site per body
allocation"): a module function's realized code's is its request's, its
node lists without the prologue's node; every other code's is itself. -/
def moduleBody (codes : List Code) (m : Code) : Code :=
  if codes.contains m then (m.1.dropLast, m.2.dropLast) else m

/-- The realized code's body is the request's code (proved). -/
theorem moduleBody_realized {σ ι : Type} [Labels ι] [StoreView σ ι] {codes : List Code}
    {r : SourceRequest σ ι} (h : realizedCode r ∈ codes) : moduleBody codes (realizedCode r) = requestCode r := by
  simp only [moduleBody, List.contains_iff_mem.mpr h, if_true]
  simp [realizedCode, requestCode]

/-- The position of an element of an append (proved). -/
theorem idxOf_append' {α : Type} [BEq α] [LawfulBEq α] (a : α) : ∀ (l₁ l₂ : List α),
    (l₁ ++ l₂).idxOf a = if a ∈ l₁ then l₁.idxOf a else l₁.length + l₂.idxOf a
  | [], l₂ => by simp
  | x :: xs, l₂ => by
    by_cases h : x = a
    · subst h; simp [List.idxOf_cons_self]
    · have ih := idxOf_append' a xs l₂
      simp only [List.cons_append, List.idxOf_cons, List.mem_cons, List.length_cons]
      have : (x == a) = false := by simp [h]
      simp only [this, cond_false, ih]
      by_cases hm : a ∈ xs
      · simp [hm]
      · simp [hm, Ne.symm h]; omega

/-- The position of a pair in a list paired with one first component
(proved). -/
theorem idxOf_map_pair {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (b : α) (kx : β) :
    ∀ l : List β, (l.map (b, ·)).idxOf (b, kx) = l.idxOf kx
  | [] => by simp
  | x :: xs => by
    by_cases h : x = kx
    · subst h; simp [List.idxOf_cons_self]
    · have : ((b, x) == (b, kx)) = false := by simp [h]
      have h2 : (x == kx) = false := by simp [h]
      simp only [List.map_cons, List.idxOf_cons, this, h2, cond_false, idxOf_map_pair b kx xs]

/-- **The position of a body's first node key among the bodies'
allocation occurrences**: the node keys of the bodies before its first
listing. -/
def offsetOf : List Code → Code → Nat
  | [], _ => 0
  | b' :: rest, b => if b' = b then 0 else b'.2.length + offsetOf rest b

/-- **An occurrence's position is its body's offset and its key's
position** (proved). -/
theorem allocOccs_idxOf {b : Code} {kx : NodeKey} (hk : kx ∈ b.2) :
    ∀ {bodies : List Code}, b ∈ bodies → (allocOccs bodies).idxOf (b, kx) = offsetOf bodies b + b.2.idxOf kx
  | [], h => absurd h (List.not_mem_nil)
  | b' :: rest, h => by
    have hsplit : allocOccs (b' :: rest) = b'.2.map (b', ·) ++ allocOccs rest := by
      simp [allocOccs, List.flatMap_cons]
    rw [hsplit, idxOf_append']
    by_cases he : b' = b
    · subst he
      have hm : (b', kx) ∈ b'.2.map (b', ·) := List.mem_map.mpr ⟨kx, hk, rfl⟩
      simp [hm, offsetOf, idxOf_map_pair]
    · have hm : (b, kx) ∉ b'.2.map (b', ·) := by
        intro hm
        obtain ⟨_, _, he'⟩ := List.mem_map.mp hm
        exact he (Prod.mk.inj he').1
      have hr : b ∈ rest := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm he
        · exact h
      simp only [hm, if_false, List.length_map, offsetOf, he, allocOccs_idxOf hk hr]
      omega

/-- The canonical site of an occurrence, read from its body's offset where
the body is listed (`canonSite` otherwise). -/
def canonSiteAt (base : Nat) (bodies : List Code) (b : Code) (kx : NodeKey) (arr : Bool) (off : Option Nat) : Nat :=
  match off with
  | some o => base + 2 * (o + b.2.idxOf kx) + if arr then 1 else 0
  | none => canonSite base bodies b kx arr

/-- A body's offset, where it is listed. -/
def offsetAt (bodies : List Code) (b : Code) : Option Nat := if bodies.contains b then some (offsetOf bodies b) else none

theorem canonSiteAt_eq {base : Nat} {bodies : List Code} {b : Code} {kx : NodeKey} {arr : Bool} (hk : kx ∈ b.2) :
    canonSiteAt base bodies b kx arr (offsetAt bodies b) = canonSite base bodies b kx arr := by
  unfold offsetAt
  split
  · rename_i hb
    simp only [canonSiteAt, canonSite, allocOccs_idxOf hk (List.contains_iff_mem.mp hb)]
  · rfl

/-- **The canonical allocation sites check, each body's offset computed
once** (`allocCanonB`'s value, `allocCanonAtB_eq`): the executable form the
pass runs. -/
def allocCanonAtB {P : Package} (num : P.Site → Nat) (base : Nat) (bodies : List Code) (bodyOf : Code → Code)
    (F : FFlow P) : Bool :=
  F.codes.all fun (m, cs) =>
    let b := bodyOf m
    let off := offsetAt bodies b
    cs.all fun (_, fc) => m.2.all fun kx =>
      !b.2.contains kx ||
        ((fc.allocAt kx).obj.map num == some (canonSiteAt base bodies b kx false off) &&
          (fc.allocAt kx).arr.map num == some (canonSiteAt base bodies b kx true off))

/-- **The executable form is the check** (proved). -/
theorem allocCanonAtB_eq {P : Package} (num : P.Site → Nat) (base : Nat) (bodies : List Code) (bodyOf : Code → Code)
    (F : FFlow P) : allocCanonAtB num base bodies bodyOf F = allocCanonB num base bodies bodyOf F := by
  unfold allocCanonAtB allocCanonB
  congr 1; funext e; obtain ⟨m, cs⟩ := e
  simp only
  congr 1; funext e; obtain ⟨_, fc⟩ := e
  simp only
  congr 1; funext kx
  by_cases hk : (bodyOf m).2.contains kx
  · have hm := List.contains_iff_mem.mp hk
    simp only [canonSiteAt_eq hm]
  · rw [Bool.not_eq_true] at hk
    simp only [hk, Bool.not_false, Bool.true_or]

/-- **The refusal of the binding checks that read the component alone**
(the draft, "The binding checks"), evaluated once per component: its flow
(`FFlow.check`), its marks (`marksB`), every module function's realized
and request codes covered (`codesCoverB`), its allocation sites some and
numbered canonically by the codes' bodies (`moduleBody`) from three per
code (`allocSomeB`, `allocCanonB` in its executable form `allocCanonAtB`), its initialization (`initB`) and the
checks (S), (K) and (O) at its bodies; `none` where every one passes. -/
def componentBindingRefusal {ofC : ComponentTag → Bool} {O : List (Option Nat)} (F : FFlow (markedPackage ofC O))
    (lay : List (Nat × Bool × Nat × Nat)) (codes : List Code) (names : List (String × Nat × List String))
    (entries : List String) (realmN : Nat) (initE : List Tm) (initK : List (Continuation × Option Target))
    (family : ComponentWire.Components) (file : String) (fns : List (String × Span × Bool)) (C : Nat) :
    Option String :=
  let body := moduleBody codes
  let checks : List (String × (Unit → Bool)) := [
    ("its flow (FFlow.check)", fun _ => F.check), ("its marks (marksB)", fun _ => F.marksB),
    ("its codes covered (codesCoverB)", fun _ => codesCoverB F (codes ++ codes.map body)),
    ("its allocation sites (allocB)", fun _ =>
      allocSomeB F && allocCanonAtB id (3 * lay.length) (F.codes.map fun e => body e.1) body F),
    ("its initialization (initB)", fun _ => initB ofC realmN codes names entries initE initK)]
  match checks.find? (!·.2 ()) with
  | some (w, _) => some s!"framed plan: the binding check of {w} fails"
  | none => (componentFrameDiags family file fns C).head?.map fun d =>
    s!"framed plan: the checks (S), (K) and (O) of its component fail: {d}"

end Verification.SourceClaimJson
