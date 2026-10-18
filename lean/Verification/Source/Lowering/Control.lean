import Verification.Source.Lowering.State
import Verification.Source.Lowering.Types
import Verification.Source.Lowering.Observations
import Verification.Source.Lowering.Plans

/-! Builds control transfers and their scope mappings. -/
namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

section
variable {ι : Type} [Labels ι]

/-- Branch binding pushes the actual tested value. For a source variable test,
map that variable to the pushed value (the same immutable value), exposing its
proved singleton refinement. Other slots retain their ordinary identities. -/
def branchMapping (width : Nat) (tested : Option Nat) (target : Target) : Target :=
  ⟨target.label, some ((target.mapping.getD (List.range width)).map fun i =>
    if tested == some i then 0 else i+1)⟩

/-- Keep a pre-existing singleton fact rather than replacing it with the
branch witness. In particular, an impossible opposite edge must not force a
contradictory replacement of an otherwise valid immutable binding. -/
@[nospecialize] private def testedSlot (scope : List (ScopeBinding ι)) (Γ : List (Ty ι)) (cond : Fragment.Expr) : Option Nat :=
  do
    let (i, _) ← conditionVariable scope cond
    if Γ[i]? == some [Labels.tru] || Γ[i]? == some [Labels.fls] then none else some i

/-- Share polarity handling between conditionals and loop heads. The saved
condition is in slot zero. Only a syntactically identified immutable variable
may be replaced by the recovered Boolean witness. -/
@[nospecialize] def emitBranch (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree)) (cond : Fragment.Expr)
    (A : Ty Tree) (yes no : Target) : Compiler Target := do
  let G := SourceTypes.graph (← table)
  if let some (i, tag, equal) := conditionTag G scope Γ cond then
    let some C := Γ[i]? | throw "internal tag-guard slot mismatch"
    let adapt := fun t =>
      let mapped := branchMapping scope.length (some i) t
      ⟨mapped.label, some ((mapped.mapping.getD []).map
        (fun j => if j == 0 then 0 else j+1))⟩
    -- The source predicate has already run and all operand claims were checked.
    -- Reading the same immutable variable observes its tag without repeating
    -- any source expression or trusting the saved Boolean's annotation.
    return ← emitAt cond.span (.var (i+1))
      (.tagBind tag (adapt (if equal then yes else no)) (adapt (if equal then no else yes)))
      (A::Γ) C "tag-dispatch" (scope := held ⟨"",some cond.span⟩ :: scope)
  let tested := testedSlot scope Γ cond
  -- Branch on the saved value; the edge maps discard its older copy and
  -- retain the new refinement slot supplied by branchBind.
  let adapt := fun t =>
    let mapped := branchMapping scope.length tested t
    ⟨mapped.label, some ((mapped.mapping.getD []).map
      (fun i => if i == 0 then 0 else i+1))⟩
  -- Negation is handled by swapping successors in compileCondition, so this
  -- dispatch always observes the saved operand itself, retaining its read link.
  -- A value that is not a Boolean is a condition by its truthiness.
  let transfer := if BranchRefinement.onlyBoolean G A then Continuation.branchBind (adapt yes) (adapt no)
    else .tagBind .truthy (adapt yes) (adapt no)
  emitAt cond.span (.var 0) transfer (A::Γ) A
    (scope := held ⟨"",some cond.span⟩ :: scope)

/-- Whether a condition holds an `Array.isArray` test. -/
def arrayTested : Fragment.Expr → Bool
  | .not _ e => arrayTested e
  | .logical _ _ l r => arrayTested l || arrayTested r
  | .shapeTest _ .isArray _ _ => true
  | _ => false

/-- What a call promises of its actual: a call whose callee's type holds a
promise signature (a type guard's, `asserts` false; an assertion function's,
`asserts` true), the callee a name, or a method or field of a name's object, of an
actual that is an immutable name. Of several promise signatures (overloads),
the first whose parameters hold the types of the actuals that are names. The
actual's slot and the promise's type; the graph checker proves it from the
callee's signature at the call (`PromiseCalls.promiseCall_sound`). -/
@[nospecialize] def promiseNarrowing (G : PositiveGraphs.NormalGraph ι) (scope : List (ScopeBinding ι))
    (Γ : List (Ty ι)) (asserts : Bool) (e : Fragment.Expr) (original : String → String := id) :
    Option (Nat × Ty ι) := do
  let (callee, args) ← match e with
    | .call _ callee args [] [] | .invoke _ callee args [] [] => some (callee, args)
    | _ => none
  let slotType := fun (name : String) => do
    let i ← valueSlot scope (original name)
    return (i, ← Γ[i]?)
  -- The callee's signatures, as (parameters, result, effect).
  let sigs : List (List (Ty ι) × Ty ι × Effect) ← match callee with
    | .var _ f => do
      let (_, F) ← slotType f
      let [.arrs L _] := PositiveRules.expand G F | none
      pure (L.map fun s => (s.arguments, s.result, s.effect))
    | .read _ fld (.var _ o) => do
      let (_, O) ← slotType o
      match ProgramTyping.memberOf G O fld with
      | some m => pure (m.calls.map fun s => (s.arguments, s.result, s.effect))
      | none =>
        let F ← fieldRow G O fld
        let [.arrs L _] := PositiveRules.expand G F | none
        pure (L.map fun s => (s.arguments, s.result, s.effect))
    | _ => none
  let holds := fun (Ds : List (Ty ι)) => (args.zip Ds).all fun (a, D) => match a with
    | .var _ name => match slotType name with
      | some (_, A) => A.all D.contains
      | none => true
    | _ => true
  let promises := sigs.filterMap fun (Ds, T, effect) => match effect.promise, asserts with
    | some (.guards p), false | some (.asserts p), true => some (Ds, T, p)
    | _, _ => none
  let chosen := match promises with
    | [one] => [one]
    | _ => promises.filter fun (Ds, _, _) => holds Ds
  let (_, T, p) ← chosen.head?
  let .var _ name ← args[p]? | none
  let (j, _) ← slotType name
  return (j, T)

/-- Facts justified on the path to a short-circuit operand. Only immutable
source bindings are refined; every generated edge checks this candidate context.
A true conjunction / false disjunction establishes both operand outcomes. The
other outcome came from either operand: a slot both paths refine holds what
either refined it to (`joinContexts`), and any other slot keeps its input
type. A test of a field of an immutable binding's object refines the object
to the arms whose field can pass it (`fieldSlice`). A passed equality with a
singleton `single` names (`conditionSingletons`) leaves its operand that value
alone, which `tagMember` checks on the edge. -/
@[nospecialize] def conditionContext (G : PositiveGraphs.NormalGraph ι) (scope : List (ScopeBinding ι)) (Γ : List (Ty ι))
    (cond : Fragment.Expr) (answer : Bool) (arrays : Option (Ty ι) := none)
    (single : Tag → Option ι := fun _ => none) (original : String → String := id) : List (Ty ι) :=
  match cond with
  | .not _ e => conditionContext G scope Γ e (!answer) arrays single original
  | .logical _ andOp left right =>
    if answer == andOp then
      conditionContext G scope (conditionContext G scope Γ left answer arrays single original) right answer arrays single original
    else
      joinContexts Γ (conditionContext G scope Γ left answer arrays single original)
        (conditionContext G scope (conditionContext G scope Γ left (!answer) arrays single original) right answer arrays single original)
  | _ =>
    if let (true, some (j, T)) := (answer, promiseNarrowing G scope Γ false cond original) then Γ.set j T
    else if let some (i, tag, equal) := conditionTag G scope Γ cond then
      match tag, answer == equal, arrays with
      | .isArray, true, some R => Γ.set i (arrayRefine G (Γ[i]?.getD []) R)
      | _, holds, _ =>
        let sliced := BranchRefinement.tagSlice G (Γ[i]?.getD []) tag holds
        match (if holds && !sliced.isEmpty then single tag else none) with
        | some l => Γ.set i [l]
        | none => Γ.set i sliced
    else if let some (i, f, tag, equal) := fieldConditionTag scope cond then
      -- The test's dispatch re-reads the field and records its link, which
      -- justifies the object's arms on the edge (`fieldSlice`).
      Γ.set i (BranchRefinement.fieldSlice G (Γ[i]?.getD []) f tag (answer == equal))
    else if let some i := testedSlot scope Γ cond then
      -- A tested Boolean is the outcome; any other tested value is of the
      -- labels its truthiness admits.
      if BranchRefinement.onlyBoolean G (Γ[i]?.getD []) then
        Γ.set i (if answer then [Labels.tru] else [Labels.fls])
      else Γ.set i (BranchRefinement.tagSlice G (Γ[i]?.getD []) .truthy answer)
    else Γ
where
  /-- Two paths' contexts over the same slots: a slot either path leaves at
  its input type keeps it, and one both refine holds the labels of both. -/
  joinContexts (Γ L R : List (Ty ι)) : List (Ty ι) :=
    (List.range Γ.length).map fun j =>
      let g := Γ[j]?.getD []
      let l := L[j]?.getD g
      let r := R[j]?.getD g
      if l == g || r == g then g else l ++ r.filter fun a => !l.contains a

/-- The singleton label of each strict equality a condition's leaves test
whose passing leaves the operand that one value (`familyMember`): a string,
or a number other than a zero. -/
@[nospecialize] partial def conditionSingletons (G : PositiveGraphs.NormalGraph Tree)
    (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree)) : Fragment.Expr → Compiler (List (Tag × Tree))
  | .not _ e => conditionSingletons G scope Γ e
  | .logical _ _ l r => return (← conditionSingletons G scope Γ l) ++ (← conditionSingletons G scope Γ r)
  | e => match conditionTag G scope Γ e with
    | some (_, .strEq s, _) => return [(.strEq s, ← lower (SourceTypes.use (.strLit s)))]
    | some (_, .numEq b, _) =>
      if b &&& 0x7fffffffffffffff != 0 then return [(.numEq b, ← lower (SourceTypes.use (.numLit b)))]
      else return []
    | _ => return []

/-- The lookup `conditionContext` reads singletons through. -/
def singletonOf (singles : List (Tag × Tree)) (tag : Tag) : Option Tree :=
  (singles.find? (·.1 == tag)).map (·.2)

/-- The fresh array an array pattern's rest collects from the array at slot
`obj` of `A`: the positions from `start` on, read into a store. They are a
fixed list of reads where `A` is one tuple of required positions, whose
length is exact (`listT`); an array of any other length has a slice of
unknown length for its rest, which no list of reads is. The array is claimed
at the rest's span, like an array literal. The store's term, the store's
type and the array's claimed type. -/
@[nospecialize] def restArray (fc : SourceClaims.Function Tree) (A : Ty Tree) (obj start : Nat) (restPos : Span) :
    Compiler (Tm × Ty Tree × Ty Tree) := do
  let G := SourceTypes.graph (← table)
  let some S := storeOf G A | throw "an array rest needs one array contract: over a union of arrays of different lengths its rest is a slice of a length known only at run time"
  let [.list T []] := PositiveRules.expand G S | throw restOfUnknownLength
  if !T.optional.isEmpty || T.rest.isSome then throw restOfUnknownLength
  let C ← claimAt fc restPos
  let some Sr := storeOf (SourceTypes.graph (← table)) C | throw "an array rest needs an array claim"
  let reads ← (List.range (T.required.length - start)).mapM fun j => do
    return Tm.elemAt (.readAt SourceTypes.storeField (.var obj)) (← indexTerm (start + j))
  let _ ← arrayObject Sr
  return (.arrLit reads, Sr, C)

/-- A slice rest's collection: the call of its `%RestFrom:k%`, `k` the
rest's index, on the array at slot `obj`, after the pattern's reads and
defaults (`Fragment.restFromName`). The array is claimed at the rest's span
with the call's instance. -/
@[nospecialize] def sliceCall (scope : List (ScopeBinding ι)) (obj k : Nat) : Except String Tm := do
  let some (i, _) := resolve scope (Fragment.restFromName k)
    | throw "internal extraction error: a slice rest without its intrinsic"
  return Tm.call (.var i) [.var obj]

/-- What a literal position of an array reads, by the array's contract: a
required position reads at its type, an optional or rest position at its type
or `undefined`, and a position no contract names is refused. A union of
array contracts reads at the union of their positions. -/
@[nospecialize] def positionRead (G : PositiveGraphs.NormalGraph Tree) (A : Ty Tree) (i : Nat) :
    Compiler (Ty Tree) := do
  -- The index is a literal of the read, typed at its singleton; the producer
  -- finds that singleton among the request's types.
  let label ← lower (SourceTypes.use (.numLit (bitsOfNat i)))
  recordHints [label]
  let alts ← (PositiveRules.expand G A).mapM fun c => do
    let store ← match c with
      | .refs fs [] vs _ _ _ => match fs.lookup SourceTypes.storeField <|> vs.lookup SourceTypes.storeField with
        | some S => pure S
        | none => throw "an array pattern requires an array contract"
      | _ => throw "an array pattern requires an array contract"
    (PositiveRules.expand G store).mapM fun c => do
      let .list T [] := c | throw "an array pattern requires an array contract"
      match T.required[i]?, ProgramTyping.positionTy T i with
      | some E, _ => pure E
      | none, some E => pure (E ++ [Labels.undef])
      | none, none =>
        -- A mutable tuple may have grown past its positions: `push` is
        -- allowed on it, so a position past them holds whatever was pushed.
        if T.readonly then throw s!"position {i} is outside the array's contract"
        else throw s!"position {i} is past the positions of a mutable tuple, which `push` may have extended with a value its type does not state there (TypeScript reads it as `undefined`, which is unsound)"
  pure alts.flatten.flatten.eraseDups

/-- An operand of a split comparison: a slot, the field read from it, and
the source expression. -/
abbrev SplitOperand := (Nat × Option PropKey) × Fragment.Expr

/-- A strict comparison of two operands neither of which is a singleton, both
read without effect (a name, or a field of a name), one of them claimed at a
union of singletons, dispatches as the tag tests it amounts to: the split
operand, the other operand, and the split operand's singletons. An immutable
name is split first, as before; otherwise a field read. -/
@[nospecialize] def equalitySplit (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree)) (Γ : List (Ty Tree))
    (l r : Fragment.Expr) :
    Compiler (Option (SplitOperand × SplitOperand × List Tag)) := do
  let G := SourceTypes.graph (← table)
  let operand : Fragment.Expr → Option (Nat × Option PropKey)
    | .var _ name => (valueSlot scope name).map (·, none)
    | .read _ f (.var _ name) => (valueSlot scope name).map (·, some f)
    | _ => none
  let singletons := fun (C : Ty Tree) =>
    if C.isEmpty then none else C.mapM fun a => singletonTag G [a]
  let attempt := fun (s o : Fragment.Expr) (field : Bool) => do
    let some sop := operand s | return none
    let some oop := operand o | return none
    let C ← match sop with
      | (k, none) => if field then pure none else pure Γ[k]?
      | (_, some _) => if field then (some <$> exprType fc s) else pure none
    match C.bind singletons with
    | some tags => return some ((sop, s), (oop, o), tags)
    | none => return none
  for (s, o, field) in [(r, l, false), (l, r, false), (r, l, true), (l, r, true)] do
    if let some x ← attempt s o field then return some x
  return none

/-- A strict comparison of an immutable name with an operand that is not read
without effect (a call, say) claimed at a union of singletons: the operand is
evaluated once, into a slot of its own, and split there; the name, which no
effect changes, is the other operand. -/
@[nospecialize] def savedSplit (fc : SourceClaims.Function Tree) (scope : List (ScopeBinding Tree))
    (l r : Fragment.Expr) : Compiler (Option (Nat × Fragment.Expr × Fragment.Expr × List Tag)) := do
  let G := SourceTypes.graph (← table)
  let attempt := fun (n e : Fragment.Expr) => do
    let .var _ name := n | return none
    let some k := valueSlot scope name | return none
    match e with
    | .var .. | .lit .. | .read _ _ (.var ..) => return none
    | _ =>
      let C ← exprType fc e
      if C.isEmpty then return none
      match C.mapM fun a => singletonTag G [a] with
      | some tags => return some (k, n, e, tags)
      | none => return none
  if let some x ← attempt l r then return some x
  attempt r l


/-- A jump from `scope` to a target over `targetScope`: the target's slots,
read through its own mapping, found in `scope` by descriptor, else by name
(an anonymous slot has no name of its own to be found by). -/
@[nospecialize] def jumpTo (scope : List (ScopeBinding Tree)) (target : Target) (targetScope : List (ScopeBinding Tree)) :
    Compiler Target := do
  let slots ← targetScope.mapM fun b =>
    match (sources scope).idxOf? b.source, (names scope).idxOf? b.source.name with
    | some i, _ | none, some i => pure i
    | none, none => throw s!"internal extraction error: lost binding '{b.source.name}'"
  return ⟨target.label, some ((target.mapping.getD (List.range targetScope.length)).map
    fun i => slots[i]?.getD 0)⟩

end
end Verification.SourceExtraction
