import Verification.Source.Claims.Invocation
import Verification.Programs.LinkAssembly
import Verification.Source.PrimitiveAttachment
import Verification.Source.LinkedRuntime

/-! # Source-bound assembly of the primitive Rust demo

Every closure embeds an accepted request and uses a checked projection of its
invocation frame. The complete module signature and its fixed ordinary call
view are certified independently against that same body.
-/
namespace Verification.Demo
open Lean PositiveGraphs PositiveRules PositiveNormalization ProgramTyping
open SourceClaimJson SourceExtraction RequestJson ControlFlow
open Linking

abbrev Label (F : EquationStore.Frozen) := EquationStore.CheckedLabel F.equations F.primitive
abbrev Request (F : EquationStore.Frozen) :=
  SourceRequest (EquationStore.Checked F.equations F.primitive) (Label F)

structure AcceptedRequest (F : EquationStore.Frozen) where
  request : Request F
  bundle : Bundle (Label F)
  response : Response (Label F)
  accepted : checkRequests [request] bundle = true
  member : (request, response) ∈ [request].zip bundle.functions

/-- Consume a retained singleton unit and its exact evidence. The demo
refuses grouped overloads and qualified generic bodies. -/
def acceptedRequest (f : FilePlans) (i : Nat) (evidence : Json) :
    Except String (AcceptedRequest f.F) := do
  if f.fr.group i != [i] then throw "demo requires singleton function units"
  let [.graph _ _ r] ← f.certified [i] | throw "expected one certified graph plan"
  if r.qualification.isSome then throw "generic demo body"
  let b ← f.groupEvidence [i] evidence
  match hc : b.functions with
  | [] => throw "absent response"
  | c :: _ =>
    if h : checkRequests [r] b = true then
      return ⟨r, b, c, h, by simp [hc]⟩
    else throw "body certificate refused"

/-- The Boolean projection check is over exact frozen labels. -/
@[nospecialize] def projectionCheck [DecidableEq ι] (inputs frame : List (Ty ι))
    (slots : List Nat) : Bool :=
  decide (slots.length = inputs.length) && (inputs.zipIdx).all fun (A, k) =>
    match slots[k]? with
    | some j => decide (frame[j]? = some A)
    | none => false

theorem projectionCheck_sound [DecidableEq ι] {inputs frame : List (Ty ι)} {slots : List Nat}
    (h : projectionCheck inputs frame slots = true) :
    slots.length = inputs.length ∧ ∀ (k : Nat) (A : Ty ι), inputs[k]? = some A →
      ∃ j, slots[k]? = some j ∧ frame[j]? = some A := by
  simp only [projectionCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, ?_⟩
  intro k A hk
  have ha := h.2 (A,k) (List.mem_zipIdx_iff_getElem?.mpr hk)
  split at ha
  · rename_i j hj
    exact ⟨j, hj, of_decide_eq_true ha⟩
  · cases ha

/-- Check one offered row against the accepted top-level request. -/
def rowCheck {F} (r : Request F) (arity : Nat) (Cs : List (Ty (Label F)))
    (slots : List Nat) (p : CallEffects.Arrow (Ty (Label F))) : Bool :=
  decide (arity ≤ p.arguments.length ∧ r.result = p.result ∧ r.promise = none ∧
    r.entrySeparation.facts = [] ∧ r.qualification = none) &&
  projectionCheck r.inputs (codeFrame arity p Cs none) slots &&
  (decide (p.effect = .ordinary) ||
    decide (p.effect = { CallEffects.Effect.ofFootprint r.footprint with onThrow := r.onThrow } ∧
      (r.footprint ≠ .top ∨ r.onThrow = true)))

theorem rowCheck_sound {F} (a : AcceptedRequest F) {arity Cs slots p}
    (h : rowCheck a.request arity Cs slots p = true) :
    GraphCodeSpec F.equations.graph arity [invocationExpression a.request.toRequest slots]
      [(.ret, none)] 0 Cs p := by
  simp only [rowCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨arityOk, result, promise, sep, qual⟩, projection⟩ := h.1
  obtain ⟨length, types⟩ := projectionCheck_sound projection
  have separation : ∀ ρ, HeapSeparation.Holds a.request.entrySeparation ρ := by
    intro ρ; simp [HeapSeparation.Holds, sep]
  rcases h.2 with ordinary | ⟨effect, effectful⟩
  · have code := code_of_adapted_request a.accepted a.member F.equations.graph.env
      (show a.request.Admits F.equations.graph.env from by simp [SourceRequest.Admits, qual])
      arityOk ordinary result promise slots length types separation
    exact code p (by simp [offerRows])
  · have code := code_of_effectful_adapted_request a.accepted a.member F.equations.graph.env
      arityOk effect effectful result promise slots length types separation
    exact code p (by simp [offerRows])

structure Candidate (F : EquationStore.Frozen) where
  name : String
  accepted : AcceptedRequest F
  signature : Ty (Label F)
  arity : Nat
  captureTypes : List (Ty (Label F))
  dependencies : List String
  projection : List Nat
  arrows : List (CallEffects.Arrow (Ty (Label F)))
  rests : List (CallEffects.RestArrow (Ty (Label F)))

/-- Exact invocation code; only the capture values vary during assembly. -/
def Candidate.export {F} (c : Candidate F) (captures : List Tm) (identity : Nat) : Export (Label F) :=
  { graph := F.equations.graph, signature := c.signature, arity := c.arity
    expressions := [invocationExpression c.accepted.request.toRequest c.projection]
    continuations := [(.ret, none)], start := 0, captureTypes := c.captureTypes
    captures, fields := [], identity, kind := .call, arrows := c.arrows, rests := c.rests }

def Candidate.bodyCheck {F} (c : Candidate F) : Bool :=
  (offerRows c.arrows c.rests).all
    (rowCheck c.accepted.request c.arity (c.captureTypes ++ [c.signature]) c.projection)

theorem Candidate.bodyCheck_sound {F} {c : Candidate F} (h : c.bodyCheck = true)
    (captures : List Tm) (identity : Nat) :
    CodeOffers F.equations.graph (c.export captures identity).arity
      (c.export captures identity).expressions (c.export captures identity).continuations
      (c.export captures identity).start
      ((c.export captures identity).captureTypes ++ [(c.export captures identity).signature])
      false (c.export captures identity).arrows (c.export captures identity).rests [] := by
  intro p hp
  exact rowCheck_sound c.accepted ((List.all_eq_true.mp h) p hp)

/-- Evidence lines have the same strict shape as the unit verifier's input. -/
def evidenceFor (lines : List Json) (unit : String) : Except String Json := do
  let decoded ← lines.mapM readUnitLine
  let found :=  decoded.filter (·.1 == unit)
  match found with
  | [(_, evidence)] => return evidence
  | _ => throw s!"expected one evidence line for {unit}"

def retainedType (f : FilePlans) (name : String) (fixed : Bool) : Except String (Ty (Label f.F)) := do
  match f.signatures.filter (·.name == name) with
  | [s] => if fixed then s.fixed else s.type
  | _ => throw s!"expected one retained signature for {name}"

/-- Module captures use the extraction's ordered module-binding selection.
The frame projection is checked against the actual retained request inputs. -/
def candidates (f : FilePlans) (lines : List Json) : Except String (List (Candidate f.F)) := do
  if !f.p.modules.isEmpty then throw "demo has no qualified module runs"
  if !f.fr.moduleConstants.isEmpty || !f.fr.classSelves.isEmpty then
    throw "demo has only callable module bindings"
  let pairs ← (f.fr.units.zipIdx).mapM fun ((fn, tps, init), i) => do
    if !tps.isEmpty || init.isSome || fn.async || fn.params.any (fun p => p.rest || p.name == "this") then
      throw "demo requires fixed synchronous function units"
    let accepted ← acceptedRequest f i (← evidenceFor lines (f.fr.unitId i))
    let mentioned := fn.body.flatMap stmtNames
    let dependencies := (f.fr.moduleFunctions.filter fun g => mentioned.contains g.1 ||
      SourceTypes.prototypeNames.contains g.1 || g.1 == Fragment.throwUninitializedName).map (·.1)
    let arity := fn.params.length
    let captures := accepted.request.inputs.drop arity
    let projection := (List.range accepted.request.inputs.length).map (· + 1)
    let make (fixed : Bool) : Except String (Candidate f.F) := do
      let signature ← retainedType f fn.name fixed
      let [.arrs arrows rests] := expand f.F.equations.graph signature
        | throw s!"{fn.name}: retained signature is not callable"
      return {
        name := fn.name ++ (if fixed then "#public" else "")
        accepted, signature, arity, captureTypes := captures, dependencies, projection, arrows, rests }
    return [← make false, ← make true]
  return pairs.flatten

structure Built (F : EquationStore.Frozen) where
  candidate : Candidate F
  captures : List Tm
  identity : Nat
  rank : Nat
  slots : List (Option Nat)

def Built.export {F} (b : Built F) : Export (Label F) :=
  b.candidate.export b.captures b.identity

/-- Construct concrete closures in dependency order. Every captured value is
an earlier constructed closure; the assembly checker independently checks
its exact value, label and decreasing rank. -/
def build {F} : Nat → List (Candidate F) → List (Built F) → Except String (List (Built F))
  | 0, [], done => return done
  | 0, _ :: _, _ => throw "cyclic or external demo dependency"
  | fuel + 1, todo, done => do
    if todo.isEmpty then return done
    let some c := todo.find? (fun c => c.dependencies.all fun name =>
      done.any (·.candidate.name == name)) | throw "cyclic or external demo dependency"
    let targets ← c.dependencies.mapM fun name => do
      let some j := (List.range done.length).find? (fun j =>
        (done[j]?).any (·.candidate.name == name)) | throw "capture target absent"
      let some b := done[j]? | throw "capture index absent"
      return (j,b)
    let b : Built F := {
      candidate := c, captures := targets.map (·.2.export.value)
      identity := done.length, rank := 1 + (targets.map (·.2.rank)).foldl max 0
      slots := targets.map (some ∘ Prod.fst) }
    build fuel (todo.filter (·.name != c.name)) (done ++ [b])

def exports {F} (bs : List (Built F)) : Fin bs.length → Export (Label F) := fun i => bs[i].export

def assemblyData {F} (bs : List (Built F)) : Assembly.Data :=
  ⟨bs.map (·.rank), bs.map (·.slots)⟩

def assemblyCheck {F} (bs : List (Built F)) : Bool :=
  Assembly.check F.equations.graph (exports bs) (assemblyData bs)
    (fun i => bs[i].candidate.bodyCheck)

theorem assemblyCheck_sound {F} {bs : List (Built F)} (h : assemblyCheck bs = true) :
    Nonempty (WellLinked (Assembly.family F.equations.graph (exports bs))) := by
  apply Assembly.check_sound (h := h)
  intro i hi
  exact Candidate.bodyCheck_sound hi bs[i].captures bs[i].identity

structure CheckedAssembly (F : EquationStore.Frozen) where
  built : List (Built F)
  checked : assemblyCheck built = true

def assemble (f : FilePlans) (lines : List Json) : Except String (CheckedAssembly f.F) := do
  let cs ← candidates f lines
  if (cs.map (·.name)).eraseDups.length != cs.length then throw "duplicate assembly name"
  let bs ← build cs.length cs []
  if bs.length != cs.length then throw "incomplete assembly"
  if h : assemblyCheck bs = true then return ⟨bs,h⟩
  else throw "source-bound assembly refused"

theorem CheckedAssembly.linked {F} (a : CheckedAssembly F) :
    Nonempty (WellLinked (Assembly.family F.equations.graph (exports a.built))) :=
  assemblyCheck_sound a.checked

structure Link (R C : EquationStore.Frozen) (assembly : CheckedAssembly R) where
  target : Fin assembly.built.length
  required : Ty (Label C)
  exported : PrimitiveBoundary.Signature
  imported : PrimitiveBoundary.Signature
  exportChecked : PrimitiveBoundary.attachmentCheck R.equations.graph
    (exports assembly.built target).signature exported = true
  importChecked : PrimitiveBoundary.attachmentCheck C.equations.graph required imported = true
  compared : PrimitiveBoundary.compare exported imported = true

structure Entry (R C : EquationStore.Frozen) (assembly : CheckedAssembly R) where
  name : String
  accepted : AcceptedRequest C
  arguments : List (Ty (Label C))
  atoms : List PrimitiveBoundary.Atom
  argumentsChecked : PrimitiveBoundary.argumentsCheck C.equations.graph arguments atoms = true
  links : List (Link R C assembly)
  layout : accepted.request.inputs = arguments ++ links.map (·.required)
  separation : accepted.request.entrySeparation.facts = []
  unqualified : accepted.request.qualification = none

/-- Resolve the source import's declaration identity and attach both decoded
primitive signatures to the retained graph labels used by this link. -/
def link (rustAst callerAst : Json) {R C} (assembly : CheckedAssembly R)
    (caller : FilePlans) (same : caller.F = C) (localName : String) : Except String (Link R C assembly) := do
  let declarations ← callerAst.getObjVal? "declarations"
  let values ← declarations.getObjValAs? (Array Json) "values"
  let [value] := values.toList.filter (fun v =>
    (v.getObjValD "binding" |>.getObjValAs? String "local").toOption == some localName)
    | throw s!"expected one import for {localName}"
  if (← value.getObjValAs? Bool "construct") ||
      !(← value.getObjValAs? (Array Json) "typeParams").isEmpty then throw "generic or construct import"
  let declaration ← value.getObjVal? "declaration"
  if (← declaration.getObjValAs? String "module") != "./lib.d.ts" then throw "external demo import"
  let name ← declaration.getObjValAs? String "name"
  let some target := (List.finRange assembly.built.length).find? (fun i =>
    assembly.built[i].candidate.name == name ++ "#public") | throw "export target absent"
  let functions ← rustAst.getObjValAs? (Array Json) "functions"
  let [fn] := functions.toList.filter (fun j => (j.getObjValAs? String "name").toOption == some name)
    | throw "expected one source export"
  let exported ← PrimitiveBoundary.exportOf fn
  let imported ← PrimitiveBoundary.signatureOf (← value.getObjVal? "type")
  let required := same ▸ (← retainedType caller localName false)
  if he : PrimitiveBoundary.attachmentCheck R.equations.graph
      (exports assembly.built target).signature exported = true then
    if hi : PrimitiveBoundary.attachmentCheck C.equations.graph required imported = true then
      if hc : PrimitiveBoundary.compare exported imported = true then
        return ⟨target, required, exported, imported, he, hi, hc⟩
      else throw "primitive signatures disagree"
    else throw "import attachment refused"
  else throw "export attachment refused"

def entries (rustAst callerAst : Json) {R} (assembly : CheckedAssembly R)
    (caller : FilePlans) (lines : List Json) : Except String (List (Entry R caller.F assembly)) := do
  if !caller.p.modules.isEmpty || !caller.fr.moduleConstants.isEmpty ||
      !caller.fr.classSelves.isEmpty then throw "demo caller has external initialization"
  (caller.fr.units.zipIdx).mapM fun ((fn, tps, init), i) => do
    if !tps.isEmpty || init.isSome || fn.async || fn.params.any (fun p => p.rest || p.name == "this") then
      throw "demo caller requires fixed synchronous functions"
    let accepted ← acceptedRequest caller i (← evidenceFor lines (caller.fr.unitId i))
    let functions ← callerAst.getObjValAs? (Array Json) "functions"
    let some raw := functions.find? (fun j =>
      (j.getObjValAs? String "name").toOption == some fn.name) | throw "caller source function absent"
    let atoms ← (← raw.getObjValAs? (Array Json) "params").toList.mapM fun p =>
      PrimitiveBoundary.atomOf (p.getObjValD "type")
    let arguments := accepted.request.inputs.take fn.params.length
    let mentioned := fn.body.flatMap stmtNames
    let dependencies := (caller.fr.moduleFunctions.filter fun g => mentioned.contains g.1 ||
      SourceTypes.prototypeNames.contains g.1 || g.1 == Fragment.throwUninitializedName).map (·.1)
    let links ← dependencies.mapM (link rustAst callerAst assembly caller rfl)
    if ha : PrimitiveBoundary.argumentsCheck caller.F.equations.graph arguments atoms = true then
      if hl : accepted.request.inputs = arguments ++ links.map (·.required) then
        if hs : accepted.request.entrySeparation.facts = [] then
          if hq : accepted.request.qualification = none then
            return ⟨fn.name, accepted, arguments, atoms, ha, links, hl, hs, hq⟩
          else throw "qualified caller"
        else throw "entry separation outside primitive demo"
      else throw "caller import slots disagree with retained inputs"
    else throw "caller arguments outside primitive demo"

structure CheckedDemo where
  rust : FilePlans
  caller : FilePlans
  assembly : CheckedAssembly rust.F
  entries : List (Entry rust.F caller.F assembly)
  rustBuiltins : rust.F.equations.graph.builtins = none
  callerBuiltins : caller.F.equations.graph.builtins = none

/-- This is the complete pure decision used by `boundary-check`. It reads the
same Fragments, claims and evidence as unit acceptance and constructs all
closures and entry import slots from their retained results. -/
def check (rustAst rustClaims : Json) (rustEvidence : List Json)
    (callerAst callerClaims : Json) (callerEvidence : List Json) : Except String CheckedDemo := do
  let rust ← linkingFilePlans rustAst rustClaims (← rustAst.getObjValAs? String "file") {}
  let caller ← linkingFilePlans callerAst callerClaims (← callerAst.getObjValAs? String "file") {}
  let assembly ← assemble rust rustEvidence
  let es ← entries rustAst callerAst assembly caller callerEvidence
  if es.isEmpty || !(es.any fun e => !e.links.isEmpty) then throw "demo has no linked caller entry"
  if hr : rust.F.equations.graph.builtins = none then
    if hc : caller.F.equations.graph.builtins = none then
      return ⟨rust, caller, assembly, es, hr, hc⟩
    else throw "caller graph has array builtins"
  else throw "Rust graph has array builtins"

theorem Link.transport {R C} {assembly : CheckedAssembly R} (l : Link R C assembly)
    (exceptions : excOf R.equations.graph = excOf C.equations.graph) :
    ∀ n W v, meaning (exports assembly.built l.target).graph
      (exports assembly.built l.target).signature n W v ↔ meaning (ι := Label C) C.equations.graph l.required n W v := by
  intro n W v
  have he := PrimitiveBoundary.attachmentCheck_sound l.exportChecked
  have hi := PrimitiveBoundary.attachmentCheck_sound l.importChecked
  have hc : l.exported = l.imported := of_decide_eq_true l.compared
  constructor
  · exact PrimitiveBoundary.transport he hi l.compared exceptions
  · apply PrimitiveBoundary.transport hi he _ exceptions.symm
    simp [PrimitiveBoundary.compare, hc]

/-- Primitive entry arguments carry their usual mathematical data. This type
admits every value of the demo's public parameter types. -/
def AtomInput : PrimitiveBoundary.Atom → Type
  | .number => UInt64
  | .bigint => Int
  | .boolean => Bool
  | .string => String

def inputTerm : {a : PrimitiveBoundary.Atom} → AtomInput a → Tm
  | .number, v => .num v
  | .bigint, v => .bigint v
  | .boolean, true => .tru
  | .boolean, false => .fls
  | .string, v => .str v

inductive Inputs : List PrimitiveBoundary.Atom → Type where
  | nil : Inputs []
  | cons {a atoms} : AtomInput a → Inputs atoms → Inputs (a :: atoms)

def Inputs.values : {atoms : List PrimitiveBoundary.Atom} → Inputs atoms → List Tm
  | _, .nil => []
  | _, .cons v rest => inputTerm v :: rest.values

theorem inputTerm_typed {a} (v : AtomInput a) : ∀ n W, a.meaning n W (inputTerm v) := by
  intro n W
  cases a with
  | number => exact ⟨v,rfl⟩
  | bigint => exact ⟨v,rfl⟩
  | string => exact ⟨v,rfl⟩
  | boolean => cases v <;> simp [inputTerm, PrimitiveBoundary.Atom.meaning, boolT]

theorem Inputs.length {atoms} (xs : Inputs atoms) : xs.values.length = atoms.length := by
  induction xs <;> simp_all [values]

theorem Inputs.typed {atoms} (xs : Inputs atoms) : ∀ (k : Nat) (a : PrimitiveBoundary.Atom), atoms[k]? = some a →
    ∀ n W, a.meaning n W (envOf xs.values .nul k) := by
  induction xs with
  | nil => intro k a h; simp at h
  | @cons a atoms v rest ih =>
    intro k b h n W
    cases k with
    | zero =>
      have : a = b := by simpa using h
      subst b
      exact inputTerm_typed v n W
    | succ k => exact ih k b (by simpa using h) n W

theorem Inputs.closed {atoms} (xs : Inputs atoms) : ∀ k, Scoped 0 (envOf xs.values .nul k) := by
  induction xs with
  | nil => intro k; simp [values, envOf, List.getD, Scoped]
  | @cons a atoms v rest ih =>
    intro k
    cases k with
    | zero => cases a <;> simp [values, envOf, List.getD, inputTerm, Scoped]; cases v <;> trivial
    | succ k => exact ih k

theorem atom_ne_export {a : PrimitiveBoundary.Atom} {v n W} (h : a.meaning n W v)
    (e : Export ι) : v ≠ e.value := by
  intro eq
  subst v
  cases a <;> simp [PrimitiveBoundary.Atom.meaning, numT, bigintT, strT, boolT, Export.value] at h

/-- The entry environment contains the written primitive arguments followed
by the constructed export values at their exact checked request slots. -/
def Entry.environment {R C assembly} (e : Entry R C assembly) (xs : Inputs e.atoms) : Env :=
  envOf (xs.values ++ e.links.map (fun l => (exports assembly.built l.target).value)) .nul

theorem Entry.argument_meaning {R C assembly} (e : Entry R C assembly) (xs : Inputs e.atoms)
    {k : Nat} {A : Ty (Label C)} (hA : e.arguments[k]? = some A) :
    ∀ n W, meaning (ι := Label C) C.equations.graph A n W (envOf xs.values .nul k) := by
  have hm := PrimitiveBoundary.argumentsCheck_sound (ι := Label C) e.argumentsChecked
  have ht : (e.atoms.map PrimitiveBoundary.Atom.meaning)[k]? =
      some (meaning (ι := Label C) C.equations.graph A) := by
    rw [← hm, List.getElem?_map, hA]; rfl
  rw [List.getElem?_map] at ht
  obtain ⟨a, ha, eq⟩ := Option.map_eq_some_iff.mp ht
  rw [← eq]
  exact xs.typed k a ha

theorem Entry.slots {R C assembly} (e : Entry R C assembly) (xs : Inputs e.atoms)
    (exceptions : excOf R.equations.graph = excOf C.equations.graph) :
    ∀ (k : Nat) (A : Ty (Label C)), e.accepted.request.inputs[k]? = some A →
      ((∀ j, e.environment xs k ≠ (Assembly.family R.equations.graph (exports assembly.built) j).value) ∧
        ∀ n W, meaning (ι := Label C) C.equations.graph A n W (e.environment xs k)) ∨
      ∃ j, e.environment xs k = (Assembly.family R.equations.graph (exports assembly.built) j).value ∧
        ∀ n W v, meaning (Assembly.family R.equations.graph (exports assembly.built) j).graph
          (Assembly.family R.equations.graph (exports assembly.built) j).signature n W v ↔
            meaning (ι := Label C) C.equations.graph A n W v := by
  intro k A hA
  have lengths : xs.values.length = e.arguments.length :=
    xs.length.trans (by
      simpa only [List.length_map] using (congrArg List.length
        (PrimitiveBoundary.argumentsCheck_sound (ι := Label C) e.argumentsChecked).symm))
  rw [e.layout] at hA
  by_cases hk : k < e.arguments.length
  · have ha : e.arguments[k]? = some A := by
      rw [List.getElem?_append_left hk] at hA
      exact hA
    have env : e.environment xs k = envOf xs.values .nul k := by
      simp [environment, envOf, List.getD, List.getElem?_append, lengths, hk]
    left
    refine ⟨?_, fun n W => env ▸ e.argument_meaning xs ha n W⟩
    intro j
    rw [env]
    have hm := PrimitiveBoundary.argumentsCheck_sound (ι := Label C) e.argumentsChecked
    have ht : (e.atoms.map PrimitiveBoundary.Atom.meaning)[k]? = some (meaning (ι := Label C) C.equations.graph A) := by
      rw [← hm, List.getElem?_map, ha]; rfl
    rw [List.getElem?_map] at ht
    obtain ⟨a, hat, _⟩ := Option.map_eq_some_iff.mp ht
    exact atom_ne_export (xs.typed k a hat 0 (by rw [WorldT_eq]; exact [])) _
  · have ha : (e.links.map (·.required))[k - e.arguments.length]? = some A := by
      rw [List.getElem?_append_right (Nat.le_of_not_gt hk)] at hA
      exact hA
    rw [List.getElem?_map] at ha
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp ha
    right
    refine ⟨l.target, ?_, l.transport exceptions⟩
    simp [environment, envOf, List.getD, List.getElem?_append, lengths, hk,
      List.getElem?_map, hl, Assembly.family, Export.value]

theorem Entry.closed {R C assembly} (e : Entry R C assembly) (xs : Inputs e.atoms)
    (linked : WellLinked (Assembly.family R.equations.graph (exports assembly.built))) :
    ∀ k, Scoped 0 (e.environment xs k) := by
  intro k
  unfold environment envOf
  simp only [List.getD]
  cases hv : (xs.values ++ e.links.map (fun l => (exports assembly.built l.target).value))[k]? with
  | none => trivial
  | some v =>
    have mem := List.mem_of_getElem? hv
    rcases List.mem_append.mp mem with arg | linkedValue
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp arg
      have hc := xs.closed j
      simpa [envOf, List.getD, hj] using hc
    · obtain ⟨l, _, rfl⟩ := List.mem_map.mp linkedValue
      exact (scopedArgs_iff 0 _).mpr (linked.closed l.target)

/-- Six decoded artifact inputs. Evidence uses the unit verifier's JSON lines. -/
structure Input where
  rustAst : Json
  rustClaims : Json
  rustEvidence : List Json
  callerAst : Json
  callerClaims : Json
  callerEvidence : List Json

def Input.run (i : Input) : Except String CheckedDemo :=
  check i.rustAst i.rustClaims i.rustEvidence i.callerAst i.callerClaims i.callerEvidence

/-- Exactly the successful branch of the boundary executable. -/
def Input.accepted (i : Input) : Bool := i.run.isOk

def Input.result (i : Input) (success : i.accepted = true) : CheckedDemo :=
  match h : i.run with
  | .ok d => d
  | .error _ => by simp [Input.accepted, h, Except.isOk, Except.toBool] at success

open LinkedRuntime

/-- A runtime simulation and its related initial state. All implementation
assumptions are the five simulations; this record adds only their initial
state relation. -/
structure Started (model runtime : Machine) (n : Nat) (initial : model.State n) where
  simulation : Simulation model runtime
  state : runtime.State n
  related : simulation.related n initial state

def Entry.model {R C assembly} (e : Entry R C assembly) (xs : Inputs e.atoms) : Machine :=
  graphMachine (excOf C.equations.graph) e.accepted.request.program
    (GoalHolds C.equations.graph e.accepted.request.goal
      (e.accepted.request.goal.argument (e.environment xs)))

def Entry.initial {R C assembly} (e : Entry R C assembly) (xs : Inputs e.atoms) (n : Nat) :
    (e.model xs).State n :=
  ⟨ofList [], [], .at e.accepted.request.start (e.environment xs)⟩

/-- **The demo's CLI-to-runtime theorem.** `success` is exactly the Boolean
condition selecting exit zero in `boundary-check`. The computed result
supplies accepted caller code, a source-bound concrete `WellLinked` family,
primitive attachments, signature transport, exact entry slots, admissibility
and separation. Entry arguments range over every written primitive value;
execution starts in the empty admitted world and heap after initialization.

The five named, started simulations are TypeScript lowering, Rust translation
and arithmetic/adapters, rustc, wasm-bindgen including exceptional adapter
state, and engine/loading/artifact provenance. No model premise is a runtime
simulation field. Scope: ordinary primitive entries, acyclic callable imports,
completed initialization, stable exports, no live-binding writes or re-exports.
-/
theorem linked_safe (input : Input) (success : input.accepted = true)
    (j : Fin (input.result success).entries.length)
    (xs : Inputs ((input.result success).entries[j]).atoms) (n : Nat)
    {ts rust wasm glue deployed : Machine}
    (typescriptLowering : Started (((input.result success).entries[j]).model xs) ts n
      (((input.result success).entries[j]).initial xs n))
    (rustTranslation : Started ts rust n typescriptLowering.state)
    (rustc : Started rust wasm n rustTranslation.state)
    (wasmBindgen : Started wasm glue n rustc.state)
    (engine : Started glue deployed n wasmBindgen.state) :
    deployed.Safe n engine.state := by
  let d := input.result success
  let e := d.entries[j]
  obtain ⟨linked⟩ := d.assembly.linked
  have exceptions := PrimitiveBoundary.exceptions_eq_of_no_builtins d.rustBuiltins d.callerBuiltins
  have admitted : e.accepted.request.Admits d.caller.F.equations.graph.env := by
    simp [SourceRequest.Admits, e.unqualified]
  have separation : HeapSeparation.Holds e.accepted.request.entrySeparation (e.environment xs) := by
    simp [HeapSeparation.Holds, e.separation]
  have world : WorldAdm (ofList ([] : List (Ctr n))) := by
    simp [WorldAdm, lookup]
  have heap : HeapOk n (ofList ([] : List (Ctr n))) [] := by
    simp [HeapOk, lookup]
  exact LinkedRuntime.end_to_end linked (requestsSafe_of_check e.accepted.accepted)
    e.accepted.member admitted (e.closed xs linked) (e.slots xs exceptions) separation world heap
    typescriptLowering.simulation rustTranslation.simulation rustc.simulation
    wasmBindgen.simulation engine.simulation typescriptLowering.related
    rustTranslation.related rustc.related wasmBindgen.related engine.related

end Verification.Demo
