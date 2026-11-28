import Verification.Source.SliceWire
import Verification.Source.FlowJson
-- FlowJson.lean supplies the execution graphs `--lower-control-flow` prints.
import Verification.Source.Claims.Json
-- Claims/ModuleInterfaces.lean computes and reads the module interfaces of mode 8.
import Verification.Source.Claims.ModuleInterfaces
import Verification.Source.WorkerWire

/-! File interface to the source adapter. Source parsing remains external;
the single pass computes each unit's types from the fragment alone. -/
namespace Verification.RequestCli
open Lean RequestJson

/-- A refusal record: its reason after `reject: `, then the line that ends
it, so a reader can tell a complete record from one cut short. Its exit
status is 1; an operational failure is the command's other exit (`main`). -/
def refuse (reason : String) : IO UInt32 := do
  IO.eprintln s!"reject: {reason}"
  IO.eprintln "end of refusal"
  return 1

/-- A hexadecimal digit's value. -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Four hexadecimal digits' value. -/
def hex4 (cs : List Char) : Option Nat :=
  cs.foldlM (fun v c => (hexDigit c).map (v * 16 + ·)) 0

/-- A lone surrogate escape of a JSON text's strings, if it has one. Every
wire string is well-formed Unicode (HOST-FAMILIES.md, "Tag sets"): Lean's
JSON parser reads a lone surrogate as U+FFFD, a different string, so a text
holding one is refused before it is parsed, as is a text that is not valid
UTF-8. -/
def loneSurrogate (cs : List Char) (inString : Bool := false) : Option String :=
  match cs, inString with
  | [], _ => none
  | '"' :: rest, b => loneSurrogate rest !b
  | '\\' :: 'u' :: a :: b :: c :: d :: rest, true =>
    match hex4 [a, b, c, d] with
    | some u =>
      if 0xD800 ≤ u ∧ u ≤ 0xDBFF then
        match rest with
        | '\\' :: 'u' :: e :: f :: g :: h :: more =>
          match hex4 [e, f, g, h] with
          | some v => if 0xDC00 ≤ v ∧ v ≤ 0xDFFF then loneSurrogate more true else some "a lone high surrogate"
          | none => some "a lone high surrogate"
        | _ => some "a lone high surrogate"
      else if 0xDC00 ≤ u ∧ u ≤ 0xDFFF then some "a lone low surrogate"
      else loneSurrogate rest true
    | none => loneSurrogate rest true
  | '\\' :: _ :: rest, true => loneSurrogate rest true
  | _ :: rest, b => loneSurrogate rest b

theorem charLe {a c : Char} : a ≤ c ↔ a.toNat ≤ c.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

theorem char_eq_of_toNat {c d : Char} (h : c.toNat = d.toNat) : c = d :=
  Char.ext (UInt32.toNat_inj.mp h)

theorem hexDigit_lt {c : Char} {v : Nat} (h : hexDigit c = some v) : v < 16 := by
  unfold hexDigit at h
  simp only [charLe] at h
  have h0 : '0'.toNat = 48 := rfl
  have h9 : '9'.toNat = 57 := rfl
  have ha : 'a'.toNat = 97 := rfl
  have hf : 'f'.toNat = 102 := rfl
  have hA : 'A'.toNat = 65 := rfl
  have hF : 'F'.toNat = 70 := rfl
  split at h
  · simp only [Option.some.injEq] at h; omega
  · split at h
    · simp only [Option.some.injEq] at h; omega
    · split at h
      · simp only [Option.some.injEq] at h; omega
      · cases h

theorem hexDigit_d {c : Char} (h : hexDigit c = some 13) : c = 'd' ∨ c = 'D' := by
  unfold hexDigit at h
  simp only [charLe] at h
  have h0 : '0'.toNat = 48 := rfl
  have h9 : '9'.toNat = 57 := rfl
  have ha : 'a'.toNat = 97 := rfl
  have hf : 'f'.toNat = 102 := rfl
  have hA : 'A'.toNat = 65 := rfl
  have hF : 'F'.toNat = 70 := rfl
  have hd : 'd'.toNat = 100 := rfl
  have hD : 'D'.toNat = 68 := rfl
  split at h
  · simp only [Option.some.injEq] at h; omega
  · split at h
    · simp only [Option.some.injEq] at h; left; apply char_eq_of_toNat; omega
    · split at h
      · simp only [Option.some.injEq] at h; right; apply char_eq_of_toNat; omega
      · cases h

theorem hex4_surrogate {a b c d : Char} {u : Nat} (h : hex4 [a, b, c, d] = some u)
    (lo : 0xD800 ≤ u) (hi : u ≤ 0xDFFF) : a = 'd' ∨ a = 'D' := by
  simp only [hex4, List.foldlM_cons, List.foldlM_nil] at h
  cases ha : hexDigit a <;> simp [ha] at h
  rename_i da
  cases hb : hexDigit b <;> simp [hb] at h
  rename_i db
  cases hc : hexDigit c <;> simp [hc] at h
  rename_i dc
  cases hd : hexDigit d <;> simp [hd] at h
  rename_i dd
  have := hexDigit_lt ha; have := hexDigit_lt hb; have := hexDigit_lt hc; have := hexDigit_lt hd
  have h13 : da = 13 := by omega
  subst h13
  exact hexDigit_d ha

/-- A backslash, `u` and `d` or `D` in a row: how every surrogate escape starts. -/
def SurrogateStart (cs : List Char) : Prop :=
  ∃ pre x post, cs = pre ++ '\\' :: 'u' :: x :: post ∧ (x = 'd' ∨ x = 'D')

theorem SurrogateStart.cons {c : Char} {cs : List Char} (h : SurrogateStart cs) : SurrogateStart (c :: cs) := by
  obtain ⟨pre, x, post, rfl, hx⟩ := h
  exact ⟨c :: pre, x, post, rfl, hx⟩

theorem SurrogateStart.here {x : Char} {post : List Char} (hx : x = 'd' ∨ x = 'D') :
    SurrogateStart ('\\' :: 'u' :: x :: post) := ⟨[], x, post, rfl, hx⟩

theorem loneSurrogate_start {cs : List Char} {b : Bool} {w : String}
    (h : loneSurrogate cs b = some w) : SurrogateStart cs := by
  fun_induction loneSurrogate cs b <;>
    first
    | (simp at h; done)
    | exact SurrogateStart.here (hex4_surrogate (by assumption) (by omega) (by omega))
    | ((repeat apply SurrogateStart.cons); solve_by_elim)


/-- Whether byte `i` is `v`. -/
def byteIs (b : ByteArray) (i : Nat) (v : UInt8) : Bool :=
  if h : i < b.size then b[i] == v else false

/-- A backslash, `u` and `d` or `D` at byte `i`. -/
def surrogateEscapeAt (b : ByteArray) (i : Nat) : Bool :=
  byteIs b i 92 && byteIs b (i + 1) 117 && (byteIs b (i + 2) 100 || byteIs b (i + 2) 68)

/-- Whether such a run starts at byte `i` or after it. -/
def surrogateEscapeFrom (b : ByteArray) (i : Nat) : Bool :=
  if i < b.size then surrogateEscapeAt b i || surrogateEscapeFrom b (i + 1) else false
termination_by b.size - i

theorem surrogateEscapeFrom_of_at {b : ByteArray} {i j : Nat} (hij : i ≤ j)
    (h : surrogateEscapeAt b j = true) : surrogateEscapeFrom b i = true := by
  have hj : j < b.size := by
    by_cases hj : j < b.size
    · exact hj
    · simp [surrogateEscapeAt, byteIs, hj] at h
  induction i using surrogateEscapeFrom.induct b with
  | case1 i hi ih =>
    rw [surrogateEscapeFrom]; simp only [hi, ite_true, Bool.or_eq_true]
    rcases Nat.lt_or_eq_of_le hij with hlt | heq
    · exact Or.inr (ih (by omega))
    · subst heq; exact Or.inl h
  | case2 i hi => omega

theorem byteIs_mk {l : List UInt8} {i : Nat} {v : UInt8} :
    byteIs ⟨⟨l⟩⟩ i v = (l[i]? == some v) := by
  unfold byteIs
  by_cases hi : i < l.length
  · have hs : i < (⟨⟨l⟩⟩ : ByteArray).size := hi
    have hg : (⟨⟨l⟩⟩ : ByteArray)[i] = l[i] := rfl
    simp [hs, hg, hi]
  · have hs : ¬ i < (⟨⟨l⟩⟩ : ByteArray).size := hi
    simp [hs, hi]

theorem start_bytes {cs : List Char} (h : SurrogateStart cs) :
    ∃ j, surrogateEscapeAt cs.utf8Encode j = true := by
  obtain ⟨pre, x, post, rfl, hx⟩ := h
  refine ⟨(pre.flatMap String.utf8EncodeChar).length, ?_⟩
  have hb : String.utf8EncodeChar '\\' = [92] := rfl
  have hu : String.utf8EncodeChar 'u' = [117] := rfl
  simp only [surrogateEscapeAt, List.utf8Encode, byteIs_mk]
  rcases hx with rfl | rfl
  · have hd : String.utf8EncodeChar 'd' = [100] := rfl
    simp [List.flatMap_append, hb, hu, hd]
  · have hd : String.utf8EncodeChar 'D' = [68] := rfl
    simp [List.flatMap_append, hb, hu, hd]

/-- A text's lone surrogate escape, `loneSurrogate`'s, looked for only where
the text's bytes hold the start of a surrogate escape: one pass over the
bytes, without the text's list of characters (`wireSurrogate_eq`). -/
def wireSurrogate (text : String) : Option String :=
  if surrogateEscapeFrom text.toByteArray 0 then loneSurrogate text.toList else none

theorem wireSurrogate_eq (text : String) : wireSurrogate text = loneSurrogate text.toList := by
  unfold wireSurrogate
  split
  · rfl
  · rename_i hno
    cases h : loneSurrogate text.toList with
    | none => rfl
    | some w =>
      exfalso
      obtain ⟨j, hj⟩ := start_bytes (loneSurrogate_start h)
      rw [String.utf8Encode_toList] at hj
      exact hno (surrogateEscapeFrom_of_at (Nat.zero_le j) hj)

/-- A document's JSON, or its refusal. A file that cannot be read is no
refusal of a document: its error is thrown, and the command fails without a
`reject:` line. -/
def readJson (path : String) : IO (Except String Json) := do
  let bytes ← IO.FS.readBinFile path
  let some text := String.fromUTF8? bytes
    | return .error s!"{path}: a text that is not valid UTF-8 is refused"
  if let some what := wireSurrogate text then
    return .error s!"{path}: a string that is not well-formed Unicode, {what}, is refused"
  return EffectCodec.parseDocument text

/-- Export the same execution graph constructor used by lowering. -/
def flowFile (astPath : String) : IO UInt32 := do
  let ast ← readJson astPath
  match ast >>= SourceFlow.document with
  | .ok graph => match EffectCodec.document graph with
    | .ok j => IO.println j.compress; return 0
    | .error e => refuse e
  | .error reason => refuse reason

/-- The work table, where profiling (`TSCERT_PROFILE`), written to
`work.jsonl` in the working directory, a stage's output
(docs/drafts/on-demand-processing.md, "Accounting"): one line per kind and
item, `{"kind","item","count","ns","selfNs"}`, and a line of kind `process`
with the nanoseconds since `start`. -/
def writeWork (start : Nat) (path : String := "work.jsonl") : IO Unit := do
  if !(← SinglePass.profiling.get) then return
  let t ← IO.monoNanosNow
  let m ← SinglePass.workTable.get
  let rows := m.toList.mergeSort fun a b => a.1.1 < b.1.1 || (a.1.1 == b.1.1 && a.1.2 ≤ b.1.2)
  let lines := rows.map fun ((k, i), (c, n, own)) =>
    (Json.mkObj [("kind", toJson k), ("item", toJson i), ("count", toJson c), ("ns", toJson n),
      ("selfNs", toJson own)]).compress
  let total := (Json.mkObj [("kind", toJson "process"), ("item", toJson ""), ("count", toJson 1),
    ("ns", toJson (t - start)), ("selfNs", toJson (t - start))]).compress
  IO.FS.writeFile path (String.intercalate "\n" (lines ++ [total]) ++ "\n")

/-- A selection of units by their members' names, comma-separated; every
unit without one. -/
def selection : Option String → Option (List String)
  | none => none
  | some names => some ((names.splitOn ",").filter (· != ""))

/-- **The units a selection's processing needs**, by the names a selection
names them by (a function's name, `:init`): the named ones and every unit
their code reaches by name, closed, as the front's edges reach them
(`Front.edgesOf`), read off the fragment: a function by its name, the
initialization by a name its statements bind, a class's self binding or a
generic class. A unit of the selection's verdict closure lacking here is
missing a verdict, and the runner leaves the units depending on it open. -/
def selectionClosure (ast : Json) (roots : List String) : List String := Id.run do
  let fns := ((ast.getObjValAs? (Array Json) "functions").toOption.getD #[]).toList.filterMap fun j =>
    (Fragment.decodeFn j).toOption.map (·.1)
  let init := (Fragment.decodeInit ast).toOption.getD []
  let bound := init.flatMap Fragment.Stmt.bound
  let owned := bound ++ bound.map Fragment.selfBindingOf ++
    SourceClaimJson.genericClassNames ((ast.getObjVal? "init").toOption.getD (.arr #[]))
  let edges := fns.foldl (fun (m : Std.HashMap String (List String)) f =>
    m.insert f.name ((f.body.flatMap SourceElaboration.stmtNames) ++ m.getD f.name [])) {}
  let known := edges.insert ":init" (init.flatMap SourceElaboration.stmtNames)
  let bindings := Std.HashSet.ofList owned
  let mut pending := roots
  let mut seen := Std.HashSet.ofList roots
  for _ in [:roots.length + known.size] do
    let some name := pending.head? | break
    pending := pending.tail
    for n in known.getD name [] do
      for dep in ((if edges.contains n then [n] else []) ++
          (if !init.isEmpty && bindings.contains n then [":init"] else [])) do
        unless seen.contains dep do
          seen := seen.insert dep
          pending := dep :: pending
  return seen.toList

/-- The given lines of a module's units, by their identity in the module:
each line of a unit `module:<location>#<unit>`. -/
def forModule (location : String) («given» : Std.HashMap String Json) : Std.HashMap String Json :=
  let pre := s!"module:{location}#"
  given.fold (init := {}) fun m k v => if k.startsWith pre then m.insert (k.drop pre.length).toString v else m

/-- A module's given lines a pass reads (`FilePlans.passGroup`): those stating
a graph, by the unit's identity in the module whose document is `ast`. -/
def moduleGiven (ast : Json) («given» : Std.HashMap String Json) : Std.HashMap String Json :=
  let location := (ast.getObjValAs? String "file").toOption.getD ""
  (forModule location given).fold (init := {}) fun m k v => if (v.getObjVal? "graph").isOk then m.insert k v else m

/-- Discovery binds both the fragment and its requested roots. -/
def interfacePlanFile (path selection : String) : IO UInt32 := do
  let ast := (← readJson path) >>= fun a => do
    Fragment.symbolNumbersApart [a]
    Fragment.canonicalSymbols a
  let selected ← readJson selection
  match (do SourceClaimJson.interfacePlan (← ast) (← selected)) with
  | .error e => refuse e
  | .ok j => match EffectCodec.document j with
    | .ok j => IO.println j.compress; return 0
    | .error e => refuse e

/-- A complete canonical component check. All semantic inputs are in its
request; no environment-supplied stand-ins or evidence enter this check. -/
def interfaceFile (path : String) (budget : PositiveCertificates.SearchBudget) : IO UInt32 := do
  let request ← readJson path
  let parsed : Except String Json := do
    let j ← request
    fieldsExactly j ["modules", "names", "dependencies", "force", "fuel", "mode"]
    -- Every symbol key at its canonical number (`Fragment.canonicalSymbols`):
    -- the members' documents, and the dependencies', which their own
    -- components' checks wrote so.
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
    -- No module unit is given a line: every loop head's proposal is
    -- inferred (`HeadInference`).
    let given : Std.HashMap String Json := {}
    let force : List String ← fromJson? (← jField j "force")
    let fuel ← j.getObjValAs? Nat "fuel"
    let mode ← j.getObjValAs? Nat "mode"
    if mode != 8 then throw "interface mode must be 8"
    let infer := true
    let prepare := fun location (f : SourceClaimJson.FilePlans) =>
      SinglePass.work "prepare: head facts" (SourceClaimJson.fileItem f.fr.ast) fun _ =>
      f.withHeadFacts (forModule location given) false (inferred := infer)
    let check := fun (f : SourceClaimJson.FilePlans) group =>
      SinglePass.work "check: group" (f.fr.workItem (group.headD 0)) fun _ =>
      -- The given lines inference computes and the region separations, as
      -- for the file's own units (`passGroupMode8`).
      let r := f.passGroupMode8 infer force (fun _ => []) fuel group (given := some (moduleGiven f.fr.ast given))
      (r.1, r.2.1)
    let (est, _, _, tables) ← SourceClaimJson.establishModules
      (own.mergeSort (fun a b => a.module.location ≤ b.module.location)) budget force incoming prepare check incomingTables
    SourceClaimJson.encodeInterfaces modules est tables
  match parsed with
  | .error e => refuse e
  | .ok j => match EffectCodec.document j with
    | .ok j => IO.println j.compress; return 0
    | .error e => refuse e

abbrev GroupAnswers := List (String × Option SourceClaimJson.StandIn)

structure GroupVerdict where
  line : String
  refusal : Option String
  diagnostics : List String

/-- A group's plan or planning refusal, together with precisely the answers
its callers receive in either case. -/
structure PlannedGroup where
  planned : Except String SourceClaimJson.FilePlans
  answers : GroupAnswers
  verdict : Bool → GroupVerdict

/-- The immutable file inputs of a group's planning and verdict. -/
structure GroupContext where
  ast : Json
  fileKey : String
  budget : PositiveCertificates.SearchBudget
  est : SourceClaimJson.Established
  tables : List (String × SourceClaimJson.RowTable)
  force : List String
  front : Json × SourceClaimJson.Front
  givenLines : Std.HashMap String Json
  fuel : Nat

  printFailure : SourceClaimJson.PassDiagnostic → String := SourceClaimJson.PassDiagnostic.render

/-- The prepared file's front: its units, their identities and groups. -/
def GroupContext.fr (p : GroupContext) : SourceClaimJson.Front := p.front.2

/-- Named empty answers suppress inference for these members. -/
def GroupContext.emptyAnswers (p : GroupContext) (i : Nat) : GroupAnswers :=
  (p.fr.group i).filterMap fun j => match p.fr.units[j]? with
    | some (f, _, none) => some (f.name, none)
    | _ => none

/-- The group's ordinary verdict and reporting lines, including a planning
refusal. Counting controls the pass diagnostics printed alongside the verdict. -/
def GroupContext.groupVerdict (p : GroupContext) (i : Nat) (planned : Except String SourceClaimJson.FilePlans)
    (counting : Bool) : GroupVerdict :=
  let unit := p.fr.unitId i
  let members := (p.fr.group i).map p.fr.unitId
  match planned with
  | .error reason => ⟨WorkerWire.verdictLine unit members (.error reason) (some reason) [], some reason, []⟩
  | .ok f =>
    let (lines, verdict, dropped, runs) := SinglePass.work "check: group" (f.fr.workItem i) fun _ =>
      f.passGroupMode8 true p.force (f.givenAt p.givenLines) p.fuel (f.fr.group i) (counting := counting) (located := true) (print := p.printFailure)
    let diagnostics := lines ++ (if dropped > 0 then [s!"inferred heads: {dropped} proposals dropped, {runs} runs"] else [])
    let line := WorkerWire.verdictLine unit members verdict (f.elaborationRefusal (some [SourceClaimJson.memberName unit]))
      (f.contractReads (p.fr.group i))
    ⟨line, match verdict with | .ok _ => none | .error reason => some reason, diagnostics⟩

/-- One group operation. The verdict uses the very plan that produced its
answers, and is evaluated only if the group is requested for checking. -/
def GroupContext.groupOperation (p : GroupContext) (i : Nat) (demand : Bool) (below : GroupAnswers)
    (inputs : Except String (SourceClaimJson.GroupImports × SourceClaimJson.PlanningFront p.force)) :
    PlannedGroup × Option (SourceClaimJson.PlanningFront p.force) :=
  let result := do
    let (imports, front) ← inputs
    let names := some [SourceClaimJson.memberName (p.fr.unitId i)]
    let known := if demand then below else below ++ p.emptyAnswers i
    let (f, updated) ← SinglePass.work "prepare: unit plans" (p.fr.workItem i) fun _ =>
      imports.plan p.ast p.fileKey p.budget names {} p.force p.est p.tables (some front) known
    let f := SinglePass.work "prepare: head facts" (p.fr.workItem i) fun _ =>
      f.withHeadFacts p.givenLines false (inferred := true)
    return (if p.force.contains "start-facts" then f.withFalseStartFact else f, updated)
  let planned := result.map Prod.fst
  let answers := match planned with
    | .ok f => f.groupProposals i
    | .error _ => p.emptyAnswers i
  (⟨planned, answers, p.groupVerdict i planned⟩, result.toOption.bind Prod.snd)

/-- At the file's import answers and supplied planning front, the ordinary
plan, named answers and verdict agree with the interface planner and group check.
The front may contain answers from earlier groups of this worker. -/
theorem GroupContext.groupOperation_eq (p : GroupContext) (i : Nat)
    (demand : Bool) (below : GroupAnswers) (front : SourceClaimJson.PlanningFront p.force) :
    let names := some [SourceClaimJson.memberName (p.fr.unitId i)]
    let reads := SourceClaimJson.groupImports (SourceClaimJson.planImports p.ast) p.ast names {} p.est
    let known := if demand then below else below ++ p.emptyAnswers i
    let planned := (SourceClaimJson.fragmentPlansFromInterfaces p.ast p.fileKey p.budget names {} p.force p.est
        p.tables (some front) known).map fun f =>
          let f := f.withHeadFacts p.givenLines false (inferred := true)
          if p.force.contains "start-facts" then f.withFalseStartFact else f
    let answers := match planned with
      | .ok f => f.groupProposals i
      | .error _ => p.emptyAnswers i
    (p.groupOperation i demand below (reads.map (·, front))).1 =
      ⟨planned, answers, p.groupVerdict i planned⟩ := by
  dsimp only
  unfold groupOperation SourceClaimJson.fragmentPlansFromInterfaces
  cases h : SourceClaimJson.groupImports (SourceClaimJson.planImports p.ast) p.ast
    (some [SourceClaimJson.memberName (p.fr.unitId i)]) {} p.est with
  | error => rfl
  | ok imports =>
    dsimp [SinglePass.work, Except.map, Functor.map, Except.bind, Bind.bind]
    cases imports.plan p.ast p.fileKey p.budget (some [SourceClaimJson.memberName (p.fr.unitId i)]) {}
      p.force p.est p.tables (some front) (if demand then below else below ++ p.emptyAnswers i) <;> rfl

/-- The two premises of the group safety theorem at the inputs of a check. -/
def CheckedGroup (ast : Json) (key : String) (budget : PositiveCertificates.SearchBudget)
    (force : List String) (est : SourceClaimJson.Established) (tables : List (String × SourceClaimJson.RowTable))
    (imports : SourceClaimJson.GroupImports) (i fuel : Nat) (lines : Std.HashMap String Json)
    (counting : Bool) : Prop :=
  ∃ names front known f₀ updated deps,
    imports.plan ast key budget names {} force est tables (some front) known = .ok (f₀, updated) ∧
    (let f := SourceClaimJson.PassUnit.preparedMode8 force lines true f₀
     (f.passGroupMode8 true force (f.givenAt lines) fuel (f.fr.group i)
       (counting := counting) (located := true)).2.1) = .ok deps

private theorem groupVerdict_checked (p : GroupContext) (i : Nat) (f : SourceClaimJson.FilePlans)
    (counting : Bool) (h : (p.groupVerdict i (.ok f) counting).refusal = none) :
    ∃ deps, (f.passGroupMode8 true p.force (f.givenAt p.givenLines) p.fuel (f.fr.group i)
      (counting := counting) (located := true)).2.1 = .ok deps := by
  let printed := (f.passGroupMode8 true p.force (f.givenAt p.givenLines) p.fuel (f.fr.group i)
      (counting := counting) (located := true) (print := p.printFailure)).2.1
  change (match printed with | .ok _ => none | .error why => some why) = none at h
  have same := f.passGroupMode8_print p.force (f.givenAt p.givenLines) p.fuel (f.fr.group i)
    none counting p.printFailure
  change printed.toOption = _ at same
  cases he : printed with
  | error _ => simp [he] at h
  | ok ds =>
    refine ⟨ds, ?_⟩
    cases he' : (f.passGroupMode8 true p.force (f.givenAt p.givenLines) p.fuel (f.fr.group i)
        (counting := counting) (located := true)).2.1 <;> simp_all [Except.toOption]

theorem GroupContext.groupOperation_checked (p : GroupContext) (i : Nat) (demand : Bool)
    (below : GroupAnswers) (reads : Except String SourceClaimJson.GroupImports)
    (mkFront : SourceClaimJson.GroupImports → SourceClaimJson.PlanningFront p.force) (counting : Bool)
    (h : (((p.groupOperation i demand below (reads.map fun r => (r, mkFront r))).1.verdict counting).refusal) = none) :
    ∃ imports, reads = .ok imports ∧
      CheckedGroup p.ast p.fileKey p.budget p.force p.est p.tables imports i p.fuel p.givenLines counting := by
  cases reads with
  | error _ => contradiction
  | ok imports =>
    let names := some [SourceClaimJson.memberName (p.fr.unitId i)]
    let known := if demand then below else below ++ p.emptyAnswers i
    cases hp : imports.plan p.ast p.fileKey p.budget names {} p.force p.est p.tables (some (mkFront imports)) known with
    | error msg =>
      have herr : (p.groupOperation i demand below (.ok (imports, mkFront imports))).1.planned = .error msg := by
        unfold groupOperation
        dsimp only [SinglePass.work, Bind.bind, Except.bind]
        rw [hp]; rfl
      change (p.groupVerdict i (p.groupOperation i demand below (.ok (imports, mkFront imports))).1.planned counting).refusal = none at h
      rw [herr] at h; contradiction
    | ok pair =>
      obtain ⟨f₀, updated⟩ := pair
      let f := SourceClaimJson.PassUnit.preparedMode8 p.force p.givenLines true f₀
      have hplan : (p.groupOperation i demand below (.ok (imports, mkFront imports))).1.planned = .ok f := by
        unfold groupOperation
        dsimp only [SinglePass.work, Bind.bind, Except.bind]
        rw [hp]; rfl
      change (p.groupVerdict i (p.groupOperation i demand below (.ok (imports, mkFront imports))).1.planned counting).refusal = none at h
      rw [hplan] at h
      obtain ⟨ds, ha⟩ := groupVerdict_checked p i f counting h
      exact ⟨imports, rfl, names, mkFront imports, known, f₀, updated, ds, hp, ha⟩

/-- Names used at the slice boundary, indexed once on the validated front. -/
structure SliceIndex where
  units : Array (Fragment.Fn × List Fragment.TypeParam × Option (SourceClaimJson.Function EquationGraphs.Tree))
  names : GroupProjection.UnitNames
  unitIds : Array String
  functions : Std.HashMap String (List Nat)
  selectors : Std.HashMap String (List Nat)
  initMentions : Std.HashSet String
  statements : Array Fragment.Stmt
  bindings : Std.HashSet String

def SliceIndex.ofFront (fr : SourceClaimJson.Front) : SliceIndex := Id.run do
  let units := fr.units.toArray
  let ids := units.map fun (f, _, c) => if c.isSome then "init" else s!"{f.name}@{f.namePos.1}"
  let mut functions := {}
  let mut selectors := {}
  for ((fn, _, c), i) in units.zipIdx.reverse do
    if c.isNone then functions := functions.insert fn.name (i :: functions.getD fn.name [])
    let name := SourceClaimJson.memberName (ids.getD i "")
    selectors := selectors.insert name (i :: selectors.getD name [])
  return ⟨units, GroupProjection.UnitNames.ofFront fr, ids, functions, selectors, .ofList (fr.init.flatMap SourceElaboration.stmtNames),
    fr.init.toArray, .ofList fr.initNames⟩

/-- The same-name selection can include several overloads. Their bodies
and the initializer typing their module reads form the executable
part. A slot outside it brings its signatures and its group leader. -/
structure SliceLayout where
  bodies : List Nat
  signatures : List Nat
  statements : List Nat
  reads : List String
  externalGroups : List (List Nat)
  answerGroups : List Nat
  order : List Nat

def SliceIndex.layout (x : SliceIndex) (fr : SourceClaimJson.Front) (i : Nat) : SliceLayout := Id.run do
  let selected := ((x.selectors.getD (SourceClaimJson.memberName (x.unitIds.getD i "")) []).flatMap fr.group).eraseDups
  let fnIndex := fun j => (x.units[j]?).any (·.2.2.isNone)
  let bodies := selected.filter fnIndex
  let bodyReads := bodies.flatMap fun j => (x.units[j]?.map fun (fn, _, _) => SourceElaboration.moduleReadNames fn.body).getD []
  -- withInitTypes walks the initializer in order. An earlier statement can
  -- affect a later binding even when that statement binds no name itself.
  let whole := selected.any (fun j => !fnIndex j || (fr.edges j).any (!fnIndex ·)) || bodyReads.any x.bindings.contains
  let statements := if whole then List.range x.statements.size else []
  let reads := if whole then bodyReads ++ SourceElaboration.moduleReadNames fr.init else bodyReads
  let needed := reads.flatMap (x.functions.getD · [])
  let external := ((needed ++ selected.flatMap fr.edges).filter (!selected.contains ·)).map
    (fun j => (fr.group j).headD j) |>.eraseDups
  let groups := external.map fr.group
  let signatures := groups.flatten.filter fnIndex
  let names := (bodies ++ signatures).filterMap fun j => x.units[j]?.map (·.1.name)
  -- Leaving a component cannot lead back to it. External answers are
  -- already known; preserve depth-first overload order among selected bodies.
  let active := Std.HashSet.ofList selected
  let ordered := signatures ++ (SourceClaimJson.PassProposals.postorder active.size
    (fun j => (fr.edges j).filter active.contains) selected.reverse).filter fnIndex
  let groups := groups.map fun g => g.filter (fun j => fnIndex j || !statements.isEmpty)
  return ⟨bodies, signatures, statements, (reads ++ names).eraseDups, groups.filter (!·.isEmpty), external, ordered⟩

/-- File selection, shared preparation and the results retained by this worker. -/
structure PreparedFile extends GroupContext where
  index : SliceIndex
  layouts : Array (Thunk SliceLayout)
  declarations : Thunk (Except String GroupProjection.DeclarationIndex)
  declarationSites : Thunk GroupProjection.DeclarationSites
  replayDetails : Bool
  fileAnswers : IO.Ref (Std.HashMap Nat GroupAnswers)
  reportGroups : Bool
  counting : Bool
  imports : Thunk (Except String SourceClaimJson.PlanImports)
  fronts : IO.Ref (List (SourceClaimJson.PlanningFront force))
  modules : List String
  selected : Option (List String)
  /-- Groups whose interface another reachable group consumes. -/
  interfaceDemand : Std.HashSet Nat
  quiet : Bool
  t0 : Nat
  returned : IO.Ref (Std.HashSet Nat)
  proposals : IO.Ref (Std.HashMap Nat GroupAnswers)
  plans : IO.Ref (Std.HashMap Nat PlannedGroup)

/-- Interface demand of one prepared selection, using the existing group
dependency graph. Every reachable group is queued once. An incomplete walk
conservatively demands every group. -/
def demandedInterfaces (fr : SourceClaimJson.Front) (wanted : List Nat) : Std.HashSet Nat := Id.run do
  let mut pending := wanted
  let mut seen : Std.HashSet Nat := pending.foldl (·.insert ·) {}
  let mut demand : Std.HashSet Nat := {}
  for _ in List.range (fr.units.length + 1) do
    let some g := pending.head? | return demand
    pending := pending.tail
    for h in fr.dependencies (fr.group g) do
      demand := demand.insert h
      if !seen.contains h then
        seen := seen.insert h
        pending := h :: pending
  if pending.isEmpty then return demand
  return fr.leaders.foldl (·.insert ·) demand

/-- Mode 8's preparation of a file's fragment and the module interfaces its
imports read: the fragment and interfaces decoded, the file's claims and
front lowered (`fragmentClaims`, `fileFront`, no import read at an interface:
each unit's planning gives the front its own reads), the selection's closure
(`selectionClosure`); or the refusal of the fragment or of its lowering.
No unit is planned here: each unit's plans are computed in its own check
(`PreparedFile.plan`). -/
def prepareUnitsFile (astPath : String) (fileKey : String) (fuel : Nat) (names : Option String)
    (budget : PositiveCertificates.SearchBudget) (interfacesPath : String) (quiet : Bool := false)
    (force : List String := []) :
    IO (Except String PreparedFile) := do
  let emit := fun (s : String) => if quiet then pure () else IO.eprintln s
  -- Per-kind timings only where asked (`TSCERT_PROFILE`).
  SinglePass.profiling.set (← IO.getEnv "TSCERT_PROFILE").isSome
  SinglePass.dumping.set (← IO.getEnv "TSCERT_DUMP").isSome
  let t0 ← IO.monoNanosNow
  let ast ← readJson astPath
  -- Every symbol key at its canonical number (`Fragment.canonicalSymbols`),
  -- the module documents it carries too.
  let ast := ast >>= fun a => do
    Fragment.symbolNumbersApart [a]
    Fragment.canonicalSymbols a
  -- No unit is given a line: every loop head's proposal is inferred.
  let givenLines : Std.HashMap String Json := {}
  let interfaces ← readJson interfacesPath
  -- A selection names its roots: the units checked are those and every unit
  -- their verdicts rest on (`selectionClosure`).
  let selected : Option (List String) := match ast, selection names with
    | .ok a, some roots => some (selectionClosure a roots)
    | _, s => s
  let scope := Thunk.mk fun _ => ast >>= SourceClaimJson.ImportScope.of
  let tj ← IO.monoNanosNow
  -- The interfaces decoded, and the file's claims and front.
  let counting := (← IO.getEnv "TSCERT_COUNTS").isSome
  let shadow ← IO.getEnv "TSCERT_GROUP_SHADOW"
  let fileAnswers ← IO.mkRef {}
  let prepared : Except String (SourceClaimJson.Established × List (String × SourceClaimJson.RowTable) ×
      (Json × SourceClaimJson.Front) × Json) ← IO.lazyPure fun _ => do
    let cached ← interfaces
    let sc ← if (← jArr cached "modules").isEmpty then
        pure (⟨[], {}⟩ : SourceClaimJson.ImportScope)
      else scope.get
    let a ← ast
    let item := SourceClaimJson.fileItem a
    let (est, tables) ← SinglePass.work "rows: decode interfaces" item fun _ => SourceClaimJson.decodeInterfaces sc cached
    -- (as `fragmentPlansCore` lowers a file: its module documents apart)
    let a' := a.setObjVal! "modules" (Json.arr #[])
    let claims ← SinglePass.work "prepare: claims" item fun _ => SourceClaimJson.fragmentClaims a' fileKey {} force
    let definitions := EquationLowering.DefinitionCache.ofDocument (a.getObjValD "declarations")
    let fr ← SinglePass.work "prepare: file lowering" item fun _ => do
      let source ← SourceClaimJson.lowerEquationFront a' claims budget definitions
      SourceClaimJson.fileFrontFrom a'
        (Thunk.mk fun _ => SourceClaimJson.prepareEquationFront a' fileKey source) [] (lenient := true)
    return (est, tables, (claims, fr), a)
  let t1 ← IO.monoNanosNow
  let ms := fun (a b : Nat) => s!"{(b - a) / 1000000}"
  emit s!"stamp: read+lower {ms t0 t1} ms: read JSON {ms t0 tj} ms"
  -- The bytes of the files it read, with the pass's counts
  -- (`TSCERT_COUNTS`, `dev/perf-gate.mts`).
  if (← IO.getEnv "TSCERT_COUNTS").isSome then
    let size := fun (p : String) => do
      try pure (← System.FilePath.metadata p).byteSize.toNat catch _ => pure 0
    emit s!"counts-read: \{\"fragmentBytes\":{← size astPath},\"interfaceBytes\":{← size interfacesPath}}"
  let returned ← IO.mkRef {}
  let proposals ← IO.mkRef {}
  let plans ← IO.mkRef {}
  let fronts ← IO.mkRef []
  return prepared.map fun (est, tables, front, a) =>
    let index := SliceIndex.ofFront front.2
    { ast := a, index, layouts := (List.range index.units.size).toArray.map (fun i => Thunk.mk fun _ => index.layout front.2 i),
      reportGroups := ["1", "replay"].contains (shadow.getD ""),
      replayDetails := shadow == some "replay", fileAnswers, counting,
      declarations := Thunk.mk fun _ => GroupProjection.DeclarationIndex.of (a.getObjValD "declarations")
      declarationSites := Thunk.mk fun _ => GroupProjection.DeclarationSites.of a
      imports := Thunk.mk fun _ => scope.get.map (SourceClaimJson.planImportsIn a), fileKey, budget, est, tables, front, fronts, modules := (est.map (·.2.2)).eraseDups, selected,
      interfaceDemand := demandedInterfaces front.2 (front.2.selected selected), force,
      givenLines, fuel, quiet, t0, returned, proposals, plans }

/-- The units a prepared file's selection checks, in the order their checks
run: the leaders of the groups the selection names (`Front.selected`). -/
def PreparedFile.units (p : PreparedFile) : List Nat := p.fr.selected p.selected

/-- The worker shares initialization typing across groups reading the same
ordered qualified effects. The file, lowered front and force are fixed. -/
def PreparedFile.frontAt (p : PreparedFile) (imports : SourceClaimJson.GroupImports) :
    IO (SourceClaimJson.PlanningFront p.force) := do
  if let some f := (← p.fronts.get).find? (·.qualified == imports.qualified) then return f
  let f : SourceClaimJson.PlanningFront p.force :=
    { claims := p.front.1, raw := p.fr, qualified := imports.qualified }
  return f

/-- Postorder on the graph of groups. Each edge names its target's leader. -/
private def orderedGroups (fr : SourceClaimJson.Front) (roots : List Nat)
    (visited : Std.HashSet Nat) (answered : Nat → Bool := fun _ => false) : List Nat :=
  SourceClaimJson.PassProposals.postorder fr.groupTable.size
    (fun g => fr.dependencies (fr.group g)) roots (fun g => visited.contains g || answered g)

private def PreparedFile.unitId (p : PreparedFile) (i : Nat) : String := p.index.unitIds.getD i ""

/-- The lower groups in the order their proposals enter this group's input. -/
def groupsBelow (fr : SourceClaimJson.Front) (i : Nat) : List Nat :=
  let leader := fun j => (fr.group j).head?.getD j
  orderedGroups fr (((fr.group i).flatMap fr.edges).map leader) (({} : Std.HashSet Nat).insert (leader i))

/-- One traversal schedules a request, including repeated requested IDs. -/
private def requestedOrder (fr : SourceClaimJson.Front) (chosen : List Nat) : List Nat :=
  let counts := chosen.foldl (fun (m : Std.HashMap Nat Nat) g => m.insert g (m.getD g 0 + 1)) {}
  (orderedGroups fr chosen {}).flatMap fun g => List.replicate (counts.getD g 0) g

private def memberRequest (f : SourceClaimJson.FilePlans) (id : String) :
    Except String (SourceElaboration.SourceRequest (EquationStore.Checked f.F.equations f.F.primitive)
      (EquationStore.CheckedLabel f.F.equations f.F.primitive)) := do
  let some i := (List.range f.fr.units.length).find? (f.fr.unitId · == id) | throw s!"missing member {id}"
  let some plan := f.plans[i]? | throw s!"missing plan for {id}"
  return (← plan).parts.2.2

/-- Executable content at physical sites. Compare availability per member
so one failed member cannot hide another member's graph. -/
private def memberGraph (planned : PlannedGroup) (id : String) : Option Json := do
  let f ← planned.planned.toOption
  let r ← (memberRequest f id).toOption
  return toJson (r.start, r.program, r.codes.map fun c =>
    (c.async, c.entry.arity, c.entry.start, c.entry.exprs, c.entry.conts))

open EquationGraphs in
mutual
private def numberTree (number : Nat → Nat) : Tree → Tree
  | .app h args => .app (number h) (numberArgs number args)
  | .bound h args i => .bound (number h) (numberArgs number args) i
  | .meet parts => .meet (numberTypes number parts)
  | t => t
private def numberArgs (number : Nat → Nat) : Args → Args
  | .nil => .nil
  | .cons t ts => .cons (numberTypes number t) (numberArgs number ts)
private def numberTypes (number : Nat → Nat) : Types → Types
  | .nil => .nil
  | .cons t ts => .cons (numberTree number t) (numberTypes number ts)
end

open EquationGraphs PositiveGraphs in
/-- Present the result, inputs and array builtins by their finite ordinary
equations. Number heads in order of discovery from those roots. Thus a
recursive application visits its declaration once, at symbolic arguments. -/
private def bindingEquations (E : Equations) (roots : List (List Tree)) := Id.run do
  let builtins := E.builtins.map fun b => (b.keys, b.proto.map Subtype.val, b.unknown.map Subtype.val)
  let roots := roots ++ builtins.toList.flatMap (fun b => [b.2.1, b.2.2])
  let enqueue := fun (state : Std.HashMap Nat Nat × Array Nat) (heads : List Nat) =>
    heads.foldl (fun (st : Std.HashMap Nat Nat × Array Nat) h =>
      if st.1.contains h then st else (st.1.insert h st.2.size, st.2.push h)) state
  let mut queue := enqueue ({}, #[]) (roots.flatten.flatMap Tree.dependencyHeads)
  let mut rows : Array (Header × GraphRow Tree) := #[]
  for i in [:E.headers.size] do
    let some h := queue.2[i]? | break
    if hh : h < E.signature.length then
      let head := (⟨h, hh⟩ : Fin E.signature.length)
      if !E.ordinaryTemplate head then return none
      let row := E.rawBody head
      queue := enqueue queue (row.operands.flatten.flatMap Tree.dependencyHeads)
      let rename := numberTree (queue.1.getD · 0)
      rows := rows.push (E.signature[head], row.map rename (·.map rename))
    else return none
  if rows.size != queue.2.size then return none
  return some (roots.map (·.map (numberTree (queue.1.getD · 0))), builtins.map Prod.fst, rows)

open EquationGraphs PositiveGraphs in
/-- A finite graph for proposing a store map when the templates have different
presentations. Bound the syntax size of each instantiated label as well as
the number of expansions: repeated generic substitution can grow a label at
each step. Every proposed pair is checked on the unrestricted graphs. -/
private def proposalGraph (E : Equations) (roots : List (List (Label E.signature))) :
    NormalGraph (Label E.signature) :=
  let seeds := roots.flatten ++ E.builtins.toList.flatMap (fun b => b.proto ++ b.unknown)
  let limit := seeds.foldl (fun n l => max n l.val.size) (SourceClaimJson.matchFuel E.headers.size)
  NormalGraph.ofRowMap (fun l => if l.val.size ≤ limit then E.row l else .clauses []) E.builtins

@[nospecialize] private def rowsAgree {ι κ : Type} [LabelStore.Labels ι] [LabelStore.Labels κ]
    (from_ fromProposal : PositiveGraphs.NormalGraph ι) (to_ toProposal : PositiveGraphs.NormalGraph κ)
    (pairs : List (List ι × List κ)) (fuel : Nat) : Bool :=
  let _ : Inhabited κ := ⟨LabelStore.Labels.nul⟩
  let seeds := pairs.flatMap fun (a,b) => StoreMaps.startPairs fromProposal toProposal a b
  let map := StoreMaps.propose fromProposal toProposal fuel seeds {}
  StoreMaps.checkMapBody from_ to_ (fun xs => (xs.mergeSort LabelStore.Labels.le).eraseDups) map &&
    pairs.all fun (a,b) => StoreMaps.checkMapRoots map a b

/-- Compare slot names and types by their finite equations or by a checked
map between the two frozen stores. A failed search gives no correspondence. -/
private def memberBindings (file localPlan : PlannedGroup) (members : List String) : Except String Bool := do
  let f ← file.planned
  let g ← localPlan.planned
  members.allM fun id => do
    let a ← memberRequest f id
    let b ← memberRequest g id
    if a.siblings != b.siblings || a.inputs.length != b.inputs.length then return false
    let left := bindingEquations f.F.equations ((a.result :: a.inputs).map (·.map EquationStore.CheckedLabel.tree))
    let right := bindingEquations g.F.equations ((b.result :: b.inputs).map (·.map EquationStore.CheckedLabel.tree))
    if left.isSome && left == right then return true
    let G := LabelStore.StoreView.graph a.types
    let H := LabelStore.StoreView.graph b.types
    let pairs := (a.result, b.result) :: a.inputs.zip b.inputs
    let fuel := SourceClaimJson.matchFuel (max f.F.equations.headers.size g.F.equations.headers.size)
    let lhs := proposalGraph f.F.equations (a.result :: a.inputs)
    let rhs := proposalGraph g.F.equations (b.result :: b.inputs)
    return rowsAgree G lhs H rhs pairs fuel || rowsAgree H rhs G lhs (pairs.map Prod.swap) fuel


private def PreparedFile.layout (p : PreparedFile) (i : Nat) : SliceLayout :=
  match p.layouts[i]? with
  | some l => l.get
  | none => p.index.layout p.fr i

private def PreparedFile.inheritedReturn (p : PreparedFile) (i : Nat) : IO Bool := do
  let returned ← p.returned.get
  return (p.fr.dependencies (p.fr.group i)).any returned.contains

private def PreparedFile.recordAnswers (p : PreparedFile) (i : Nat) (answers : GroupAnswers) : IO Unit := do
  p.proposals.modify (·.insert i answers)
  if (← p.inheritedReturn i) || answers.any (fun (name, answer) =>
      p.index.initMentions.contains name && answer.any (·.resultFootprint != .top)) then
    p.returned.modify (·.insert i)

def PreparedFile.sliceInput (p : PreparedFile) (i : Nat) (demand : Bool) (below : GroupAnswers)
    (returnedBelow : Bool) : Except String GroupProjection.Slice := do
  let members := p.fr.group i
  let layout := p.layout i
  let ast ← GroupProjection.sliceProgram p.ast layout.bodies layout.signatures layout.statements
  -- Slot resolution sees the original declaration document, including
  -- ambiguous bindings. Only this group's executable code can read a slot.
  let imports := p.imports.get.bind fun ctx =>
    let code := Thunk.mk fun _ => do
      let full ← ctx.code.get
      let functions := full.functions.toArray
      let indices := ((layout.bodies ++ layout.signatures).eraseDups.mergeSort (· ≤ ·))
      let selected ← indices.mapM fun j => do
        let some (name, async_, body) := functions[j]? | throw "missing importer declaration"
        return (name, async_, if layout.bodies.contains j then body else Thunk.pure [])
      return if layout.statements.isEmpty then ⟨selected, [], Thunk.pure []⟩ else {full with functions := selected}
    SourceClaimJson.groupImports (.ok { ctx with code }) p.ast (some [SourceClaimJson.memberName (p.unitId i)]) {} p.est
  let (imports, est, tables) := GroupProjection.groupEnvironment layout.reads imports p.est p.tables
  let code := Json.arr #[ast.getObjValD "functions", ast.getObjValD "init"]
  let (declarations, missing) := (← p.declarations.get).slice code layout.reads (!tables.isEmpty)
  -- Preparation supplies the ownership decision. Omitted source mentions are
  -- read only to construct the full front’s ownership set.
  let ast := ast.setObjVal! "declarations" declarations
  let id := (p.index.names.references.getD · .initialization)
  let names := (layout.bodies ++ layout.signatures).filterMap fun j => p.index.units[j]?.map (·.1.name)
  let consumers := (names.filter p.index.initMentions.contains).eraseDups
  let owned := if layout.statements.isEmpty then [] else p.fr.moduleOwned
  return ⟨layout.externalGroups.map (·.map id), (p.fr.dependencies members).map id, returnedBelow,
    layout.order.map id, consumers, ast, members.map id, GroupProjection.ownedIn owned layout.reads code,
    if members.any (fun j => p.unitId j == "init") then p.fr.initOrder else none, demand,
    below.filter (fun (n, _) => names.contains n), imports, est, tables, p.force, p.fuel, p.budget, p.counting, missing, none⟩

/-- Plan and check with the slice as the only input. Every call builds its
own equation store, including the stores at the two proposal priors. -/
private abbrev ProposalResult := List SourceClaimJson.StandIn

def sliceFront (s : GroupProjection.Slice) :
    Except String (Json × SourceClaimJson.Front) := do
  let key ← s.ast.getObjValAs? String "file"
  let claims ← SinglePass.work "slice: claims" key fun _ => SourceClaimJson.fragmentClaims s.ast key {} s.force
  let source ← SinglePass.work "slice: lower equations" key fun _ => SourceClaimJson.lowerEquationFront s.ast claims s.budget ∅
  let raw ← SinglePass.work "slice: build front" key fun _ => SourceClaimJson.fileFrontFrom s.ast
    (Thunk.mk fun _ => SourceClaimJson.prepareEquationFront s.ast key source) [] (lenient := true)
  let raw ← match s.bindings with
    | none => pure raw
    | some env => env.install raw
  return (claims, raw)

/-- A front retained by slice preparation carries its origin. -/
abbrev PreparedSliceFront (s : GroupProjection.Slice) :=
  { front : Json × SourceClaimJson.Front // sliceFront s = .ok front }

def preparedSliceFront (s : GroupProjection.Slice) (prepared : Option (PreparedSliceFront s)) :
    Except String (Json × SourceClaimJson.Front) :=
  match prepared with
  | some input => .ok input.val
  | none => sliceFront s

theorem preparedSliceFront_eq (s : GroupProjection.Slice) (prepared : Option (PreparedSliceFront s)) :
    preparedSliceFront s prepared = sliceFront s := by
  cases prepared with
  | none => rfl
  | some input => exact input.property.symm

/-- Successful planning and checking at the index of this slice's leader. -/
def SlicePremise (s : GroupProjection.Slice) : Prop :=
  ∃ key claims raw leader i imports,
    s.ast.getObjValAs? String "file" = .ok key ∧ sliceFront s = .ok (claims, raw) ∧
    s.members.head? = some leader ∧
    ((GroupProjection.UnitNames.ofFront {raw with moduleOwned := s.owned, initOrder := s.initOrder}).references.finIdxOf? leader).map Fin.val = some i ∧
    s.imports = .ok imports ∧ CheckedGroup s.ast key s.budget s.force s.established s.tables imports i s.fuel {} s.counting

private structure SlicePlan (s : GroupProjection.Slice) extends PlannedGroup where
  checked : (verdict s.counting).refusal = none → SlicePremise s

private def success (x : Except ε α) : Except ε {a // x = .ok a} :=
  match x with
  | .ok a => .ok ⟨a,rfl⟩
  | .error e => .error e

private def planOnSlice (s : GroupProjection.Slice)
    (resolved : Option ProposalResult) (printFailure : SourceClaimJson.PassDiagnostic → String)
    (source : {r : Except String (Json × SourceClaimJson.Front) // r = sliceFront s}) :
    Except String (SlicePlan s × ProposalResult) := do
  let ⟨key,hkey⟩ ← success (s.ast.getObjValAs? String "file")
  let ⟨(claims, raw),hraw⟩ ← success source.val
  let fr := { raw with moduleOwned := s.owned, initOrder := s.initOrder }
  let some ⟨leader,hleader⟩ := s.members.head?.attach | throw "empty slice group"
  let refs := (GroupProjection.UnitNames.ofFront fr).references
  let some ⟨index,hindex⟩ := (refs.finIdxOf? leader).attach | throw "missing slice leader"
  let i := index.val
  let indices := Std.HashMap.ofList refs.toList.zipIdx
  let indexOf := fun (id : SourceClaimJson.UnitRef) => match indices.get? id with
    | some j => Except.ok j
    | none => .error s!"missing slice unit {repr id}"
  let members ← s.members.mapM indexOf
  unless (fr.group i).mergeSort (· ≤ ·) == members.mergeSort (· ≤ ·) do throw "slice changes group membership"
  let mut groups := members.foldl (fun gs j => gs.setIfInBounds j members) fr.groupTable
  for external in s.externalGroups do
    let group ← external.mapM indexOf
    unless external.all (!s.members.contains ·) do throw "external group includes a checked member"
    for j in group do groups := groups.setIfInBounds j group
  let fr := { fr with groupTable := groups }
  let deps ← s.dependencies.mapM indexOf
  unless (fr.dependencies members).mergeSort (· ≤ ·) == deps.mergeSort (· ≤ ·) do
    throw "slice changes group dependencies"
  let context : GroupContext := {
    ast := s.ast, fileKey := key, budget := s.budget, est := s.established, tables := s.tables, printFailure,
    force := s.force, front := (claims, fr), givenLines := {}, fuel := s.fuel }
  let order ← s.proposalOrder.mapM indexOf
  let own := (fr.group i).filterMap fun j => fr.units[j]?.map (·.1.name)
  let known := match resolved with
    | none => s.below
    | some computed => order.filterMap fun j => do
      let (f, _, none) ← fr.units[j]? | none
      return (f.name, computed.find? (·.name == f.name))
  let below := if resolved.isSome then known else known.filter fun (n, _) => !own.contains n
  let mkFront := fun (reads : SourceClaimJson.GroupImports) =>
    { claims, raw := fr, proposalInputs := some ⟨order, s.resultConsumers, below, s.inheritedReturn⟩,
      qualified := reads.qualified : SourceClaimJson.PlanningFront s.force }
  let operation := context.groupOperation i s.demand known (s.imports.map fun r => (r, mkFront r))
  have checked : (operation.1.verdict s.counting).refusal = none → SlicePremise s := by
    intro h
    obtain ⟨imports, hi, hc⟩ := context.groupOperation_checked i s.demand known s.imports mkFront s.counting h
    exact ⟨key, claims, raw, leader, i, imports, hkey, source.property.symm.trans hraw,
      hleader, congrArg (Option.map Fin.val) hindex, hi, hc⟩
  return (⟨operation.1, checked⟩, (operation.2.map (·.rounds.result)).getD [])

private def planSliceWithResult (s : GroupProjection.Slice) (resolved : Option ProposalResult)
    (printFailure : SourceClaimJson.PassDiagnostic → String := SourceClaimJson.PassDiagnostic.render)
    (prepared : Option (PreparedSliceFront s) := none) :=
  planOnSlice s resolved printFailure ⟨preparedSliceFront s prepared, preparedSliceFront_eq s prepared⟩

private theorem planSlice_prepared (s : GroupProjection.Slice) (resolved : Option ProposalResult)
    (print : SourceClaimJson.PassDiagnostic → String) (prepared : Option (PreparedSliceFront s)) :
    planSliceWithResult s resolved print prepared = planSliceWithResult s resolved print none := by
  apply congrArg (planOnSlice s resolved print)
  exact Subtype.ext (preparedSliceFront_eq s prepared)

def planSlice (s : GroupProjection.Slice) : Except String PlannedGroup :=
  (planSliceWithResult s none).map (·.1.toPlannedGroup)

/-- Measure reuse of the relative input by executing it and materializing its verdict. -/
private def replayFields (p : PreparedFile) (physical : GroupProjection.Slice)
    (group : PlannedGroup) (verdict : String) : List (String × Json) := Id.run do
  let .ok (relative, sites) := physical.relative p.declarationSites.get | return [("relative", toJson false)]
  let agreement : Except String (Option String) := do
    let localPlan ← planSlice relative
    let file ← localPlan.planned
    let line ← Json.parse (localPlan.verdict p.counting).line
    let named ← (GroupProjection.UnitNames.ofFront file.fr).nameVerdict line
    unless (named.getObjValD "refusal").isNull && (named.getObjValD "elaboration").isNull do return none
    let current ← p.index.names.printVerdict named
    if (← sites.printContracts current) == verdict && localPlan.answers == group.answers then return some named.compress
    return none
  let line := agreement.toOption.join
  let input := if line.isSome then relative else physical
  let fields := input.fields.map fun (k,v) => (k, toString (hash v.compress))
  let result := toString (hash (toJson (line.getD verdict, GroupProjection.answersWire group.answers)).compress)
  return [("fields", toJson fields), ("relative", toJson line.isSome), ("result", toJson result)]

/-- Compare each physical member and the verdict and proposals published by
the two independent folds. Keep the slice verdict for the worker's reply. -/
private def PreparedFile.reportSlice (p : PreparedFile) (i : Nat)
    (slice : Except String GroupProjection.Slice) (group ordinary : PlannedGroup) : IO GroupVerdict := do
  let start ← IO.monoNanosNow
  let unit := p.unitId i
  let members := (p.fr.group i).map p.unitId
  let mut unavailable := #[]
  for member in members do
    let a := memberGraph ordinary member
    let b := memberGraph group member
    if a != b then throw (IO.userError s!"group shadow: different executable graph for {member} in {unit}")
    if a.isNone then unavailable := unavailable.push member
  let graphs := if unavailable.size == members.length then "both plans unavailable" else "equal"
  let verdict ← IO.lazyPure fun _ => group.verdict p.counting
  let fileVerdict ← IO.lazyPure fun _ => ordinary.verdict p.counting
  let sameOutcome := verdict.refusal.isNone == fileVerdict.refusal.isNone
  if verdict.refusal.isNone && !unavailable.isEmpty then
    throw (IO.userError s!"group shadow: accepted {unit} lacks executable graphs for {unavailable}")
  let sameProposals := group.answers == ordinary.answers
  unless sameOutcome && sameProposals do
    throw (IO.userError s!"group shadow: {unit}: same outcome {sameOutcome}, same proposals {sameProposals}")
  let bindings ← IO.lazyPure fun _ => SinglePass.work "shadow: binding types" unit fun _ =>
    (memberBindings ordinary group members).toOption
  let details ← if p.replayDetails then do
    let physical ← IO.ofExcept slice
    IO.lazyPure fun _ => replayFields p physical group verdict.line
  else pure []
  let id := (p.fr.group i).filterMap fun j => (p.index.units[j]?).map fun (f, _, _) => p.fr.lexicalId f
  let elapsed := (← IO.monoNanosNow) - start
  IO.eprintln ("group-slice " ++ (Json.mkObj ([("unit", toJson unit), ("group", toJson id),
    ("graphs", toJson graphs), ("unavailableMembers", toJson unavailable), ("bindings", toJson bindings), ("verdict", toJson verdict.line),
    ("answers", GroupProjection.answersWire group.answers), ("fileVerdict", toJson fileVerdict.line),
    ("proposalsEqual", toJson sameProposals), ("elapsedNs", toJson elapsed)] ++ details)).compress)
  return verdict

/-- Supply this group's current import reads and their shared front. -/
def PreparedFile.plan (p : PreparedFile) (i : Nat) (demand : Bool) (below : GroupAnswers) : IO PlannedGroup := do
  let names := some [SourceClaimJson.memberName (p.unitId i)]
  let returnedBelow ← p.inheritedReturn i
  let slice := Thunk.mk fun _ => p.sliceInput i demand below returnedBelow
  let localPlan := Thunk.mk fun _ =>
    match slice.get >>= (fun s => (planSliceWithResult s none (printFailure := p.printFailure)).map (·.1.toPlannedGroup)) with
    | .ok g => g
    | .error reason => ⟨.error reason, p.emptyAnswers i, p.groupVerdict i (.error reason)⟩
  if !p.reportGroups then return localPlan.get
  let reads ← IO.lazyPure fun _ => SourceClaimJson.groupImports p.imports.get p.ast names {} p.est
  let fileAnswers ← p.fileAnswers.get
  let fileBelow := (groupsBelow p.fr i).flatMap fun j => fileAnswers.getD j []
  let inputs ← match reads with
    | .error reason => pure (.error reason)
    | .ok imports => pure (.ok (imports, ← p.frontAt imports))
  let (group, updated) ← IO.lazyPure fun _ => p.groupOperation i demand fileBelow inputs
  if let some f := updated then
    p.fronts.modify fun fs => f :: fs.filter (·.qualified != f.qualified)
  p.fileAnswers.modify (·.insert i group.answers)
  let verdict ← p.reportSlice i slice.get localPlan.get group
  return { localPlan.get with verdict := fun counting =>
    if counting == p.counting then verdict else localPlan.get.verdict counting }

/-- Whether this worker may consume a group's inferred interface: from
another selected group, recursive members, or an explicit effect contract.
Module-interface publication uses its own planner and still infers its rows. -/
def PreparedFile.needsInterface (p : PreparedFile) (i : Nat) : Bool :=
  let group := p.fr.group i
  let own := group.filterMap fun j => (p.index.units[j]?).map (·.1.name)
  !p.force.isEmpty || p.interfaceDemand.contains i ||
    group.any (fun j => (p.index.units[j]?).any fun (fn, _, init) =>
      (if init.isSome then p.fr.init else fn.body).any (fun st => (SourceElaboration.stmtNames st).any own.contains) ||
        fn.stated.isSome)

/-- Every lower group has answered when its caller is planned. A named
empty answer and a group with no function answers are both completed reads. -/
def PreparedFile.lowerAnswers (p : PreparedFile) (groups : List Nat) : IO GroupAnswers := do
  let answers ← p.proposals.get
  let values ← groups.mapM fun g => match answers.get? g with
    | some value => pure value
    | none => throw (IO.userError s!"file worker: missing proposals for {p.unitId g}")
  return values.flatten

/-- Diagnostic text includes the names and numbering of the physical equation
store. Resolve the diagnostic node on the prepared file front with published answers. -/
private def PreparedFile.diagnosticPlan (p : PreparedFile) (i : Nat) (own : GroupAnswers) : IO (Except String PlannedGroup) := do
  let id := p.unitId i
  let selected := (p.fr.selected (some [SourceClaimJson.memberName id])).flatMap p.fr.group
  let order := (SourceClaimJson.PassProposals.calleesFirst p.fr selected).filter (!p.fr.isInitialization ·)
  let below ← p.lowerAnswers (groupsBelow p.fr i)
  let fixed := below ++ own
  let reads ← IO.lazyPure fun _ => SourceClaimJson.groupImports p.imports.get p.ast (some [SourceClaimJson.memberName id]) {} p.est
  let inputs : Except String (SourceClaimJson.GroupImports × SourceClaimJson.PlanningFront p.force) ← match reads with
    | .error reason => pure (.error reason)
    | .ok imports =>
      let front ← p.frontAt imports
      pure (.ok (imports, { front with proposalInputs := some ⟨order, p.index.initMentions.toList, fixed, false⟩ }))
  return .ok (p.groupOperation i true fixed inputs).1

private def memberError (plan : Except String SourceClaimJson.FilePlans) (unit : SourceClaimJson.UnitRef) :
    Except String (String × String) := do
  let f ← plan
  let some i := f.fr.unitReferences.finIdxOf? unit | throw "missing elaboration unit"
  let some (.error reason) := f.plans[i.val]? | throw "missing elaboration error"
  return (reason, f.beforePass i.val true reason)

private def failureMessage (failure : GroupProjection.StoredFailure) (sites : GroupProjection.Sites)
    (plan : Except String SourceClaimJson.FilePlans) (fuel : Nat) : Except String String :=
  match failure with
  | .planning reason => pure (match plan with | .error msg => msg | .ok _ => reason)
  | .text msg => pure msg
  | .located msg => msg.print sites (fun n => do n.read (← plan) fuel)
  | .elaboration unit => (memberError plan unit).map Prod.snd
  | .expression unit index exhausted => do
    let f ← plan
    let some i := f.fr.unitReferences.finIdxOf? unit | throw "missing expression obligation unit"
    let some (.ok (.graph _ _ r)) := f.plans[i.val]? | throw "missing expression obligation graph"
    let some obligation := r.obligations[index]? | throw "missing expression obligation"
    if exhausted then
      -- An exhausted search names an intermediate comparison within the obligation.
      -- The prefix shares its answer cache and vocabulary with that comparison.
      let result := ExpressionClaims.produceUsing (LabelStore.StoreView.graph r.types)
        (LabelStore.StoreView.images r.types) r.searchLabels (LabelStore.StoreView.valid r.types)
        (LabelStore.StoreView.projection r.types) fuel r.obligations
      if let .error reason := result then
        if SourceClaimJson.expressionObligation? reason == some (index, true) then return reason
      throw "missing exhausted expression comparison"
    return obligation.failure index fuel (LabelStore.StoreView.projection r.types)

private def encodeFailure (failure : SourceClaimJson.PassDiagnostic) :=
  (toJson (GroupProjection.StoredFailure.ofFailure failure)).compress

/-- Resolve each outstanding dependency once, stopping the walk at a
published answer. Planning consumes the slots selected by the group's
members and their initializer. A recursive member reads its peers at
their written effects or top during settlement (`PassProposals.proposeOne`). -/
def PreparedFile.known (p : PreparedFile) (i : Nat) : IO (List (String × Option SourceClaimJson.StandIn)) := do
  let fr := p.fr
  let deps := fr.dependencies (fr.group i)
  let answered ← p.proposals.get
  let below := orderedGroups fr deps {} answered.contains
  for g in below do
    if (← p.proposals.get).contains g then continue
    let known ← p.lowerAnswers (p.layout g).answerGroups
    let group ← p.plan g (p.needsInterface g) known
    p.plans.modify (·.insert g group)
    p.recordAnswers g group.answers
  p.lowerAnswers (p.layout i).answerGroups

/-- Unit `i`'s check: its group planned in its check (`PreparedFile.plan`,
the proposals below it read through `PreparedFile.known`; the plans an
earlier unit's proposals planned it at, where kept, then released), then
`FilePlans.passGroupMode8` over its group: its verdict line
(`WorkerWire.verdictLine`), accepted with its dependencies or refused, with
its group's first elaboration refusal; and its refusal. A function of the
prepared file and `i`. -/
def PreparedFile.check (p : PreparedFile) (i : Nat) : IO (String × Option String) := do
  let emit := fun (s : String) => if p.quiet then pure () else IO.eprintln s
  let unit := p.unitId i
  let s0 ← IO.monoNanosNow
  let p0 ← SinglePass.passNanos.get
  let compare := (← IO.getEnv "TSCERT_COMPARE").isSome
  let debugNode := ((← IO.getEnv "TSCERT_NODE").bind String.toNat?).getD 1000000000
  let repeats := ((← IO.getEnv "TSCERT_REPEAT").bind String.toNat?).getD 1
  -- Observing: the state at `TSCERT_OBSERVE` (`node:L` or `offset:K`).
  let observe ← IO.getEnv "TSCERT_OBSERVE"
  -- The pass's counts as JSON lines (`TSCERT_COUNTS`, `dev/perf-gate.mts`).
  let counting := p.counting
  let p := if p.reportGroups then p else {p with printFailure := encodeFailure}
  let group ← match (← p.plans.get).get? i with
    | some group => do p.plans.modify (·.erase i); pure group
    | none => do
      let below ← p.known i
      let group ← p.plan i (p.needsInterface i) below
      p.recordAnswers i group.answers
      pure group
  if (← IO.getEnv "TSCERT_TRACE_PROPOSALS").isSome then
    let footprint := fun (f : Footprints.Closed) => Json.mkObj
      [("value", EffectJson.changeName f.value), ("array", EffectJson.changeName f.array), ("view", EffectJson.changeName f.view)]
    let answers := group.answers.map fun (name, value) => (name, value.map fun (v : SourceClaimJson.StandIn) =>
      Json.mkObj [("normal", toJson (v.summary.normal.map footprint)), ("exceptional", toJson (v.summary.exceptional.map footprint)),
        ("resultFootprint", footprint v.resultFootprint), ("returnAlias", toJson v.returnAlias)])
    IO.eprintln (Json.mkObj [("unit", toJson unit), ("answers", toJson answers)]).compress
  if let .ok f := group.planned then
    let raw := (← IO.getEnv "TSCERT_PASS_REFUSALS") == some "raw"
    if compare || debugNode != 1000000000 || repeats != 1 || observe.isSome || raw then
      let some localIndex := (List.range f.fr.units.length).find? (f.fr.unitId · == unit)
        | throw (IO.userError s!"missing planned unit {unit}")
      let (diagnostics, observed, _, _) ← IO.lazyPure fun _ =>
        f.passGroupMode8 true p.force (f.givenAt p.givenLines) p.fuel (f.fr.group localIndex)
          compare debugNode repeats none observe counting (!raw)
      for line in diagnostics do IO.eprintln line
      if raw then
        if let .error reason := observed then IO.eprintln reason
  let result ← IO.lazyPure fun _ => group.verdict counting
  let result ← if let some raw := result.refusal then do
      if p.reportGroups || !group.planned.isOk then pure result else do
        let failure ← IO.ofExcept (Json.parse raw >>= fromJson? (α := GroupProjection.StoredFailure))
        let plan ← if failure.readsPlan then do
            pure ((← p.diagnosticPlan i group.answers).bind (·.planned))
          else pure group.planned
        let reason ← IO.ofExcept (failureMessage failure {} plan p.fuel)
        let j ← IO.ofExcept (Json.parse result.line)
        let j ← match failure with
          | .elaboration unit => do
            let (why, _) ← IO.ofExcept (memberError plan unit)
            pure (j.setObjVal! "elaboration" (toJson why))
          | _ => pure j
        pure {result with refusal := some reason, line := (j.setObjVal! "refusal" (toJson reason)).compress}
    else pure result
  let p1 ← SinglePass.passNanos.get
  let s1 ← IO.monoNanosNow
  let ms := fun (a b : Nat) => s!"{(b - a) / 1000000}"
  for line in result.diagnostics do emit line
  let kinds ← SinglePass.kindNanos.get
  emit s!"rule time by term kind (ms, applications): {kinds.toList.map fun (k, t, n) => s!"{k} {t / 1000000} {n}"}"
  emit s!"stamp: {unit} pass {ms p0 p1} ms, with obligations and vocabulary {ms s0 s1} ms, total {ms p.t0 s1} ms"
  return (result.line, result.refusal)

/-- A line on standard output, flushed: a reader of the stream sees it as
soon as it is written. -/
def printFlushed (line : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn line
  out.flush

/-- The worker waits only after flushing its lookup. The driver renames
the complete reply into this worker's private execution directory. -/
private def sliceLookup (operation : String) : IO (String × Json) := do
  printFlushed ("slice-lookup " ++ operation)
  let reply : System.FilePath := "slice-reply"
  while !(← reply.pathExists) do IO.sleep 1
  let bytes ← IO.FS.readFile reply
  let stored ← IO.ofExcept (Json.parse bytes)
  IO.FS.removeFile reply
  return (bytes, stored)

private abbrev Acceptance (s : GroupProjection.Slice) := {ok : Bool // ok = true → SlicePremise s}

private def noAcceptance (s : GroupProjection.Slice) : Acceptance s := ⟨false, by intro h; contradiction⟩

/-- Execute the proposed or checked group with its prepared front. -/
private def computeSlice (slice : GroupProjection.Slice) (check : Bool)
    (resume : Option (Except String ProposalResult))
    (prepared : Option (PreparedSliceFront slice)) : Json × Acceptance slice := Id.run do
  let planned : Except String (GroupAnswers × Option String × ProposalResult × Acceptance slice) := do
    let prior ← resume.mapM id
    let (g, result) ← planSliceWithResult slice prior (printFailure := encodeFailure) (prepared := prepared)
    let file ← g.planned
    let (line, permit) ← if check then do
        let verdict := g.verdict slice.counting
        let j ← Json.parse verdict.line
        let symbolic ← (GroupProjection.UnitNames.ofFront file.fr).nameVerdict j
        let symbolic : Json ← if let .ok ds := symbolic.getObjValAs? (List Json) "depends" then do
            let (imported, localRefs) := ds.partition fun (d : Json) => d.getStr?.toOption.any (·.startsWith "module:")
            let expected := slice.dependencies.map toJson
            unless (localRefs.map Json.compress).mergeSort (· ≤ ·) == (expected.map Json.compress).mergeSort (· ≤ ·) do
              throw "slice verdict changes group dependencies"
            pure (symbolic.setObjVal! "depends" (toJson (expected ++ imported)))
          else pure symbolic
        let symbolic ← if let .ok refusal := symbolic.getObjValAs? String "refusal" then do
            let message ← Json.parse refusal
            pure (symbolic.setObjVal! "refusal" message)
          else pure symbolic
        let symbolic ← if (symbolic.getObjValD "elaboration").isNull then pure symbolic else do
          let selected := match slice.members.headD .initialization with
            | .initialization => ":init"
            | .declaration name _ => name
          let some (i, _) := file.failedElaboration (some [selected]) | throw "missing failed elaboration"
          let some unit := file.fr.unitReferences[i]? | throw "missing elaboration unit"
          pure (symbolic.setObjVal! "elaboration" (toJson unit))
        pure (some symbolic.compress, ⟨verdict.refusal.isNone, fun h => g.checked (Option.isNone_iff_eq_none.mp h)⟩)
      else pure (none, noAcceptance _)
    return (g.answers, line, result, permit)
  let (answers, line, resolution, permit) := match planned with
    | .ok (answers, line, computed, permit) =>
      (answers, line, Json.mkObj
        [("computed", GroupProjection.answersWire (computed.map fun (s : SourceClaimJson.StandIn) => (s.name, some s)))], permit)
    | .error reason =>
      let empty : GroupAnswers := slice.members.filterMap fun
        | SourceClaimJson.UnitRef.initialization => none
        | .declaration name _ => some (name, none)
      let verdict := Json.mkObj [("unit", toJson (slice.members.headD .initialization)),
        ("members", toJson slice.members), ("refusal", toJson (GroupProjection.StoredFailure.planning reason)),
        ("elaboration", toJson reason), ("contracts", .arr #[])]
      (empty, if check then some verdict.compress else none, Json.mkObj [("error", toJson reason)], noAcceptance _)
  return (Json.mkObj [("operation", toJson (if check then "check-slice" else "propose-slice")),
    ("members", toJson slice.members), ("answers", GroupProjection.answersWire answers), ("line", toJson line),
    ("resolution", resolution)], permit)

private def decodeResolution (j : Json) : Except String (Except String ProposalResult) := do
  if let .ok msg := j.getObjValAs? String "error" then
    fieldsExactly j ["error"]
    return .error msg
  fieldsExactly j ["computed"]
  let entries ← GroupProjection.decodeAnswers (← j.getObjVal? "computed")
  let computed ← entries.mapM fun (name, answer) => do
    let some s := answer | throw "missing resolved stand-in"
    unless s.name == name do throw "wrong resolved stand-in"
    return s
  return .ok computed

/-- The accepted flag of the stored relative line, as read on a hit. -/
def lineAccepted (line : String) : Bool :=
  ((Json.parse line >>= (·.getObjValAs? Bool "accepted")).toOption == some true)

def payloadAccepted (payload : Json) : Bool :=
  (payload.getObjValAs? (Option String) "line").toOption.join.any lineAccepted

def storedAccepted (bytes : String) : Bool := (Json.parse bytes).toOption.any payloadAccepted

private def publishSlice (s : GroupProjection.Slice) (payload : Json) (permit : Acceptance s) :
    Except String (Json × String) :=
  let bytes := payload.compress
  if permit.val || !storedAccepted bytes then .ok (payload, bytes)
  else .error "refused group encoded an accepted line"

private def readResume (bytes : String) : Except String (Except String ProposalResult) := do
  let reply ← Json.parse bytes
  let proposal ← reply.getObjVal? "resume"
  decodeResolution (← proposal.getObjVal? "resolution")

/-- The result and the bytes published for it. A resumed check reads the
complete reply whose digest occurs in the driver's check key. -/
def sliceResult (s : GroupProjection.Slice) (check : Bool) (resume : Option String)
    (prepared : Option (PreparedSliceFront s) := none) : Except String (Json × String) := do
  let prior ← resume.mapM readResume
  let (payload, permit) := computeSlice s check prior prepared
  publishSlice s payload permit

theorem sliceResult_prepared (s : GroupProjection.Slice) (check : Bool) (resume : Option String)
    (prepared : Option (PreparedSliceFront s)) :
    sliceResult s check resume prepared = sliceResult s check resume none := by
  simp only [sliceResult, computeSlice, planSlice_prepared]

/-- Equal operation inputs give equal published bytes and results. -/
theorem sliceResult_of_wire {s t : GroupProjection.Slice} (h : s.wire = t.wire)
    (check : Bool) (resume : Option String) (p : Option (PreparedSliceFront s))
    (q : Option (PreparedSliceFront t)) :
    sliceResult s check resume p = sliceResult t check resume q := by
  obtain rfl := GroupProjection.Slice.wire_injective h
  exact (sliceResult_prepared s check resume p).trans (sliceResult_prepared s check resume q).symm

/-- A store hit identifies a publication under the same implementation and
operation, with equal slice and resumption bytes by collision resistance. -/
theorem replayedAccepted_premise {s t : GroupProjection.Slice} (h : s.wire = t.wire)
    {check : Bool} {resume : Option String} {p : Option (PreparedSliceFront t)}
    {payload : Json} {bytes : String} (published : sliceResult t check resume p = .ok (payload, bytes))
    (accepted : storedAccepted bytes = true) : SlicePremise s := by
  obtain rfl := GroupProjection.Slice.wire_injective h
  unfold sliceResult at published
  cases prior : resume.mapM readResume with
  | error e => rw [prior] at published; contradiction
  | ok r =>
    rw [prior] at published
    let out := computeSlice s check r p
    change publishSlice s out.1 out.2 = .ok (payload, bytes) at published
    unfold publishSlice at published
    dsimp only at published
    split at published <;> cases published
    exact out.2.property (by simp_all)

private def readCertifiedSliceResult (p : PreparedFile) (i : Nat) (slice : GroupProjection.Slice)
    (sites : GroupProjection.Sites)
    (operation : String) (payload : Json) (render := true)
    (plan : Except String SourceClaimJson.FilePlans := .error "missing diagnostic plan") :
    Except String (Option {l : String // lineAccepted l = true → payloadAccepted payload = true} × GroupAnswers) := do
  let unit := p.unitId i
  let members := (p.fr.group i).map p.unitId
  fieldsExactly payload ["operation", "members", "answers", "line", "resolution"]
  unless (← payload.getObjValAs? String "operation") == operation &&
      (← payload.getObjVal? "members") == toJson slice.members do throw "wrong slice result"
  let answers ← GroupProjection.decodeAnswers (← payload.getObjVal? "answers")
  let names := answers.map Prod.fst
  let synchronous := (p.fr.group i).filterMap fun j => do
    let (f, _, none) ← p.index.units[j]? | none
    if f.async then none else some f.name
  unless (names == synchronous || names == (p.emptyAnswers i).map Prod.fst) &&
      answers.all (fun (n,v) => v.all (·.name == n)) do throw "wrong slice proposal members"
  let ⟨relative,hr⟩ ← success (payload.getObjValAs? (Option String) "line")
  unless relative.isSome == (operation == "check-slice") do throw "missing or unexpected slice verdict"
  let some ⟨l,hl⟩ := relative.attach | return (none, answers)
  let ⟨raw,hraw⟩ ← success (Json.parse l)
  let accepted := (raw.getObjValAs? Bool "accepted").toOption == some true
  have origin : payloadAccepted payload = accepted := by
    change relative = some l at hl
    simp [payloadAccepted, hr, hl, lineAccepted, hraw, EffectCodec.ok_bind, accepted, Except.toOption]
  unless (← raw.getObjVal? "unit") == toJson (slice.members.headD .initialization) &&
      (← raw.getObjVal? "members") == toJson slice.members do throw "wrong relative slice members"
  unless render do return (none, answers)
  let failure ← (raw.getObjVal? "refusal").toOption.mapM (fromJson? (α := GroupProjection.StoredFailure))
  let raw ← match failure with
    | some (.planning reason) =>
      let current := match plan with | .error msg => msg | .ok _ => reason
      pure ((raw.setObjVal! "elaboration" (toJson current)).setObjVal! "refusal" (toJson current))
    | _ => do
      let raw ← if (raw.getObjValD "elaboration").isNull then pure raw else do
        let unit ← fromJson? (raw.getObjValD "elaboration")
        let (reason, _) ← memberError plan unit
        pure (raw.setObjVal! "elaboration" (toJson reason))
      match failure with
      | none => pure raw
      | some reason => do
        let text ← failureMessage reason sites plan p.fuel
        pure (raw.setObjVal! "refusal" (toJson text))
  let raw ← if let .ok deps := raw.getObjValAs? (List Json) "depends" then
      pure (raw.setObjVal! "depends" (toJson (deps.map fun dep =>
        (dep.getStr?.toOption.bind sites.moduleUnits.get?).map Json.str |>.getD dep)))
    else pure raw
  let j ← p.index.names.printVerdict raw
  unless (← j.getObjValAs? String "unit") == unit &&
    (← j.getObjValAs? (List String) "members") == members do throw "wrong resolved slice members"
  let text ← sites.printContracts j
  if h : accepted || !lineAccepted text then
    return (some ⟨text, fun ht => by simpa [origin, ht] using h⟩, answers)
  throw "refused group rendered an accepted line"

def readSliceResult (p : PreparedFile) (i : Nat) (s : GroupProjection.Slice)
    (sites : GroupProjection.Sites) (operation : String) (payload : Json) (render := true)
    (plan : Except String SourceClaimJson.FilePlans := .error "missing diagnostic plan") :=
  (readCertifiedSliceResult p i s sites operation payload render plan).map
    fun (line, answers) => (line.map Subtype.val, answers)

/-- The actual materialized line of a replayed check supplies the current
slice's successful planning and pass premises. -/
theorem replayedLine_premise {s t : GroupProjection.Slice} (key : s.wire = t.wire)
    {resume : Option String} {front : Option (PreparedSliceFront t)} {previous payload : Json} {bytes : String}
    (published : sliceResult t true resume front = .ok (previous, bytes))
    (reply : Json.parse bytes = .ok payload) {p : PreparedFile} {i : Nat} {sites : GroupProjection.Sites}
    {plan : Except String SourceClaimJson.FilePlans} {line : String} {answers : GroupAnswers}
    (read : readSliceResult p i s sites "check-slice" payload true plan = .ok (some line, answers))
    (accepted : lineAccepted line = true) : SlicePremise s := by
  apply replayedAccepted_premise key published
  simp only [storedAccepted, reply, Except.toOption, Option.any_some]
  unfold readSliceResult at read
  cases h : readCertifiedSliceResult p i s sites "check-slice" payload true plan with
  | error => rw [h] at read; contradiction
  | ok pair =>
    obtain ⟨l, a⟩ := pair
    rw [h] at read
    cases l with
    | none => cases read
    | some v => cases read; exact v.property accepted

/-- A separately checked initializer supplies its captured slots. Its
declarators supply the binding sites and written annotations to lowering. -/
private def bindingSlice (p : PreparedFile) (s : GroupProjection.Slice) (i : Nat) : IO GroupProjection.Slice := do
  if s.members.contains .initialization || !(s.dependencies.contains .initialization) ||
      !s.resultConsumers.isEmpty then return s
  let some imports := s.imports.toOption | return s
  let layout := p.layout i
  let reads := (layout.bodies.flatMap fun j =>
    (p.index.units[j]?.map fun (fn, _, _) => SourceElaboration.moduleReadNames fn.body).getD []).eraseDups
  -- A class brings its constructor and generic declaration into the front.
  if reads.any (SourceElaboration.sourceClasses p.fr.init).contains then return s
  let front ← p.frontAt imports
  p.fronts.modify fun fs => if fs.any (·.qualified == front.qualified) then fs else front :: fs
  let some env := GroupProjection.bindingEnvironment front.base.get.2.get reads | return s
  let slots := env.slots.map Prod.fst
  if slots.isEmpty then return s
  let mut init := #[]
  for statement in (s.ast.getObjValAs? (Array Json) "init").toOption.getD #[] do
    let bindings := (statement.getObjValAs? (Array Json) "bindings").toOption.getD #[]
    for binding in bindings do
      let name := (binding.getObjValAs? String "name").toOption.getD ""
      if slots.contains name then
        let pos := binding.getObjValD "namePos"
        let value := Json.mkObj [("k", "lit"), ("pos", pos), ("lit", Json.mkObj [("a", "undefined")])]
        let binder := binding.setObjVal! "init" value
        init := init.push (statement.setObjVal! "pos" pos |>.setObjVal! "bindings" (.arr #[binder]))
  if init.size != slots.length then return s
  let ast := s.ast.setObjVal! "init" (.arr init)
  let names := (layout.bodies ++ layout.signatures).filterMap fun j => p.index.units[j]?.map (·.1.name)
  let names := (reads ++ names).eraseDups
  let (imports, established, tables) := GroupProjection.groupEnvironment names s.imports s.established s.tables
  let code := Json.arr #[ast.getObjValD "functions", .arr init, toJson (env.origins.toList.filterMap id)]
  let index ← IO.ofExcept p.declarations.get
  -- The original lowering may expose an implicit module value because of
  -- an initializer statement. Its presence fixes the reader's frame slots.
  let original := s.ast.getObjValD "declarations"
  let captured := ((original.getObjValAs? (List Json) "values").toOption.getD []).filterMap fun v =>
    ((v.getObjValD "binding").getObjValAs? String "local").toOption
  let readBuiltins := ((original.getObjValAs? (List Json) "definitions").toOption.getD []).any fun d =>
    EquationLowering.ImplicitDependency.arrayProto.selects (d.getObjValD "declaration")
  let (declarations, missing) := index.slice code names readBuiltins captured
  return {s with
    ast := ast.setObjVal! "declarations" declarations
    imports, established, tables, missing, bindings := some env}

/-- Resolve a group against the driver's store. Only the result uses the
reply channel. The occurrence map belongs to this worker's preparation. -/
private def resolveSlice (p : PreparedFile) (i : Nat) (below : GroupAnswers)
    (check : Bool) : IO (Option String × GroupAnswers) := do
  let unit := p.unitId i
  let returnedBelow ← p.inheritedReturn i
  let physical ← IO.ofExcept (p.sliceInput i (p.needsInterface i) below returnedBelow)
  let candidate ← bindingSlice p physical i
  let ⟨slice, sites, prepared, input⟩ ← IO.ofExcept <| SinglePass.work "slice: project" unit fun _ => show Except String ((s : GroupProjection.Slice) × GroupProjection.Sites × Option (PreparedSliceFront s) × String) from do
    if candidate.bindings.isSome then
      if let .ok (s, sites) := candidate.relative p.declarationSites.get then
        match h : sliceFront s with
        | .ok front => return ⟨s, sites, some ⟨front, h⟩, s.wire⟩
        | .error _ => pure ()
    let (s, sites) ← physical.relative p.declarationSites.get
    return ⟨s, sites, none, s.wire⟩
  IO.FS.writeFile "slice-input" input
  -- A dependency outside this request can consume a completed check's
  -- answers. On a miss it needs only the proposal operation.
  let full ← sliceLookup (if check then "check-slice" else "probe-check-slice")
  let (operation, replyBytes, stored) ← if !check && full.2.isNull then do
      printFlushed "slice-skip"
      pure ("propose-slice", ← sliceLookup "propose-slice")
    else pure ("check-slice", full)
  let (operation, stored) := if operation == "propose-slice" && (stored.getObjVal? "checked").isOk then
    ("check-slice", stored.getObjValD "checked") else (operation, stored)
  let resume := operation == "check-slice" && (stored.getObjVal? "resume").isOk
  let stored := if resume then stored.getObjValD "resume" else stored
  if resume then do
      let _ ← IO.ofExcept (readSliceResult p i slice sites "propose-slice" stored)
      pure ()
  let fresh := stored.isNull || resume
  let (payload, published) ← if !fresh then pure (stored, "") else
    IO.ofExcept (← IO.lazyPure fun _ => SinglePass.work "slice: execute" unit fun _ =>
      sliceResult slice (operation == "check-slice") (if resume then some replyBytes else none) prepared)
  if resume && payload.getObjValD "answers" != stored.getObjValD "answers" then
    throw (IO.userError "the resumed plan changed its proposal")
  let mut diagnostic : Except String SourceClaimJson.FilePlans := .error "missing diagnostic plan"
  if check then
    if let .ok raw := payload.getObjValAs? String "line" >>= Json.parse then
      let failure := (raw.getObjValAs? GroupProjection.StoredFailure "refusal").toOption
      if failure.any (·.readsPlan) || (raw.getObjValAs? SourceClaimJson.UnitRef "elaboration").isOk then
        let answers ← IO.ofExcept (GroupProjection.decodeAnswers (payload.getObjValD "answers"))
        diagnostic := (← p.diagnosticPlan i answers).bind (·.planned)
  let result ← IO.ofExcept (← IO.lazyPure fun _ =>
    SinglePass.work (if fresh then "slice: render" else "slice: replay") unit fun _ =>
      readSliceResult p i slice sites operation payload check diagnostic)
  printFlushed (if fresh then "slice-result " ++ published else "slice-hit")
  return result

private def checkWithStore (p : PreparedFile) (i : Nat)
    (lines : IO.Ref (Std.HashMap Nat String)) : IO String := do
  let answered ← p.proposals.get
  let deps := p.fr.dependencies (p.fr.group i)
  for g in orderedGroups p.fr deps {} answered.contains ++ [i] do
    if g == i then
      if (← lines.get).contains g then continue
    else if (← p.proposals.get).contains g then continue
    let (line, answers) ← resolveSlice p g (← p.lowerAnswers (p.layout g).answerGroups) (g == i)
    p.recordAnswers g answers
    if let some line := line then lines.modify (·.insert g line)
  let some line := (← lines.get).get? i | throw (IO.userError "missing requested slice verdict")
  return line

/-- Mode 8, the single pass, over a file's fragment and the module
interfaces its imports read (`--verify-interface-stage 8`): the file prepared
once (`prepareUnitsFile`), then each selected unit's group checked in turn
(`PreparedFile.check`), its types computed by the walk, every loop head's
proposal inferred (`HeadInference`); each unit's verdict on a line
`{"unit","members","accepted","depends"}` or `{"unit","members","refusal"}`,
flushed as its check ends. -/
def verifyUnitsFile (astPath : String) (fileKey : String) (fuel : Nat) (names : Option String)
    (budget : PositiveCertificates.SearchBudget) (interfacesPath : String) (quiet : Bool := false)
    (force : List String := []) : IO UInt32 := do
  match ← prepareUnitsFile astPath fileKey fuel names budget interfacesPath quiet (force := force) with
  | .error e => refuse e
  | .ok p =>
    let mut refused : Option String := none
    let mut elaboration : Option String := none
    for u in p.modules do printFlushed (WorkerWire.verdictLine u [u] (.ok []) none [])
    for i in p.units do
      let (line, refusal) ← p.check i
      printFlushed line
      if refused.isNone then refused := refusal
      if elaboration.isNone then
        elaboration := (WorkerWire.lineElaboration line).toOption.join
    match elaboration with
    | some reason => refuse reason
    | none =>
      match refused with
      | some reason => refuse reason
      | none =>
        IO.println s!"accept: stateful source {fileKey}"
        return 0

/-- The work table, where profiling, written as `work.jsonl` whole, by a
rename: a reader of the file sees the table as of a finished unit. -/
def writeWorkNow (start : Nat) : IO Unit := do
  if !(← SinglePass.profiling.get) then return
  writeWork start "work.jsonl.next"
  IO.FS.rename "work.jsonl.next" "work.jsonl"

/-- **The file worker** (`--file-worker 8`, docs/REQUEST-PROTOCOL.md, "The
file worker"): the file prepared once (`prepareUnitsFile`), its preparation's
line printed (`WorkerWire.preparedLine`: the selected units with their
members, the established module units, the elaboration refusal), then, for
each request line read from standard input (`WorkerWire.decodeRequest`: the
units to check, `null` for every selected unit), each named unit checked
(`PreparedFile.check`) and its verdict line printed and flushed as its check
ends, until standard input ends. A refusal of the preparation is the
command's refusal, before any line. -/
def fileWorker (astPath : String) (fileKey : String) (fuel : Nat) (names : Option String)
    (budget : PositiveCertificates.SearchBudget) (interfacesPath : String) (start : Nat)
    (force : List String := []) : IO UInt32 := do
  match ← prepareUnitsFile astPath fileKey fuel names budget interfacesPath true (force := force) with
  | .error e => refuse e
  | .ok p =>
    let units := p.units
    let fr := p.fr
    let byId := Std.HashMap.ofList (units.map fun j => (p.unitId j, j))
    writeWorkNow start
    printFlushed (WorkerWire.preparedLine (units.map fun i => (p.unitId i, (fr.group i).map p.unitId)) p.modules)
    let stdin ← IO.getStdin
    let store := (← IO.getEnv "TSCERT_SLICE_DRIVER") == some "1"
    let lines ← IO.mkRef {}
    repeat
      let text ← stdin.getLine
      if text.isEmpty then break
      match WorkerWire.decodeRequest text with
      | .error e => throw (IO.userError s!"file worker: {e}")
      | .ok requested =>
        let chosen ← match requested with
          | none => pure units
          | some ids => ids.mapM fun id => match byId.get? id with
            | some i => pure i
            | none => throw (IO.userError s!"file worker: {id} is no unit the selection checks")
        let order := if store then SinglePass.work "slice: schedule" (SourceClaimJson.fileItem p.ast)
          (fun _ => requestedOrder fr chosen) else chosen
        if store then printFlushed ("slice-order " ++ (toJson (order.map p.unitId)).compress)
        for i in order do
          let line ← if store then checkWithStore p i lines else Prod.fst <$> p.check i
          writeWorkNow start
          printFlushed (if store then "slice-verdict " ++ line else line)
    return 0

end Verification.RequestCli
