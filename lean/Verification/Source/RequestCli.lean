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
  let initMentions := init.flatMap SourceElaboration.stmtNames
  let mentions := fun (n : String) => if n == ":init" then initMentions else
    (fns.filter (·.name == n)).flatMap fun f => f.body.flatMap SourceElaboration.stmtNames
  let names := fns.map (·.name)
  let mut set := roots.eraseDups
  for _ in List.range (fns.length + 2) do
    let ms := set.flatMap mentions
    let next := (set ++ names.filter ms.contains ++ (if !init.isEmpty && ms.any owned.contains then [":init"] else [])).eraseDups
    if next.length == set.length then break
    set := next
  return set

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

/-- File selection, shared preparation and the results retained by this worker. -/
structure PreparedFile extends GroupContext where
  imports : Thunk (Except String SourceClaimJson.PlanImports)
  fronts : IO.Ref (List (SourceClaimJson.PlanningFront force))
  modules : List String
  selected : Option (List String)
  /-- Groups whose interface another reachable group consumes. -/
  interfaceDemand : Std.HashSet Nat
  quiet : Bool
  t0 : Nat
  proposals : IO.Ref (Std.HashMap Nat GroupAnswers)
  plans : IO.Ref (Std.HashMap Nat PlannedGroup)

/-- The prepared file's front: its units, their identities and groups. -/
def GroupContext.fr (p : GroupContext) : SourceClaimJson.Front := p.front.2

/-- Interface demand of one prepared selection, using the existing group
dependency graph. Every reachable group is queued once. An incomplete walk
conservatively demands every group. -/
def demandedInterfaces (fr : SourceClaimJson.Front) (wanted : List Nat) : Std.HashSet Nat := Id.run do
  let mut pending := wanted.eraseDups
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
  let tj ← IO.monoNanosNow
  -- The interfaces decoded, and the file's claims and front.
  let prepared : Except String (SourceClaimJson.Established × List (String × SourceClaimJson.RowTable) ×
      (Json × SourceClaimJson.Front) × Json) ← IO.lazyPure fun _ => do
    let cached ← interfaces
    let sc ← if (← jArr cached "modules").isEmpty then
        pure (⟨[], {}⟩ : SourceClaimJson.ImportScope)
      else SourceClaimJson.ImportScope.of (← ast)
    let a ← ast
    let item := SourceClaimJson.fileItem a
    let (est, tables) ← SinglePass.work "rows: decode interfaces" item fun _ => SourceClaimJson.decodeInterfaces sc cached
    -- (as `fragmentPlansCore` lowers a file: its module documents apart)
    let a' := a.setObjVal! "modules" (Json.arr #[])
    let claims ← SinglePass.work "prepare: claims" item fun _ => SourceClaimJson.fragmentClaims a' fileKey {} force
    let fr ← SinglePass.work "prepare: file lowering" item fun _ =>
      SourceClaimJson.fileFront a' claims fileKey budget [] (lenient := true)
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
  let proposals ← IO.mkRef {}
  let plans ← IO.mkRef {}
  let fronts ← IO.mkRef []
  return prepared.map fun (est, tables, front, a) =>
    { ast := a, imports := Thunk.mk fun _ => SourceClaimJson.planImports a, fileKey, budget, est, tables, front, fronts, modules := (est.map (·.2.2)).eraseDups, selected,
      interfaceDemand := demandedInterfaces front.2 (front.2.selected selected), force,
      givenLines, fuel, quiet, t0, proposals, plans }

/-- The units a prepared file's selection checks, in the order their checks
run: the leaders of the groups the selection names (`Front.selected`). -/
def PreparedFile.units (p : PreparedFile) : List Nat := p.fr.selected p.selected

/-- Named empty answers suppress inference for these members. -/
def GroupContext.emptyAnswers (p : GroupContext) (i : Nat) : GroupAnswers :=
  (p.fr.group i).filterMap fun j => match p.fr.units[j]? with
    | some (f, _, none) => some (f.name, none)
    | _ => none

/-- The worker shares initialization typing across groups reading the same
ordered qualified effects. The file, lowered front and force are fixed. -/
def PreparedFile.frontAt (p : PreparedFile) (imports : SourceClaimJson.GroupImports) :
    IO (SourceClaimJson.PlanningFront p.force) := do
  if let some f := (← p.fronts.get).find? (·.qualified == imports.qualified) then return f
  let f : SourceClaimJson.PlanningFront p.force :=
    { claims := p.front.1, raw := p.fr, qualified := imports.qualified }
  return f

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
      f.passGroupMode8 true p.force (f.givenAt p.givenLines) p.fuel (f.fr.group i) (counting := counting) (located := true)
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

/-- Supply this group's current import reads and their shared front. -/
def PreparedFile.plan (p : PreparedFile) (i : Nat) (demand : Bool) (below : GroupAnswers) : IO PlannedGroup := do
  let names := some [SourceClaimJson.memberName (p.fr.unitId i)]
  let reads ← IO.lazyPure fun _ => SourceClaimJson.groupImports p.imports.get p.ast names {} p.est
  let inputs ← match reads with
    | .error reason => pure (.error reason)
    | .ok imports => pure (.ok (imports, ← p.frontAt imports))
  let (group, updated) ← IO.lazyPure fun _ => p.groupOperation i demand below inputs
  if let some f := updated then
    p.fronts.modify fun fs => f :: fs.filter (·.qualified != f.qualified)
  return group

/-- The groups a group reaches outside itself, by their first members,
each after those it reaches (`Front.edges` over the groups). -/
def groupsBelow (fr : SourceClaimJson.Front) (i : Nat) : List Nat := Id.run do
  let leader := fun (j : Nat) => ((fr.group j).head?).getD j
  let mut order : List Nat := []
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert (leader i)
  let mut stack : List (Nat × Bool) := ((fr.group i).flatMap fr.edges).map (leader ·, false)
  for _ in List.range (4 * fr.units.length * (fr.units.length + 1) + 4) do
    match stack with
    | [] => break
    | (g, true) :: rest => stack := rest; order := order ++ [g]
    | (g, false) :: rest =>
      if seen.contains g then stack := rest
      else
        seen := seen.insert g
        stack := ((fr.group g).flatMap fr.edges).map (leader ·, false) |>.filter (!seen.contains ·.1)
          |>.append ((g, true) :: rest)
  return order

/-- Whether this worker may consume a group's inferred interface: from
another selected group, recursive members, or an explicit effect contract.
Module-interface publication uses its own planner and still infers its rows. -/
def PreparedFile.needsInterface (p : PreparedFile) (i : Nat) : Bool :=
  let group := p.fr.group i
  let own := group.filterMap fun j => (p.fr.units[j]?).map (·.1.name)
  !p.force.isEmpty || p.interfaceDemand.contains i ||
    group.any (fun j => (p.fr.mentions j).any own.contains ||
      ((p.fr.units[j]?).any fun (f, _, _) => f.stated.isSome))

/-- Every lower group has answered when its caller is planned. A named
empty answer and a group with no function answers are both completed reads. -/
def PreparedFile.lowerAnswers (p : PreparedFile) (groups : List Nat) : IO GroupAnswers := do
  let answers ← p.proposals.get
  let values ← groups.mapM fun g => match answers.get? g with
    | some value => pure value
    | none => throw (IO.userError s!"file worker: missing proposals for {p.fr.unitId g}")
  return values.flatten

/-- **The proposals unit `i`'s planning reads**: for each group `i`'s group
reaches outside itself (`groupsBelow`, callees first), its members'
proposals as that group's own planning gives them (`PreparedFile.plan`,
`FilePlans.groupProposals`), each group's computed once in the worker and
kept (`PreparedFile.proposals`). A group's proposals are a function of the
file and of the group: they read only the proposals of the groups below
it, and a member of a group of two or more functions reads the others at
their written effect or `top` (`PassProposals.proposeOne`), so they do not
depend on the units checked before. -/
def PreparedFile.known (p : PreparedFile) (i : Nat) : IO (List (String × Option SourceClaimJson.StandIn)) := do
  let fr := p.fr
  let below := groupsBelow fr i
  for g in below do
    if (← p.proposals.get).contains g then continue
    let known ← p.lowerAnswers (groupsBelow fr g)
    let group ← p.plan g (p.needsInterface g) known
    if p.units.contains g then p.plans.modify (·.insert g group)
    p.proposals.modify (·.insert g group.answers)
  p.lowerAnswers below

/-- Unit `i`'s check: its group planned in its check (`PreparedFile.plan`,
the proposals below it read through `PreparedFile.known`; the plans an
earlier unit's proposals planned it at, where kept, then released), then
`FilePlans.passGroupMode8` over its group: its verdict line
(`WorkerWire.verdictLine`), accepted with its dependencies or refused, with
its group's first elaboration refusal; and its refusal. A function of the
prepared file and `i`. -/
def PreparedFile.check (p : PreparedFile) (i : Nat) : IO (String × Option String) := do
  let emit := fun (s : String) => if p.quiet then pure () else IO.eprintln s
  let fr := p.fr
  let unit := fr.unitId i
  let s0 ← IO.monoNanosNow
  let p0 ← SinglePass.passNanos.get
  let compare := (← IO.getEnv "TSCERT_COMPARE").isSome
  let debugNode := ((← IO.getEnv "TSCERT_NODE").bind String.toNat?).getD 1000000000
  let repeats := ((← IO.getEnv "TSCERT_REPEAT").bind String.toNat?).getD 1
  -- Observing: the state at `TSCERT_OBSERVE` (`node:L` or `offset:K`).
  let observe ← IO.getEnv "TSCERT_OBSERVE"
  -- The pass's counts as JSON lines (`TSCERT_COUNTS`, `dev/perf-gate.mts`).
  let counting := (← IO.getEnv "TSCERT_COUNTS").isSome
  let group ← match (← p.plans.get).get? i with
    | some group => do p.plans.modify (·.erase i); pure group
    | none => do
      let below ← p.known i
      let group ← p.plan i (p.needsInterface i) below
      p.proposals.modify (·.insert i group.answers)
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
      let (diagnostics, observed, _, _) ← IO.lazyPure fun _ =>
        f.passGroupMode8 true p.force (f.givenAt p.givenLines) p.fuel (fr.group i)
          compare debugNode repeats none observe counting (!raw)
      for line in diagnostics do IO.eprintln line
      if raw then
        if let .error reason := observed then IO.eprintln reason
  let result ← IO.lazyPure fun _ => group.verdict counting
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
    writeWorkNow start
    printFlushed (WorkerWire.preparedLine (units.map fun i => (fr.unitId i, (fr.group i).map fr.unitId)) p.modules)
    let stdin ← IO.getStdin
    repeat
      let text ← stdin.getLine
      if text.isEmpty then break
      match WorkerWire.decodeRequest text with
      | .error e => throw (IO.userError s!"file worker: {e}")
      | .ok requested =>
        let chosen ← match requested with
          | none => pure units
          | some ids => ids.mapM fun id => match units.find? (fr.unitId · == id) with
            | some i => pure i
            | none => throw (IO.userError s!"file worker: {id} is no unit the selection checks")
        for i in chosen do
          let (line, _) ← p.check i
          writeWorkNow start
          printFlushed line
    return 0

end Verification.RequestCli
