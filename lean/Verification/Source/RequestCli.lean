import Verification.Source.FlowJson
-- FlowJson.lean supplies the claim-independent graphs the producer analyzes.
import Verification.Source.Claims.Json
-- Claims/Translate.lean writes a slice's evidence over its document's store, untrusted.
import Verification.Source.Claims.Translate
-- Claims/TypeComparison.lean compares computed types with the claims (mode 7, a measurement).
import Verification.Source.Claims.TypeComparison
-- Claims/FragmentFront.lean lowers a file's units from its fragment alone (mode 8).
import Verification.Source.Claims.ModuleInterfaces

/-! File interface to the source adapter. Source parsing remains external;
checking reconstructs each unit's request from the fragment and its claims. -/
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
    rw [surrogateEscapeFrom]; simp only [hi, if_true, Bool.or_eq_true]
    rcases Nat.lt_or_eq_of_le hij with hlt | heq
    · exact Or.inr (ih (by omega))
    · subst heq; exact Or.inl h
  | case2 i hi => omega

theorem byteIs_toByteArray {l : List UInt8} {i : Nat} {v : UInt8} :
    byteIs l.toByteArray i v = (l[i]? == some v) := by
  unfold byteIs
  by_cases hi : i < l.length
  · simp [hi, List.getElem_toByteArray]
  · simp [hi]

theorem start_bytes {cs : List Char} (h : SurrogateStart cs) :
    ∃ j, surrogateEscapeAt cs.utf8Encode j = true := by
  obtain ⟨pre, x, post, rfl, hx⟩ := h
  refine ⟨(pre.flatMap String.utf8EncodeChar).length, ?_⟩
  have hb : String.utf8EncodeChar '\\' = [92] := rfl
  have hu : String.utf8EncodeChar 'u' = [117] := rfl
  simp only [surrogateEscapeAt, List.utf8Encode, byteIs_toByteArray]
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
  return Json.parse text

/-- Export the same execution graph constructor used by typed extraction. -/
def flowFile (astPath : String) : IO UInt32 := do
  let ast ← readJson astPath
  match ast >>= SourceFlow.document with
  | .ok graph => IO.println graph.compress; return 0
  | .error reason => refuse reason

/-- Print the program graph each unit lowers to (`SourceClaimJson.lowerJson`). -/
def lowerFile (astPath claimsPath fileKey : String) : IO UInt32 := do
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match do SourceClaimJson.lowerJson (← ast) (← claims) fileKey with
  | .ok j => IO.println j.compress; return 0
  | .error e => refuse e

/-- The certified imports a document's claims plan (`SourceClaimJson.planImports`):
silent where the plan holds; a plan refused is a refusal, with each other read
it refuses on a line of its own. Plan output is never a source acceptance or
an evidence file. -/
def planFile (astPath claimsPath : String) : IO UInt32 := do
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match do SourceClaimJson.planImports (← ast) (← claims) with
  | .ok _ => return 0
  | .error e =>
    -- The plan's first refusal, then each other read it refuses, a line
    -- each, so the pipeline withdraws them in one round.
    let others := match do SourceClaimJson.planRefusals (← ast) (← claims) with
      | .ok rs => rs.filter (· != e)
      | .error _ => []
    refuse ("\n".intercalate (e :: others))

/-- A selection of units by their members' names, comma-separated; every
unit without one. -/
def selection : Option String → Option (List String)
  | none => none
  | some names => some ((names.splitOn ",").filter (· != ""))

/-- Search evidence for a unit's slice (`SourceClaimJson.slicePlans`): the
selected groups' evidence written to `evidencePath` a line per unit, each
with the heads of the slice's store its labels name
(`SourceClaimJson.sliceLine`); each unit the search refuses on a line
`refused: {"unit","refusal"}`; each unit's candidate search on a line
`candidates: {"unit","passes","mostPasses","leftOut"}`. Untrusted: the check translates the evidence
to the document's store and checks it there. -/
def produceUnitFile (slicePath claimsPath qualifiedPath evidencePath : String) (fuel : Nat) (names : Option String)
    (budget : PositiveCertificates.SearchBudget := {}) : IO UInt32 := do
  if evidencePath == slicePath || evidencePath == claimsPath || evidencePath == qualifiedPath then
    return ← refuse "evidence output must differ from the input files"
  let ast ← readJson slicePath
  let claims ← readJson claimsPath
  let qualified ← readJson qualifiedPath
  match do
      let ast ← ast
      SourceClaimJson.slicePlans ast (← claims) (← qualified) (← jStr (← jField ast "file")) budget with
  | .error e => refuse e
  | .ok f =>
    let refusals ← IO.FS.withFile evidencePath .write fun h => do
      let mut refusals : Array (String × String) := #[]
      for i in f.fr.selected (selection names) do
        let unit := f.fr.unitId i
        let (evidence, refusal, passes, most, leftOut) := f.produceGroup fuel (f.fr.group i)
        h.putStrLn (SourceClaimJson.sliceLine unit evidence f.F.store.heads (f.anchors (f.fr.group i) (claims := false))).compress
        IO.println s!"candidates: {(Json.mkObj [("unit", toJson unit), ("passes", toJson passes),
          ("mostPasses", toJson most), ("leftOut", toJson leftOut)]).compress}"
        if let some reason := refusal then refusals := refusals.push (unit, reason)
      return refusals
    IO.println s!"checked source evidence written: {evidencePath}"
    for (unit, reason) in refusals do
      IO.println s!"refused: {(Json.mkObj [("unit", toJson unit), ("refusal", toJson reason)]).compress}"
    match refusals.toList with
    | [] => return 0
    | (_, reason) :: _ => refuse reason

/-- Each line of the file at `path`, its bytes without the line feed, in
order, read a block at a time: a line is held only while `each` reads it. -/
partial def forEachLine (path : String) (each : ByteArray → IO Unit) : IO Unit :=
  IO.FS.withFile path .read fun h => do
    let rec go (pending : ByteArray) : IO Unit := do
      let block ← h.read 1048576
      if block.isEmpty then
        if !pending.isEmpty then each pending
        return
      let mut line := pending
      let mut start := 0
      for i in [0:block.size] do
        if block[i]! == 10 then
          each (line ++ block.extract start i)
          line := ByteArray.empty
          start := i + 1
      go (line ++ block.extract start block.size)
    go ByteArray.empty

/-- A line of an evidence document read as `readJson` reads a document. -/
def lineJson (bytes : ByteArray) : Except String Json := do
  let some text := String.fromUTF8? bytes
    | throw "evidence: a text that is not valid UTF-8 is refused"
  if let some what := wireSurrogate text then
    throw s!"evidence: a string that is not well-formed Unicode, {what}, is refused"
  Json.parse text

/-- Check a file's selected units over its one front
(`SourceClaimJson.filePlans`), each at the evidence its line gives
(`SourceClaimJson.checkedUnit`), a line of the evidence held only while it is
checked: each unit's verdict on a line, `{"unit","members","accepted","depends"}`
or `{"unit","members","refusal"}`, whose acceptance `checkUnitJson_safe`
states; a selected unit no line gives is refused. Any refused, the command's
refusal is the first the check meets: a selected unit's extraction, then a
line's or a unit's, in the evidence's order. -/
def checkUnitsFile (astPath claimsPath fileKey evidencePath : String) (names : Option String)
    (budget : PositiveCertificates.SearchBudget := {}) : IO UInt32 := do
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match do SourceClaimJson.filePlans (← ast) (← claims) fileKey budget with
  | .error e => refuse e
  | .ok f =>
    let wanted := (f.fr.selected (selection names)).map (fun i => (f.fr.unitId i, (f.fr.group i).map f.fr.unitId))
    let print (unit : String) (members : List String) (verdict : Except String (List String)) : IO Unit :=
      IO.println (match verdict with
        | .ok deps => Json.mkObj [("unit", toJson unit), ("members", toJson members), ("accepted", toJson true),
            ("depends", toJson deps)]
        | .error reason => Json.mkObj [("unit", toJson unit), ("members", toJson members),
            ("refusal", toJson reason)]).compress
    let target ← IO.mkRef (SourceClaimJson.Translate.Target.of f.F.store.heads)
    let seen ← IO.mkRef ({} : Std.HashSet String)
    let refused ← IO.mkRef (none : Option String)
    let note (reason : String) : IO Unit := refused.modify (·.orElse fun _ => some reason)
    forEachLine evidencePath fun bytes => do
      match lineJson bytes >>= SourceClaimJson.readLine with
      | .error reason => note reason
      | .ok (unit, evidence, heads) =>
        if let some (_, members) := wanted.find? (·.1 == unit) then
          let (verdict, next) := SourceClaimJson.checkedUnit f budget (← target.get) unit evidence heads
          target.set next
          print unit members verdict
          seen.modify (·.insert unit)
          if let .error reason := verdict then note reason
    let seen ← seen.get
    for (unit, members) in wanted do
      if !seen.contains unit then
        let reason := s!"no evidence for unit {unit}"
        print unit members (.error reason)
        note reason
    match f.extractionRefusal (selection names) with
    | some reason => refuse reason
    | none =>
      match ← refused.get with
      | some reason => refuse reason
      | none =>
        IO.println s!"accept: stateful source {fileKey}"
        return 0

/-- The given lines of a module's units, by their identity in the module:
each line of a unit `module:<location>#<unit>`. -/
def forModule (location : String) (given : Std.HashMap String Json) : Std.HashMap String Json :=
  let pre := s!"module:{location}#"
  given.fold (init := {}) fun m k v => if k.startsWith pre then m.insert (k.drop pre.length).toString v else m

/-- A module's given lines a pass reads (`FilePlans.passGroup`): those stating
a graph, by the unit's identity in the module whose document is `ast`. -/
def moduleGiven (ast : Json) (given : Std.HashMap String Json) : Std.HashMap String Json :=
  let location := (ast.getObjValAs? String "file").toOption.getD ""
  (forModule location given).fold (init := {}) fun m k v => if (v.getObjVal? "graph").isOk then m.insert k v else m

/-- Discovery binds both the fragment and its requested roots. -/
def interfacePlanFile (path selection : String) : IO UInt32 := do
  let ast ← readJson path
  let selected ← readJson selection
  match (do SourceClaimJson.interfacePlan (← ast) (← selected)) with
  | .error e => refuse e
  | .ok j => IO.println j.compress; return 0

/-- A complete canonical component check. All semantic inputs are in its
request; no environment-supplied stand-ins or evidence enter this check. -/
def interfaceFile (path : String) (budget : PositiveCertificates.SearchBudget) : IO UInt32 := do
  let request ← readJson path
  let parsed : Except String Json := do
    let j ← request
    fieldsExactly j ["modules", "dependencies", "given", "force", "allCuts", "fuel", "mode"]
    let modules ← (← jArr j "modules").mapM Fragment.decodeModule
    let ds ← jArr j "dependencies"
    let mut imported : List Fragment.ModuleAst := []
    for d in ds do
      fieldsExactly d ["key", "interface"]
      let _ ← d.getObjValAs? String "key"
      let i ← jField d "interface"
      fieldsExactly i ["modules"]
      for row in ← jArr i "modules" do
        let m ← Fragment.decodeModule (← jField row "module")
        if modules.any (·.location == m.location) || imported.any (·.location == m.location) then
          throw "component dependency overlaps"
        imported := imported ++ [m]
    let sc : SourceClaimJson.ImportScope := ⟨modules ++ imported, SourceClaimJson.ModuleCode.of (modules ++ imported)⟩
    let incoming ← ds.flatMapM fun (d : Json) => do
      return (← SourceClaimJson.decodeInterfaces sc (d.getObjValD "interface")).1
    let needs ← SourceClaimJson.interfaceNeeds sc
    let own := needs.filter fun (n : SourceClaimJson.ModuleNeed) => modules.any (·.location == n.module.location)
    let mut given : Std.HashMap String Json := {}
    for line in ← jArr j "given" do
      let u ← line.getObjValAs? String "unit"
      if !modules.any (fun m => u.startsWith s!"module:{m.location}#") then throw "foreign given identity"
      if given.contains u then throw "duplicate given identity"
      given := given.insert u line
    let force : List String ← fromJson? (← jField j "force")
    let allCuts ← j.getObjValAs? Bool "allCuts"
    let fuel ← j.getObjValAs? Nat "fuel"
    let mode ← j.getObjValAs? Nat "mode"
    if mode != 8 && mode != 9 then throw "interface mode must be 8 or 9"
    let prepare := fun location (f : SourceClaimJson.FilePlans) =>
      let f := f.withHeadFacts (forModule location given) (mode == 9)
      if mode == 9 && !allCuts then f.headCuts else f
    let check := fun (f : SourceClaimJson.FilePlans) group =>
      if mode == 9 then (([] : List String), f.verifyGroup fuel group false)
      else f.passGroup fuel group (given := some (moduleGiven f.fr.ast given))
    let (est, _, _, tables) ← SourceClaimJson.establishModules
      (own.mergeSort (fun a b => a.module.location ≤ b.module.location)) budget force incoming prepare check
    SourceClaimJson.encodeInterfaces modules est tables
  match parsed with
  | .error e => refuse e
  | .ok j => IO.println j.compress; return 0

/-- Search and check a file's selected units over its one front
(`SourceClaimJson.filePlans`) in one process: each group's evidence searched
over the file's own store (`FilePlans.produceGroup`) and checked there
(`SourceClaimJson.unitVerdict`), no evidence written. Each unit's verdict on
a line, as `--check-units` prints it. -/
def verifyUnitsFile (astPath : String) (claimsPath : Option String) (fileKey : String) (fuel : Nat)
    (names : Option String) (mode : Nat)
    (budget : PositiveCertificates.SearchBudget := {}) (interfacesPath : Option String := none)
    (givenPath : Option String := none) (standPath : Option String := none) (quiet : Bool := false) : IO UInt32 := do
  let emit := fun (s : String) => if quiet then pure () else IO.eprintln s
  -- Per-kind timings only where asked (`TSCERT_PROFILE`).
  SinglePass.profiling.set (← IO.getEnv "TSCERT_PROFILE").isSome
  let t0 ← IO.monoNanosNow
  let ast ← readJson astPath
  -- Mode 8 reads no claims document.
  let claims ← match claimsPath with
    | some p => readJson p
    | none => pure (.error "no claims document")
  -- Mode 8's written-footprint stand-ins (`TSCERT_STANDINS`), a measurement aid.
  let envStand ← IO.getEnv "TSCERT_STANDINS"
  let standInsPath := standPath.orElse fun _ => envStand.filter (!·.isEmpty)
  let envGiven ← IO.getEnv "TSCERT_GIVEN"
  let suppliedGiven := givenPath.orElse fun _ => envGiven
  let standIns : Except String SourceClaimJson.StandIns ← match standInsPath with
    | some p => do pure ((← readJson p) >>= fromJson?)
    | none => pure (.ok {})
  -- The given file's lines (`TSCERT_GIVEN`), for modes 8 and 9's plans: the
  -- selected file's units' by unit, and a module unit's (`module:…`) kept
  -- as text, read where its module's groups are checked (`moduleLines`).
  let givenText : List String ← match suppliedGiven with
    | none => pure []
    | some path => do
      let text ← try IO.FS.readFile path catch _ => pure ""
      pure ((text.splitOn "\n").filter (!·.isEmpty))
  let moduleLine := fun (l : String) => (l.splitOn "\"unit\":\"module:").length > 1
  let givenLines : Std.HashMap String Json := (givenText.filter (!moduleLine ·)).foldl
    (fun (m : Std.HashMap String Json) l => match Json.parse l with
      | .ok j => match j.getObjValAs? String "unit" with
        | .ok u => m.insert u j
        | .error _ => m
      | .error _ => m) {}
  let moduleText := givenText.filter moduleLine
  -- A module's given lines, by unit: those naming it, parsed.
  let moduleLines := fun (location : String) =>
    let pre := s!"\"unit\":\"module:{location}#"
    (moduleText.filter fun l => (l.splitOn pre).length > 1).foldl (fun (m : Std.HashMap String Json) l =>
      match Json.parse l with
      | .ok j => match j.getObjValAs? String "unit" with
        | .ok u => m.insert u j
        | .error _ => m
      | .error _ => m) {}
  -- Adversarial proposals forced, for the referee (`TSCERT_FORCE`, comma-separated).
  let force := ((← IO.getEnv "TSCERT_FORCE").getD "").splitOn "," |>.filter (!·.isEmpty)
  -- The referee's statement entries all the search's cuts (`TSCERT_ALL_CUTS`).
  let allCuts := (← IO.getEnv "TSCERT_ALL_CUTS").isSome
  let interfaces ← match interfacesPath with
    | none => pure (none : Option (Except String Json))
    | some p => pure (some (← readJson p))
  let tj ← IO.monoNanosNow
  -- The single pass (mode 3) reads what the selected units' groups read.
  let planned : Except String (SourceClaimJson.FilePlans × List SourceClaimJson.ModuleVerdict × List String) ← IO.lazyPure fun _ => do
    if mode == 3 || mode == 7 then
      (·, ([] : List SourceClaimJson.ModuleVerdict), ([] : List String)) <$> SourceClaimJson.unitPlans (← ast) (← claims) fileKey budget (selection names)
    -- Mode 8: the single pass over the fragment alone, each unit's types
    -- computed by the walk (`SourceClaimJson.fragmentPlans`).
    -- Mode 9: the search and the proved check over the same plans, the
    -- referee of mode 8's verdicts. Both take the loop heads' facts from the
    -- given file.
    else if mode == 8 || mode == 9 then
      let prepare := fun (given : Std.HashMap String Json) (f : SourceClaimJson.FilePlans) =>
        let f := f.withHeadFacts given (mode == 9)
        let f := if force.contains "start-facts" then f.withFalseStartFact else f
        if mode == 9 && !allCuts then f.headCuts else f
      -- The module units an import's footprint rests on, checked here by the
      -- same mode (`fragmentPlansWithModules`), each at the given lines of
      -- its wire identity (`module:<location>#<unit>`).
      let check := fun (f : SourceClaimJson.FilePlans) (group : List Nat) =>
        if mode == 9 then (([] : List String), f.verifyGroup fuel group false)
        else f.passGroup fuel group (given := some (moduleGiven f.fr.ast
          (moduleLines ((f.fr.ast.getObjValAs? String "file").toOption.getD ""))))
      if let some cached := interfaces then
        let cached ← cached
        let sc ← if (← jArr cached "modules").isEmpty then
            pure (⟨[], {}⟩ : SourceClaimJson.ImportScope)
          else SourceClaimJson.ImportScope.of (← ast)
        let (est, tables) ← SourceClaimJson.decodeInterfaces sc cached
        let f ← SourceClaimJson.fragmentPlansFromInterfaces (← ast) fileKey budget (selection names) (← standIns) force est tables
        let ms : List SourceClaimJson.ModuleVerdict := (est.map (·.2.2)).eraseDups.map fun u =>
          ⟨u, [u], [], .ok []⟩
        return (prepare givenLines f, ms, [])
      let (f, ms, notes) ← SourceClaimJson.fragmentPlansWithModules (← ast) fileKey budget (selection names) (← standIns) force
        (fun location => prepare (forModule location (moduleLines location))) check
      pure (prepare givenLines f, ms, notes)
    else (·, ([] : List SourceClaimJson.ModuleVerdict), ([] : List String)) <$> SourceClaimJson.filePlans (← ast) (← claims) fileKey budget
  let t1 ← IO.monoNanosNow
  let ms := fun (a b : Nat) => s!"{(b - a) / 1000000}"
  let phases := (← SinglePass.kindNanos.get).toList.filter (·.1.startsWith "lower: ")
  emit s!"stamp: read+lower {ms t0 t1} ms: read JSON {ms t0 tj} ms, {", ".intercalate (phases.map fun (k, t, _) => s!"{k.drop 7} {t / 1000000} ms")}"
  match planned with
  | .error e => refuse e
  | .ok (f, modules, notes) =>
    let mut refused : Option String := none
    -- The module units checked for the imports' footprints, each on its
    -- line; a refused one leaves its importers' reads at the ordinary effect.
    if !modules.isEmpty then
      let passNs := ((← SinglePass.kindNanos.get).toList.filter (·.1 == "modules: pass")).foldl (· + ·.2.1) 0
      emit s!"stamp: modules: {modules.length} groups checked, {passNs / 1000000} ms"
    -- Profiling: each import read at a footprint, and that footprint.
    if (← SinglePass.profiling.get) then
      for (n, Φ, ot, r) in f.p.qualified do
        emit s!"import: {n} {(toJson Φ).compress} onThrow {ot} result {(toJson r).compress}"
      for n in notes do emit s!"import read: {n}"
    for m in modules do
      for line in m.lines do
        for l in line.splitOn "\n" do emit s!"{m.unit}: {l}"
      IO.println (match m.verdict with
        | .ok deps => Json.mkObj [("unit", toJson m.unit), ("members", toJson m.members), ("accepted", toJson true),
            ("depends", toJson deps)]
        | .error reason => Json.mkObj [("unit", toJson m.unit), ("members", toJson m.members),
            ("refusal", toJson reason)]).compress
    for i in f.fr.selected (selection names) do
      let unit := f.fr.unitId i
      let members := (f.fr.group i).map f.fr.unitId
      let s0 ← IO.monoNanosNow
      let f0 ← CertificateProducer.forwardNanos.get
      let verdict : Except String (List String) ← match mode with
        | 0 => IO.lazyPure fun _ =>
          let (evidence, refusal, _, _, _) := f.produceGroup fuel (f.fr.group i)
          match refusal with
          | some reason => .error reason
          | none => SourceClaimJson.unitVerdict f budget unit evidence
        -- Mode 9: the search and the proved check over mode 8's plans.
        | 1 | 9 => IO.lazyPure fun _ => f.verifyGroup fuel (f.fr.group i) false
        | 3 | 8 => do
          let p0 ← SinglePass.passNanos.get
          let compare := (← IO.getEnv "TSCERT_COMPARE").isSome
          let debugNode := ((← IO.getEnv "TSCERT_NODE").bind String.toNat?).getD 1000000000
          let repeats := ((← IO.getEnv "TSCERT_REPEAT").bind String.toNat?).getD 1
          -- The given statement-entry facts, a file of lines by unit
          -- (`TSCERT_GIVEN`, written by `dev/single-pass-given.mts`).
          -- (no file is no given fact; a module unit's line is its module's)
          let given ← match suppliedGiven with
            | none => pure none
            | some _ => pure (some (givenLines.fold (init := {}) fun (m : Std.HashMap String Json) u j =>
                if (j.getObjVal? "graph").isOk then m.insert u j else m))
          -- Observing: the state at `TSCERT_OBSERVE` (`node:L` or `offset:K`).
          let observe ← IO.getEnv "TSCERT_OBSERVE"
          -- The pass's counts as JSON lines (`TSCERT_COUNTS`, `dev/perf-gate.mts`),
          -- with the bytes of the files it read.
          let counting := (← IO.getEnv "TSCERT_COUNTS").isSome
          if counting then
            let size := fun (p : String) => do
              try pure (← System.FilePath.metadata p).byteSize.toNat catch _ => pure 0
            -- The given file's lines read: the file's units', and a module
            -- unit's where its module's groups were checked.
            let checked := if interfaces.isSome then [] else modules.map fun m => ((m.unit.drop "module:".length).toString.splitOn "#").head!
            let given := (givenText.filter fun l => !moduleLine l ||
              checked.any fun c => (l.splitOn s!"\"unit\":\"module:{c}#").length > 1).foldl
              (fun n l => n + l.utf8ByteSize + 1) 0
            let claimsBytes ← match claimsPath with
              | some p => size p
              | none => pure 0
            let standInBytes ← match standInsPath with
              | some p => size p
              | none => pure 0
            let interfaceBytes ← match interfacesPath with
              | some p => size p
              | none => pure 0
            emit s!"counts-read: \{\"fragmentBytes\":{← size astPath},\"claimsBytes\":{claimsBytes},\"givenBytes\":{given},\"standInBytes\":{standInBytes},\"interfaceBytes\":{interfaceBytes}}"
          let (lines, v) ← IO.lazyPure fun _ =>
            f.passGroup fuel (f.fr.group i) compare debugNode repeats given observe counting
          let p1 ← SinglePass.passNanos.get
          let s1 ← IO.monoNanosNow
          for line in lines do emit line
          let kinds ← SinglePass.kindNanos.get
          emit s!"rule time by term kind (ms, applications): {kinds.toList.map fun (k, t, n) => s!"{k} {t / 1000000} {n}"}"
          emit s!"stamp: {unit} pass {ms p0 p1} ms, with obligations and vocabulary {ms s0 s1} ms"
          pure v
        | 5 => do
          -- Debugging: the searched certificate's node of label TSCERT_NODE.
          let label := ((← IO.getEnv "TSCERT_NODE").bind String.toNat?).getD 0
          match f.searchGroup fuel (f.fr.group i) true with
          | .ok b => match b.functions.head? with
            | some r => match r.certificate[label]? with
              | some c => emit s!"node {label}: knowledge {reprStr c.knowledge}\noutput {reprStr c.output}\nimplies {reprStr c.implies}\nyields {reprStr (c.yields.map fun y => (y.conditional, y.onFalse, y.target, y.type))}\nedges {c.edges.length}"
              | none => emit "no node"
            | none => emit "no function"
          | .error e => emit e
          pure (.error "debug")
        | 6 => do
          -- The given statement-entry facts of the selected units, read from
          -- the existing search's certificate: one line per unit.
          -- `TSCERT_GIVEN_FACTS=all`: the other statement entries' facts too.
          let facts ← IO.getEnv "TSCERT_GIVEN_FACTS"
          for line in f.givenLines fuel (f.fr.group i) facts.isSome (facts == some "all") do IO.println line.compress
          pure (.error "given facts written")
        | 7 => do
          -- The computed types against the claims, a line per unit
          -- (`Front.compareTypes`): a measurement only.
          match f.fr.compareTypes i with
          | .ok j => IO.println (Json.mkObj [("unit", toJson unit), ("comparison", j)]).compress
          | .error e => IO.println (Json.mkObj [("unit", toJson unit), ("error", toJson e)]).compress
          pure (.error "comparison only")
        | 4 => do
          let label := ((← IO.getEnv "TSCERT_NODE").bind String.toNat?).getD 0
          for line in f.passStats (f.fr.group i) label do emit line
          pure (.error "statistics only")
        | _ => do
          let b ← IO.lazyPure fun _ => f.searchGroup fuel (f.fr.group i) true
          let s1 ← IO.monoNanosNow
          let f1 ← CertificateProducer.forwardNanos.get
          emit s!"stamp: {unit} search {ms s0 s1} ms (forward pass {ms f0 f1} ms)"
          let v ← IO.lazyPure fun _ => do f.checkGroup (f.fr.group i) (← b)
          let s2 ← IO.monoNanosNow
          emit s!"stamp: {unit} check {ms s1 s2} ms"
          pure v
      let s3 ← IO.monoNanosNow
      emit s!"stamp: {unit} verdict {ms s0 s3} ms, total {ms t0 s3} ms"
      IO.println (match verdict with
        | .ok deps => Json.mkObj [("unit", toJson unit), ("members", toJson members), ("accepted", toJson true),
            ("depends", toJson deps)]
        | .error reason => Json.mkObj [("unit", toJson unit), ("members", toJson members),
            ("refusal", toJson reason)]).compress
      if let .error reason := verdict then refused := refused.orElse fun _ => some reason
    -- Mode 6: the given lines of the module runs' units too, each named by
    -- its wire identity (`ModuleRun.givenLines`).
    if mode == 6 then
      let facts ← IO.getEnv "TSCERT_GIVEN_FACTS"
      for m in f.p.modules do
        for line in m.givenLines budget fuel facts.isSome (facts == some "all") do IO.println line.compress
    match f.extractionRefusal (selection names) with
    | some reason => refuse reason
    | none =>
      match refused with
      | some reason => refuse reason
      | none =>
        IO.println s!"accept: stateful source {fileKey}"
        return 0

/-- The module runs a document's claims plan (`SourceClaimJson.planImports`),
one per line (`ModuleRun.wire`): each imported module's document restricted
to the read closure of the functions read qualified of it, with its claims
and its own qualified reads. A plan refused is a refusal. -/
def moduleRunsFile (astPath claimsPath : String) : IO UInt32 := do
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match do SourceClaimJson.planImports (← ast) (← claims) with
  | .ok p => p.modules.forM (IO.println ·.wire.compress); return 0
  | .error e => refuse e

/-- Check one module run at its slice lines (`SourceClaimJson.moduleLineVerdict`),
whose acceptance `checkUnitJson_safe` states: its verdict on a line,
`{"unit","members","accepted","depends"}` or `{"unit","members","refusal"}`. -/
def checkModuleFile (runPath evidencePath : String)
    (budget : PositiveCertificates.SearchBudget := {}) : IO UInt32 := do
  let run ← readJson runPath
  match run >>= SourceClaimJson.ModuleRun.decode with
  | .error e => refuse e
  | .ok m =>
    let unit := toJson ("module:" ++ m.location)
    let members := toJson ([] : List String)
    match (← readJson evidencePath) >>= fun e => SourceClaimJson.moduleLineVerdict m budget e with
    | .ok () =>
      IO.println (Json.mkObj [("unit", unit), ("members", members), ("accepted", toJson true),
        ("depends", toJson ([] : List String))]).compress
      IO.println s!"accept: stateful source {m.location}"
      return 0
    | .error reason =>
      IO.println (Json.mkObj [("unit", unit), ("members", members), ("refusal", toJson reason)]).compress
      refuse reason

end Verification.RequestCli
