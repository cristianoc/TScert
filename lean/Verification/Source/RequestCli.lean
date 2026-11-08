import Verification.Source.FlowJson
-- FlowJson.lean supplies the claim-independent graphs the producer analyzes.
import Verification.Source.Claims.Json
-- Claims/Translate.lean writes a slice's evidence over its document's store, untrusted.
import Verification.Source.Claims.Translate

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
`refused: {"unit","refusal"}`. Untrusted: the check translates the evidence
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
        let (evidence, refusal) := f.produceGroup fuel (f.fr.group i)
        h.putStrLn (SourceClaimJson.sliceLine unit evidence f.F.store.heads).compress
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
(`SourceClaimJson.unitVerdict`), a line of the evidence held only while it is
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
    let seen ← IO.mkRef ({} : Std.HashSet String)
    let refused ← IO.mkRef (none : Option String)
    let note (reason : String) : IO Unit := refused.modify (·.orElse fun _ => some reason)
    -- The document's heads, matched with each slice's (`Translate.headMap`),
    -- their signatures computed once.
    let target ← IO.mkRef (none : Option SourceClaimJson.Translate.Target)
    let translated (evidence : Json) : Option (Array EquationLowering.Draft) → IO (Except String Json)
      | none => pure (.ok evidence)
      | some heads => do
        let t := (← target.get).getD (SourceClaimJson.Translate.Target.of f.F.store.heads.heads)
        match SourceClaimJson.Translate.translate heads t evidence with
        | .ok (e, t) => target.set (some t); pure (.ok e)
        | .error reason => target.set (some t); pure (.error reason)
    forEachLine evidencePath fun bytes => do
      match lineJson bytes >>= SourceClaimJson.readLine with
      | .error reason => note reason
      | .ok (unit, evidence, heads) =>
        match ← translated evidence heads with
        | .error reason => note reason
        | .ok evidence =>
          if let some (_, members) := wanted.find? (·.1 == unit) then
            let verdict := SourceClaimJson.unitVerdict f budget unit evidence
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

/-- Search evidence for one module run (`SourceClaimJson.produceModule`),
written to `evidencePath`; a search refused is a refusal. -/
def produceModuleFile (runPath evidencePath : String) (fuel : Nat)
    (budget : PositiveCertificates.SearchBudget := {}) : IO UInt32 := do
  if evidencePath == runPath then return ← refuse "evidence output must differ from the input file"
  let run ← readJson runPath
  match run >>= SourceClaimJson.ModuleRun.decode with
  | .error e => refuse e
  | .ok m =>
    let (evidence, refusal) := SourceClaimJson.produceModule m fuel budget
    IO.FS.writeFile evidencePath evidence.compress
    IO.println s!"checked source evidence written: {evidencePath}"
    match refusal with
    | none => return 0
    | some reason => refuse reason

/-- Check one module run at its evidence (`SourceClaimJson.moduleVerdict`),
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
    match (← readJson evidencePath) >>= fun e => SourceClaimJson.moduleVerdict m budget e with
    | .ok () =>
      IO.println (Json.mkObj [("unit", unit), ("members", members), ("accepted", toJson true),
        ("depends", toJson ([] : List String))]).compress
      IO.println s!"accept: stateful source {m.location}"
      return 0
    | .error reason =>
      IO.println (Json.mkObj [("unit", unit), ("members", members), ("refusal", toJson reason)]).compress
      refuse reason

end Verification.RequestCli
