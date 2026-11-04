import Verification.Source.FlowJson
-- FlowJson.lean supplies the claim-independent graphs the producer analyzes.
import Verification.Source.Claims.Json

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

/-- The runs a document's search consists of (`SourceClaimJson.planJson`),
one per line; a plan refused is a refusal. Plan output is never a source
acceptance or an evidence file. -/
def planFile (astPath claimsPath : String) : IO UInt32 := do
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match do SourceClaimJson.planJson (← ast) (← claims) with
  | .ok runs => runs.forM (IO.println ·.compress); return 0
  | .error e =>
    -- The plan's first refusal, then each other read it refuses, a line
    -- each, so the pipeline withdraws them in one round.
    let others := match do SourceClaimJson.planRefusals (← ast) (← claims) with
      | .ok rs => rs.filter (· != e)
      | .error _ => []
    refuse ("\n".intercalate (e :: others))

/-- Search evidence for one planned run (`SourceClaimJson.produceRunJson`),
written to `evidencePath`. -/
def runFile (runPath fileKey evidencePath : String) (fuel : Nat)
    (budget : PositiveCertificates.SearchBudget := {}) : IO UInt32 := do
  if evidencePath == runPath then return ← refuse "evidence output must differ from the input files"
  let run ← readJson runPath
  match do SourceClaimJson.produceRunJson (← run) fileKey fuel budget with
  | .ok evidence =>
    IO.FS.writeFile evidencePath (evidence.compress ++ "\n")
    IO.println s!"checked source evidence written: {evidencePath}"
    return 0
  | .error e => refuse e

/-- A file's units (`SourceClaimJson.unitsJson`), one per line; a front
refused is a refusal of every unit. -/
def unitsFile (astPath claimsPath fileKey : String) (budget : PositiveCertificates.SearchBudget := {}) :
    IO UInt32 := do
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match do SourceClaimJson.unitsJson (← ast) (← claims) fileKey budget with
  | .ok units => units.forM (IO.println ·.compress); return 0
  | .error e => refuse e

/-- Search evidence for one unit (`SourceClaimJson.produceUnitJson`),
written to `evidencePath`. -/
def produceUnitFile (astPath claimsPath fileKey evidencePath unit : String) (fuel : Nat)
    (budget : PositiveCertificates.SearchBudget := {}) : IO UInt32 := do
  if evidencePath == astPath || evidencePath == claimsPath then
    return ← refuse "evidence output must differ from the input files"
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match do SourceClaimJson.produceUnitJson (← ast) (← claims) fileKey fuel budget unit with
  | .ok evidence =>
    IO.FS.writeFile evidencePath (evidence.compress ++ "\n")
    IO.println s!"checked source evidence written: {evidencePath}"
    return 0
  | .error e => refuse e

/-- Check one unit (`SourceClaimJson.checkUnitJson`): on acceptance, its
dependencies on a `depends:` line. -/
def checkUnitFile (astPath claimsPath fileKey evidencePath unit : String)
    (budget : PositiveCertificates.SearchBudget := {}) : IO UInt32 := do
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  let evidence ← readJson evidencePath
  match do SourceClaimJson.checkUnitJson (← ast) (← claims) fileKey (← evidence) budget unit with
  | .ok deps =>
    IO.println s!"accept: unit {unit} of {fileKey}"
    IO.println s!"depends: {(toJson deps).compress}"
    return 0
  | .error e => refuse e

def sourceFiles (astPath claimsPath fileKey evidencePath : String)
    (fuel : Option Nat)
    (budget : PositiveCertificates.SearchBudget := {}) : IO UInt32 := do
  if fuel.isSome && (evidencePath == astPath || evidencePath == claimsPath) then
    return ← refuse "evidence output must differ from the input files"
  let ast ← readJson astPath
  let claims ← readJson claimsPath
  match fuel with
  | none =>
    let evidence ← readJson evidencePath
    let checked := do
      SourceClaimJson.checkJson (← ast) (← claims) fileKey (← evidence) budget
    match checked with
    | .ok () => IO.println s!"accept: stateful source {fileKey}"; return 0
    | .error e => refuse e
  | some depth =>
    let produced := do
      SourceClaimJson.produceJson (← ast) (← claims) fileKey depth budget
    match produced with
    | .error e => refuse e
    | .ok evidence =>
      -- A file that cannot be written is no refusal: its error is thrown.
      IO.FS.writeFile evidencePath (evidence.compress ++ "\n")
      IO.println s!"checked source evidence written: {evidencePath}"
      return 0

end Verification.RequestCli
