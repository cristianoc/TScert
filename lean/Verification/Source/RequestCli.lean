import Verification.Source.FlowJson
-- FlowJson.lean supplies the execution graphs `--lower-control-flow` prints.
import Verification.Source.Claims.Json
-- Claims/ModuleInterfaces.lean computes and reads the module interfaces of mode 8.
import Verification.Source.Claims.ModuleInterfaces

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

/-- A selection of units by their members' names, comma-separated; every
unit without one. -/
def selection : Option String → Option (List String)
  | none => none
  | some names => some ((names.splitOn ",").filter (· != ""))

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
  let ast := (← readJson path) >>= fun a => do
    Fragment.symbolNumbersApart [a]
    pure (Fragment.canonicalSymbols a)
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
    fieldsExactly j ["modules", "dependencies", "force", "fuel", "mode"]
    -- Every symbol key at its canonical number (`Fragment.canonicalSymbols`):
    -- the members' documents, and the dependencies', which their own
    -- components' checks wrote so.
    let members ← jArr j "modules"
    let ds ← jArr j "dependencies"
    Fragment.symbolNumbersApart (members ++ ds.flatMap fun d =>
      (((d.getObjValD "interface").getObjValAs? (Array Json) "modules").toOption.getD #[]).toList.map
        (·.getObjValD "module"))
    let modules ← members.mapM fun m => Fragment.decodeModule (Fragment.canonicalSymbols m)
    let mut imported : List Fragment.ModuleAst := []
    for d in ds do
      fieldsExactly d ["key", "interface"]
      let _ ← d.getObjValAs? String "key"
      let i ← jField d "interface"
      fieldsExactly i ["modules"]
      for row in ← jArr i "modules" do
        let m ← Fragment.decodeModule (Fragment.canonicalSymbols (← jField row "module"))
        if modules.any (·.location == m.location) || imported.any (·.location == m.location) then
          throw "component dependency overlaps"
        imported := imported ++ [m]
    let sc : SourceClaimJson.ImportScope := ⟨modules ++ imported, SourceClaimJson.ModuleCode.of (modules ++ imported)⟩
    let decoded ← ds.mapM fun (d : Json) => SourceClaimJson.decodeInterfaces sc (d.getObjValD "interface")
    let incoming := decoded.flatMap (·.1)
    let incomingTables := decoded.flatMap (·.2)
    let needs ← SourceClaimJson.interfaceNeeds sc
    let own := needs.filter fun (n : SourceClaimJson.ModuleNeed) => modules.any (·.location == n.module.location)
    -- No module unit is given a line: every loop head's proposal is
    -- inferred (`HeadInference`).
    let given : Std.HashMap String Json := {}
    let force : List String ← fromJson? (← jField j "force")
    let fuel ← j.getObjValAs? Nat "fuel"
    let mode ← j.getObjValAs? Nat "mode"
    if mode != 8 then throw "interface mode must be 8"
    let infer := true
    let prepare := fun location (f : SourceClaimJson.FilePlans) =>
      f.withHeadFacts (forModule location given) false (inferred := infer)
    let check := fun (f : SourceClaimJson.FilePlans) group =>
      -- The given lines inference computes and the region separations, as
      -- for the file's own units (`passGroupMode8`).
      let r := f.passGroupMode8 infer force (fun _ => []) fuel group (given := some (moduleGiven f.fr.ast given))
      (r.1, r.2.1)
    let (est, _, _, tables) ← SourceClaimJson.establishModules
      (own.mergeSort (fun a b => a.module.location ≤ b.module.location)) budget force incoming prepare check incomingTables
    SourceClaimJson.encodeInterfaces modules est tables
  match parsed with
  | .error e => refuse e
  | .ok j => IO.println j.compress; return 0

/-- Mode 8, the single pass, over a file's fragment and the module
interfaces its imports read (`--verify-interface-stage 8`): each selected
unit's group checked by `FilePlans.passGroupMode8`, its types computed by the
walk, every loop head's proposal inferred (`HeadInference`); each unit's
verdict on a line `{"unit","members","accepted","depends"}` or
`{"unit","members","refusal"}`. -/
def verifyUnitsFile (astPath : String) (fileKey : String) (fuel : Nat) (names : Option String)
    (budget : PositiveCertificates.SearchBudget) (interfacesPath : String) (quiet : Bool := false) : IO UInt32 := do
  let emit := fun (s : String) => if quiet then pure () else IO.eprintln s
  -- Per-kind timings only where asked (`TSCERT_PROFILE`).
  SinglePass.profiling.set (← IO.getEnv "TSCERT_PROFILE").isSome
  let t0 ← IO.monoNanosNow
  let ast ← readJson astPath
  -- Every symbol key at its canonical number (`Fragment.canonicalSymbols`),
  -- the module documents it carries too.
  let ast := ast >>= fun a => do
    Fragment.symbolNumbersApart [a]
    pure (Fragment.canonicalSymbols a)
  -- No unit is given a line: every loop head's proposal is inferred.
  let givenLines : Std.HashMap String Json := {}
  -- A pass refusal's text located at the source obligation it names
  -- (`FilePlans.locatedRefusal`), unless `TSCERT_PASS_REFUSALS=raw`: the
  -- pass's own text alone.
  let located := (← IO.getEnv "TSCERT_PASS_REFUSALS") != some "raw"
  -- Adversarial proposals forced, for the controls (`TSCERT_FORCE`, comma-separated).
  let force := ((← IO.getEnv "TSCERT_FORCE").getD "").splitOn "," |>.filter (!·.isEmpty)
  let infer := true
  let interfaces ← readJson interfacesPath
  let tj ← IO.monoNanosNow
  -- The plans, and the module units the interfaces establish, each printed
  -- accepted (`decodeInterfaces`).
  let planned : Except String (SourceClaimJson.FilePlans × List String) ← IO.lazyPure fun _ => do
    let prepare := fun (given : Std.HashMap String Json) (f : SourceClaimJson.FilePlans) =>
      let f := f.withHeadFacts given false (inferred := infer)
      if force.contains "start-facts" then f.withFalseStartFact else f
    let cached ← interfaces
    let sc ← if (← jArr cached "modules").isEmpty then
        pure (⟨[], {}⟩ : SourceClaimJson.ImportScope)
      else SourceClaimJson.ImportScope.of (← ast)
    let (est, tables) ← SourceClaimJson.decodeInterfaces sc cached
    let f ← SourceClaimJson.fragmentPlansFromInterfaces (← ast) fileKey budget (selection names) {} force est tables
    return (prepare givenLines f, (est.map (·.2.2)).eraseDups)
  let t1 ← IO.monoNanosNow
  let ms := fun (a b : Nat) => s!"{(b - a) / 1000000}"
  let phases := (← SinglePass.kindNanos.get).toList.filter (·.1.startsWith "lower: ")
  emit s!"stamp: read+lower {ms t0 t1} ms: read JSON {ms t0 tj} ms, {", ".intercalate (phases.map fun (k, t, _) => s!"{k.drop 7} {t / 1000000} ms")}"
  match planned with
  | .error e => refuse e
  | .ok (f, modules) =>
    let mut refused : Option String := none
    for u in modules do
      IO.println (Json.mkObj [("unit", toJson u), ("members", toJson [u]), ("accepted", toJson true),
        ("depends", toJson ([] : List String))]).compress
    -- Profiling: each import read at a footprint, and that footprint.
    if (← SinglePass.profiling.get) then
      for (n, Φ, ot, r) in f.p.qualified do
        emit s!"import: {n} {(toJson Φ).compress} onThrow {ot} result {(toJson r).compress}"
    for i in f.fr.selected (selection names) do
      let unit := f.fr.unitId i
      let members := (f.fr.group i).map f.fr.unitId
      let s0 ← IO.monoNanosNow
      let p0 ← SinglePass.passNanos.get
      let compare := (← IO.getEnv "TSCERT_COMPARE").isSome
      let debugNode := ((← IO.getEnv "TSCERT_NODE").bind String.toNat?).getD 1000000000
      let repeats := ((← IO.getEnv "TSCERT_REPEAT").bind String.toNat?).getD 1
      -- Observing: the state at `TSCERT_OBSERVE` (`node:L` or `offset:K`).
      let observe ← IO.getEnv "TSCERT_OBSERVE"
      -- The pass's counts as JSON lines (`TSCERT_COUNTS`, `dev/perf-gate.mts`),
      -- with the bytes of the files it read.
      let counting := (← IO.getEnv "TSCERT_COUNTS").isSome
      if counting then
        let size := fun (p : String) => do
          try pure (← System.FilePath.metadata p).byteSize.toNat catch _ => pure 0
        emit s!"counts-read: \{\"fragmentBytes\":{← size astPath},\"interfaceBytes\":{← size interfacesPath}}"
      let (lines, verdict) ← IO.lazyPure fun _ =>
        let (ls, v, dropped, runs) := f.passGroupMode8 infer force (f.givenAt givenLines) fuel (f.fr.group i)
          compare debugNode repeats none observe counting located
        (ls ++ (if dropped > 0 then [s!"inferred heads: {dropped} proposals dropped, {runs} runs"] else []), v)
      let p1 ← SinglePass.passNanos.get
      let s1 ← IO.monoNanosNow
      for line in lines do emit line
      let kinds ← SinglePass.kindNanos.get
      emit s!"rule time by term kind (ms, applications): {kinds.toList.map fun (k, t, n) => s!"{k} {t / 1000000} {n}"}"
      emit s!"stamp: {unit} pass {ms p0 p1} ms, with obligations and vocabulary {ms s0 s1} ms, total {ms t0 s1} ms"
      IO.println (match verdict with
        | .ok deps => Json.mkObj [("unit", toJson unit), ("members", toJson members), ("accepted", toJson true),
            ("depends", toJson deps)]
        | .error reason => Json.mkObj [("unit", toJson unit), ("members", toJson members),
            ("refusal", toJson reason)]).compress
      if let .error reason := verdict then refused := refused.orElse fun _ => some reason
    match f.extractionRefusal (selection names) with
    | some reason => refuse reason
    | none =>
      match refused with
      | some reason => refuse reason
      | none =>
        IO.println s!"accept: stateful source {fileKey}"
        return 0

end Verification.RequestCli
