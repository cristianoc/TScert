import Verification.Programs.Linking
import Verification.Source.EffectJson
import Verification.Types.Decode

/-! # Comparison of closed primitive boundary signatures

The executable decoder admits exactly one fixed-arity, synchronous primitive
signature. Both contracts use the same primitive families and exception
interpretation. Graph attachment is explicit; contextual or generic types
require additional semantic transport.
-/
namespace Verification.PrimitiveBoundary
open Lean CallEffects PositiveGraphs PositiveNormalization PositiveRules Tower ProgramTyping

inductive Atom where
  | number | bigint | boolean | string
  deriving DecidableEq, Repr

structure Signature where
  parameters : List Atom
  result : Atom
  effect : Effect
  deriving DecidableEq, Repr

def Atom.meaning : Atom → Fam
  | .number => numT
  | .bigint => bigintT
  | .boolean => boolT
  | .string => strT

def Signature.contract (s : Signature) (receiver : Fam := sourceT) : Arrow Fam :=
  ⟨receiver, s.parameters.map Atom.meaning, s.result.meaning, s.effect⟩

def compare (a b : Signature) : Bool := decide (a = b)

/-- A successful comparison gives equality of interpreted callable contracts,
including the effect, under a shared exception interpretation. -/
theorem compare_sound {a b : Signature} (h : compare a b = true) (receiver : Fam := sourceT) :
    a.contract receiver = b.contract receiver := by
  have : a = b := of_decide_eq_true h
  subst b
  rfl

/-- A frozen graph attachment records its represented callable row and the
primitive interpretation of that row. It states type interpretation only;
it imposes no semantic membership requirement on the exported value. -/
structure Attachment {ι : Type} (G : NormalGraph ι) (F : Ty ι) (s : Signature) : Prop where
  row : ∃ p : Arrow (Ty ι), Represents G F (.arrs [p] []) ∧
    Arrow.map (meaning G) p = s.contract (excOf G)

/-- Comparison transports a certified export's semantic membership to its
importer, provided both signatures are attached to their frozen graphs and
share their exception interpretation. The export membership is supplied by
`Linking.exports_safe`; no Node comparison is a premise. -/
theorem transport {ι κ : Type} {G : NormalGraph ι} {H : NormalGraph κ}
    {F : Ty ι} {I : Ty κ} {a b : Signature}
    (exported : Attachment G F a) (imported : Attachment H I b)
    (equal : compare a b = true) (exceptions : excOf G = excOf H)
    {n W v} (member : meaning G F n W v) : meaning H I n W v := by
  obtain ⟨p, hp, hpm⟩ := exported.row
  obtain ⟨q, hq, hqm⟩ := imported.row
  have hc := (represents_raw hp n W v member).1
  have hm : Arrow.map (meaning G) p = Arrow.map (meaning H) q :=
    hpm.trans ((compare_sound equal (excOf G)).trans (by rw [exceptions]; exact hqm.symm))
  simp only [List.map_cons, List.map_nil] at hc
  rw [hm, exceptions] at hc
  apply represents_back hq n W v
  change CallEffects.callsT (excOf H) [Arrow.map (meaning H) q] n W v ∧ CallEffects.restsT (excOf H) [] n W v
  exact ⟨hc, hc.1, fun _ h => False.elim (List.not_mem_nil h)⟩

/-- Primitive TypeTerm decoder; spans carry locations only. -/
def atomOf (j : Json) : Except String Atom := do
  fieldsExactly j ["k", "name", "span"]
  if (← j.getObjValAs? String "k") != "atom" then throw "expected primitive atom"
  match ← j.getObjValAs? String "name" with
  | "number" => return .number
  | "bigint" => return .bigint
  | "boolean" => return .boolean
  | "string" => return .string
  | _ => throw "boundary type is outside the closed primitive fragment"

/-- The importer's complete fixed primitive TypeTerm, with every contract
field checked. Generics and construct signatures are checked at the value. -/
def signatureOf (j : Json) : Except String Signature := do
  fieldsExactly j ["k", "effect", "receiver", "params", "rest", "result", "span"]
  if (← j.getObjValAs? String "k") != "function" then throw "expected one function signature"
  if (← j.getObjVal? "receiver") != .null then throw "explicit receiver outside boundary"
  if (← j.getObjVal? "rest") != .null then throw "rest outside boundary"
  let params ← (← j.getObjValAs? (Array Json) "params").toList.mapM atomOf
  return ⟨params, ← atomOf (← j.getObjVal? "result"), ← fromJson? (← j.getObjVal? "effect")⟩

/-- Read the signature from the actual Fragment function supplied to the
Rust certificate pipeline, rather than recomputing it from the Rust parser.
Correspondence of this Fragment with Rust is the translation premise. -/
def exportOf (j : Json) : Except String Signature := do
  if (← j.getObjValAs? (Array Json) "typeParams").size != 0 then throw "generic export"
  if (← j.getObjValAs? String "completion") != "sync" then throw "async export"
  if (← j.getObjVal? "guard") != .null || (← j.getObjVal? "stated") != .null then
    throw "qualified export outside primitive demo"
  let params ← (← j.getObjValAs? (Array Json) "params").toList.mapM fun p => do
    atomOf (← p.getObjVal? "type")
  return ⟨params, ← atomOf (← j.getObjVal? "retType"), Effect.ordinary⟩

/-- The decision the boundary command uses. Successful decoding and checking
imply equality of the two interpreted callable contracts. -/
def check (exportJson importJson : Json) : Except String Bool := do
  return compare (← exportOf exportJson) (← signatureOf importJson)

theorem check_sound {e i : Json} {a b : Signature}
    (he : exportOf e = .ok a) (hi : signatureOf i = .ok b)
    (hc : check e i = .ok true) : a.contract = b.contract := by
  simp only [check, he, hi, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hc
  exact compare_sound hc

end Verification.PrimitiveBoundary
