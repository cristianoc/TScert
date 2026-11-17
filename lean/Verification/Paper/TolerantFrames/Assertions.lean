import Verification.Paper.TolerantFrames.SemanticRules
import Verification.Semantics.ViewConversion

/-! # The paper's assertion syntax

This extends the shared partial path and term readings, not heap or world
semantics. The older `Parity` arena remains a finite certificate language;
its extra presence and invariant-guard checks do not define this language.
All linear combinations evaluate every syntactically mentioned term, including
ones with coefficient zero. Thus undefined terms cannot disappear by algebra.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.TolerantFrames
open Verification.Parity (Path)

/-- Safe integer literals of the term grammar. -/
abbrev IntegerLiteral := { n : Int // -9007199254740991 ≤ n ∧ n ≤ 9007199254740991 }

/-- The four integer readings of a value: numeric value, array length,
view length, UTF-16 string length. These are the shared meanings. -/
abbrev Reading := HeapKnowledge.Term.Kind

mutual
/-- Terms t of §4. The optional field suffix after an element is empty for
z[e] or slen(z[e]); well-formedness below excludes the other empty suffixes. -/
inductive Term where
  | literal (n : IntegerLiteral)
  | path (reading : Reading) (p : Path)
  | element (reading : Reading) (z : Path) (index : Expression) (suffix : List String)
      (valid : reading = .value ∨ reading = .strLength ∨ suffix ≠ [])
/-- Linear combinations e, with arbitrary integer coefficients. -/
inductive Expression where
  | constant (n : Int)
  | scale (coefficient : Int) (term : Term)
  | add (left right : Expression)
end

/-- A collection's entries, ordinary arrays and typed arrays alike. -/
def collectionEntries (h : Heap) (v : Val) : Option (List (Option Nat)) :=
  (elementsOf v).bind fun s => h[s]?.bind spineEntries

/-- An in-bounds element. A hole reads undefined; an out-of-bounds read
is undefined as a term of the assertion language (it denotes no value). -/
def elementValue (h : Heap) (v : Val) (i : Int) : Option Val := do
  if i < 0 then none else
    let entries ← collectionEntries h v
    match entries[i.toNat]? with
    | none => none
    | some none => some .undef
    | some (some l) => h[l]?

mutual
/-- Partial term evaluation, shared readings at every path and element suffix. -/
def Term.eval (ρ : Env) (h : Heap) : Term → Option Int
  | .literal n => some n.val
  | .path k p => (p.read ρ h).bind (kindValue h k)
  | .element k z i fs _ => do
    let v ← z.read ρ h
    let j ← i.eval ρ h
    let e ← elementValue h v j
    let u ← readPath h e fs
    kindValue h k u
/-- Integer arithmetic on combinations; intermediate combinations need not
be safe integers. Terms themselves must satisfy their reading's bounds. -/
def Expression.eval (ρ : Env) (h : Heap) : Expression → Option Int
  | .constant n => some n
  | .scale c t => (t.eval ρ h).map (c * ·)
  | .add e f => do return (← e.eval ρ h) + (← f.eval ρ h)
end

/-- Terms of a quantified body. The shifted element has a nonnegative
literal offset; only an unshifted element may have a field suffix. -/
inductive BodyTerm where
  | index
  | element (offset : Nat)
  | project (reading : Reading) (suffix : List String)
      (valid : reading = .value ∨ reading = .strLength ∨ suffix ≠ [])
  | free (term : Term)

/-- Body expressions use exactly the same linear-combination grammar. -/
inductive BodyExpression where
  | constant (n : Int)
  | scale (coefficient : Int) (term : BodyTerm)
  | add (left right : BodyExpression)

/-- ψ and φ of §4: conjunctions of disjunctions of inequalities. A clause
is nonempty by construction, without imposing conjunctive normalisation. -/
inductive Clause where
  | le (left right : BodyExpression)
  | or (left right : Clause)

inductive Body where
  | clause (c : Clause)
  | and (left right : Body)

/-- The body is evaluated even at indices where no element exists. Only a
term which reads the element requires it. -/
def BodyTerm.eval (ρ : Env) (h : Heap) (z : Val) (i : Int) : BodyTerm → Option Int
  | .index => some i
  | .element d => (elementValue h z (i + d)).bind intValue
  | .project k fs _ => (elementValue h z i).bind fun v => (readPath h v fs).bind (kindValue h k)
  | .free t => t.eval ρ h

def BodyExpression.eval (ρ : Env) (h : Heap) (z : Val) (i : Int) : BodyExpression → Option Int
  | .constant n => some n
  | .scale c t => (t.eval ρ h z i).map (c * ·)
  | .add e f => do return (← e.eval ρ h z i) + (← f.eval ρ h z i)

def Clause.Holds (ρ : Env) (h : Heap) (z : Val) (i : Int) : Clause → Prop
  | .le e f => ∃ a b, e.eval ρ h z i = some a ∧ f.eval ρ h z i = some b ∧ a ≤ b
  | .or c d => c.Holds ρ h z i ∨ d.Holds ρ h z i

def Body.Holds (ρ : Env) (h : Heap) (z : Val) (i : Int) : Body → Prop
  | .clause c => c.Holds ρ h z i
  | .and c d => c.Holds ρ h z i ∧ d.Holds ρ h z i

/-- Source scalar literals cannot contain executable terms or internal spines. -/
inductive ScalarLiteral where
  | null | undefined
  | boolean (value : Bool)
  | number (bits : UInt64)
  | string (value : String)
  | bigint (value : Int)

def ScalarLiteral.eval : ScalarLiteral → Val
  | .null => .nul
  | .undefined => .undef
  | .boolean b => boolVal b
  | .number b => .num b
  | .string s => .str s
  | .bigint n => .bigint n

/-- Value kinds, including literals and their exclusions. Object membership
reads no heap or world. -/
inductive ValueKind where
  | number | string | object | null | undefined | boolean | bigint
  deriving DecidableEq

def ValueKind.Mem : ValueKind → Val → Prop
  | .number, .num _ | .string, .str _ | .object, .objAt .. | .null, .nul
  | .undefined, .undef | .boolean, .tru | .boolean, .fls | .bigint, .bigint _ => True
  | _, _ => False

structure ValueSet where
  kinds : List ValueKind
  included : List ScalarLiteral
  excluded : List ScalarLiteral

def ValueSet.Mem (V : ValueSet) (v : Val) : Prop :=
  ((∃ k ∈ V.kinds, k.Mem v) ∨ v ∈ V.included.map ScalarLiteral.eval) ∧ v ∉ V.excluded.map ScalarLiteral.eval

/-- A variable or scalar literal, before typed-array conversion. -/
inductive BaseValue where
  | variable (slot : Nat)
  | literal (v : ScalarLiteral)

def BaseValue.eval (ρ : Env) : BaseValue → Val
  | .variable x => ρ x
  | .literal v => v.eval

/-- Logical variables are de Bruijn slots; conversion applies only to a
variable or literal, and is defined only when that value is numeric. -/
inductive Value where
  | base (value : BaseValue)
  | converted (format : ViewFormat) (value : BaseValue)

def Value.eval (ρ : Env) : Value → Option Val
  | .base v => some (v.eval ρ)
  | .converted f v => match v.eval ρ with
    | .num bits => some (.num (f.conv bits))
    | _ => none

/-- Optional equality reads only the final field optionally. -/
def optionalRead (ρ : Env) (h : Heap) (p : Path) (f : String) : Option Val := do
  let v ← p.read ρ h
  match v with
  | .objAt fields _ _ => match fields.lookup (.str f) with
    | none => some .undef
    | some l => h[l]?
  | _ => none

/-- General quantified fact. No density or bound≤length premise is hidden
here. Negative bounds are vacuous, as in the paper. -/
def Every (ρ : Env) (h : Heap) (z : Path) (bound : Expression) (body : Body) : Prop :=
  ∃ v entries n, z.read ρ h = some v ∧ collectionEntries h v = some entries ∧
    bound.eval ρ h = some n ∧ ∀ i : Int, 0 ≤ i → i < n → body.Holds ρ h v i

inductive Atom where
  | le (left right : Expression)
  | equal (path : Path) (value : Value)
  | optionalEqual (path : Path) (field : String) (value : Value)
  | dense (slot : Nat) (bound : Expression)
  | contents (path : Path) (set : ValueSet)
  | element (path : Path) (index : Expression) (value : Value)
  | every (path : Path) (bound : Expression) (body : Body)

def Atom.Holds (ρ : Env) (h : Heap) : Atom → Prop
  | .le e f => ∃ a b, e.eval ρ h = some a ∧ f.eval ρ h = some b ∧ a ≤ b
  | .equal p v => ∃ u, p.read ρ h = some u ∧ v.eval ρ = some u
  | .optionalEqual p f v => ∃ u, optionalRead ρ h p f = some u ∧ v.eval ρ = some u
  | .dense x e => ∃ s entries n, spineOf (ρ x) = some s ∧ h[s]? = some (.arr entries) ∧
      e.eval ρ h = some n ∧ ∀ i : Nat, (i : Int) < n → ∃ l, entries[i]? = some (some l)
  | .contents p V => ∃ v, p.read ρ h = some v ∧ V.Mem v
  | .element z e v => ∃ a i u, z.read ρ h = some a ∧ e.eval ρ h = some i ∧
      elementValue h a i = some u ∧ v.eval ρ = some u
  | .every z t body => Every ρ h z t body

/-- Recursive paper assertions. Disjunction is unrestricted. Region freshness
and separation use the complete domain of the displayed definitions. -/
inductive Formula where
  | truth | falsity
  | atom (a : Atom)
  | and (left right : Formula)
  | or (left right : Formula)
  | existsValue (body : Formula)
  | separated (left right : Path)
  | apart (left right : Nat)
  | fresh (region : Region)
  | box (effect : Footprint) (body : Formula)

def Formula.Holds (ρ : Env) (m : Nat) (s : IndexedHeap) : Formula → Prop
  | .truth => True
  | .falsity => False
  | .atom a => a.Holds ρ s.h
  | .and F G => F.Holds ρ m s ∧ G.Holds ρ m s
  | .or F G => F.Holds ρ m s ∨ G.Holds ρ m s
  | .existsValue F => ∃ v : Val, isSourceVal v = true ∧ RefsOk s.W v ∧ F.Holds (Verification.push v ρ) m s
  | .separated p q => PathSpinesApart s.h (ρ p.root) p.fields (ρ q.root) q.fields
  | .apart x y => Verification.Parity.Apart ρ s.h ⟨x, []⟩ ⟨y, []⟩
  | .fresh r => Fresh r ρ m s
  | .box Φ F => ∀ s', Action Φ ρ s s' → F.Holds ρ m s'

/-- Semantic interpretation used by the shared modal and support theorems. -/
def Formula.meaning (F : Formula) : Assertion := fun ρ m s => F.Holds ρ m s

/-- General Inst, including element fields, shifted reads and disjunctive bodies. -/
theorem every_inst {ρ : Env} {h : Heap} {z : Path} {t : Expression} {body : Body}
    (he : Every ρ h z t body) {v : Val} {n k : Int}
    (hz : z.read ρ h = some v) (ht : t.eval ρ h = some n) (hk : 0 ≤ k) (hkn : k < n) :
    body.Holds ρ h v k := by
  obtain ⟨v', _, n', hz', _, ht', hb⟩ := he
  have hv : v' = v := Option.some.inj (hz'.symm.trans hz)
  have hn : n' = n := Option.some.inj (ht'.symm.trans ht)
  subst hv; subst hn
  exact hb k hk hkn

/-- General Prefix with arbitrary defined linear bounds. -/
theorem every_prefix {ρ : Env} {h : Heap} {z : Path} {t t' : Expression} {body : Body}
    (he : Every ρ h z t body) {n n' : Int}
    (ht : t.eval ρ h = some n) (ht' : t'.eval ρ h = some n') (hle : n' ≤ n) :
    Every ρ h z t' body := by
  obtain ⟨v, es, n0, hz, hes, ht0, hb⟩ := he
  have hn : n0 = n := Option.some.inj (ht0.symm.trans ht)
  subst hn
  exact ⟨v, es, n', hz, hes, ht', fun i hi hin => hb i hi (by omega)⟩

/-- Empty for either collection kind and any defined nonpositive bound. -/
theorem every_empty {ρ : Env} {h : Heap} {z : Path} {t : Expression} {body : Body}
    {v : Val} {es : List (Option Nat)} {n : Int}
    (hz : z.read ρ h = some v) (hes : collectionEntries h v = some es)
    (ht : t.eval ρ h = some n) (hn : n ≤ 0) : Every ρ h z t body :=
  ⟨v, es, n, hz, hes, ht, fun _ hi hin => (by omega)⟩

/-- The Guard rule works for any partial reading, optional fields included. -/
theorem guard {reading : Option Val} {v w : Val} {F : Prop}
    (h : reading = some v ∨ F) (hw : reading = some w) (hne : v ≠ w) : F := by
  rcases h with hv | hF
  · exact (hne (Option.some.inj (hv.symm.trans hw))).elim
  · exact hF

/-- All three displayed contradiction schemas. -/
theorem equal_contradiction {reading : Option Val} {v w : Val}
    (hv : reading = some v) (hw : reading = some w) (hne : v ≠ w) : False :=
  hne (Option.some.inj (hv.symm.trans hw))

theorem contents_contradiction {reading : Option Val} {V : ValueSet} {v : Val}
    (hv : reading = some v) (hc : ∃ w, reading = some w ∧ V.Mem w) (hn : ¬ V.Mem v) : False := by
  obtain ⟨w, hw, hm⟩ := hc
  have he := Option.some.inj (hv.symm.trans hw)
  exact hn (he.symm ▸ hm)

end Verification.Paper.TolerantFrames
