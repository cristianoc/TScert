import Verification.Paper.TolerantFrames.Existentials
import Verification.Paper.TolerantFrames.Admission

/-! # First-order two-state postconditions

The existing mechanism extended here is the semantic `Postcondition` target.
This syntax has separate program-variable, logical-index and logical-value
namespaces. Quantifier bodies are syntax, not arbitrary predicate functions.
A focus supplies ordinary reads; the command entry remains frozen under boxes.
`old(t)` evaluates the whole term at entry, including nested index expressions.
Regions reuse the shared interpretation, with even roots for program variables
and odd roots for logical values. Admission still excludes shared region helpers.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.TolerantFrames

namespace TwoState

inductive Root where
  | program (slot : Nat)
  | value (slot : Nat)
  deriving DecidableEq

structure Path where
  root : Root
  fields : List String

/-- The logical namespaces do not change when a command binds a program name. -/
structure LogicalEnv where
  indices : Nat → Int
  values : Nat → Val

structure State where
  env : Env
  heap : IndexedHeap

structure Context where
  entry : State
  current : State
  mark : Nat

inductive BaseValue where
  | root (r : Root)
  | literal (v : ScalarLiteral)

inductive Value where
  | base (v : BaseValue)
  | converted (format : ViewFormat) (v : BaseValue)

mutual
inductive Term where
  | literal (n : IntegerLiteral)
  | index (slot : Nat)
  | path (reading : Reading) (p : Path)
  | element (reading : Reading) (p : Path) (index : Expression) (suffix : List String)
      (valid : reading = .value ∨ reading = .strLength ∨ suffix ≠ [])
  | old (term : Term)

inductive Expression where
  | constant (n : Int)
  | scale (coefficient : Int) (term : Term)
  | add (left right : Expression)
end

inductive BodyTerm where
  | index
  | element (offset : Nat)
  | project (reading : Reading) (suffix : List String)
      (valid : reading = .value ∨ reading = .strLength ∨ suffix ≠ [])
  | free (term : Term)

inductive BodyExpression where
  | constant (n : Int)
  | scale (coefficient : Int) (term : BodyTerm)
  | add (left right : BodyExpression)

inductive Clause where
  | le (left right : BodyExpression)
  | or (left right : Clause)

inductive Body where
  | clause (c : Clause)
  | and (left right : Body)

inductive Atom where
  | le (left right : Expression)
  | equal (path : Path) (value : Value)
  | optionalEqual (path : Path) (field : String) (value : Value)
  | dense (root : Root) (bound : Expression)
  | contents (path : Path) (set : ValueSet)
  | element (path : Path) (index : Expression) (value : Value)
  | every (path : Path) (bound : Expression) (body : Body)

inductive Assertion where
  | truth | falsity
  | atom (a : Atom)
  | and (left right : Assertion)
  | or (left right : Assertion)
  | existsValue (body : Assertion)
  | separated (left right : Path)
  | apart (left right : Root)
  | fresh (region : Region)
  | box (effect : Footprint) (body : Assertion)

/-- Exactly the postcondition constructors of §4. `old` is evaluated at the
command entry, independently of the enclosing invocation mark. -/
inductive Post where
  | assertion (F : Assertion)
  | old (F : Assertion)
  | transition (effect : Footprint)
  | and (left right : Post)
  | or (left right : Post)
  | implication (premise conclusion : Post)
  | forallIndex (body : Post)
  | forallValue (body : Post)

/-- Disjoint first-order encoding of program roots and logical-value roots. -/
def Root.encode : Root → Nat
  | .program x => 2 * x
  | .value x => 2 * x + 1

def mixedEnv (ρ : Env) (ν : Nat → Val) : Env :=
  fun x => if x % 2 = 0 then ρ (x / 2) else ν (x / 2)

def pushIndex (i : Int) (η : Nat → Int) : Nat → Int
  | 0 => i
  | x + 1 => η x

def Root.eval (ρ : Env) (ν : Nat → Val) : Root → Val
  | .program x => ρ x
  | .value x => ν x

def Path.shared (p : Path) : Parity.Path := ⟨p.root.encode, p.fields⟩

def Path.read (s : State) (ν : Nat → Val) (p : Path) : Option Val :=
  readPath s.heap.h (p.root.eval s.env ν) p.fields

def BaseValue.eval (s : State) (ν : Nat → Val) : BaseValue → Val
  | .root r => r.eval s.env ν
  | .literal v => v.eval

def Value.eval (s : State) (ν : Nat → Val) : Value → Option Val
  | .base v => some (v.eval s ν)
  | .converted f v => match v.eval s ν with
    | .num b => some (.num (f.conv b))
    | _ => none

mutual
def Term.eval (entry focus : State) (η : LogicalEnv) : Term → Option Int
  | .literal n => some n.val
  | .index x => some (η.indices x)
  | .path k p => (p.read focus η.values).bind (kindValue focus.heap.h k)
  | .element k p i fs _ => do
    let v ← p.read focus η.values
    let j ← i.eval entry focus η
    let e ← elementValue focus.heap.h v j
    let u ← readPath focus.heap.h e fs
    kindValue focus.heap.h k u
  | .old t => t.eval entry entry η

def Expression.eval (entry focus : State) (η : LogicalEnv) : Expression → Option Int
  | .constant n => some n
  | .scale c t => (t.eval entry focus η).map (c * ·)
  | .add e f => do return (← e.eval entry focus η) + (← f.eval entry focus η)
end

def BodyTerm.eval (entry focus : State) (η : LogicalEnv) (z : Val) (i : Int) : BodyTerm → Option Int
  | .index => some i
  | .element d => (elementValue focus.heap.h z (i + d)).bind intValue
  | .project k fs _ => (elementValue focus.heap.h z i).bind fun v =>
    (readPath focus.heap.h v fs).bind (kindValue focus.heap.h k)
  | .free t => t.eval entry focus η

def BodyExpression.eval (entry focus : State) (η : LogicalEnv) (z : Val) (i : Int) : BodyExpression → Option Int
  | .constant n => some n
  | .scale c t => (t.eval entry focus η z i).map (c * ·)
  | .add e f => do return (← e.eval entry focus η z i) + (← f.eval entry focus η z i)

def Clause.Holds (entry focus : State) (η : LogicalEnv) (z : Val) (i : Int) : Clause → Prop
  | .le e f => ∃ a b, e.eval entry focus η z i = some a ∧ f.eval entry focus η z i = some b ∧ a ≤ b
  | .or c d => c.Holds entry focus η z i ∨ d.Holds entry focus η z i

def Body.Holds (entry focus : State) (η : LogicalEnv) (z : Val) (i : Int) : Body → Prop
  | .clause c => c.Holds entry focus η z i
  | .and c d => c.Holds entry focus η z i ∧ d.Holds entry focus η z i

def Atom.Holds (entry focus : State) (η : LogicalEnv) : Atom → Prop
  | .le e f => ∃ a b, e.eval entry focus η = some a ∧ f.eval entry focus η = some b ∧ a ≤ b
  | .equal p v => ∃ u, p.read focus η.values = some u ∧ v.eval focus η.values = some u
  | .optionalEqual p f v => ∃ u,
      optionalRead (mixedEnv focus.env η.values) focus.heap.h p.shared f = some u ∧
      v.eval focus η.values = some u
  | .dense r e => ∃ st es n, spineOf (r.eval focus.env η.values) = some st ∧
      focus.heap.h[st]? = some (.arr es) ∧ e.eval entry focus η = some n ∧
      ∀ i : Nat, (i : Int) < n → ∃ l, es[i]? = some (some l)
  | .contents p V => ∃ v, p.read focus η.values = some v ∧ V.Mem v
  | .element p e v => ∃ a i u, p.read focus η.values = some a ∧
      e.eval entry focus η = some i ∧ elementValue focus.heap.h a i = some u ∧ v.eval focus η.values = some u
  | .every p e b => ∃ v es n, p.read focus η.values = some v ∧
      collectionEntries focus.heap.h v = some es ∧ e.eval entry focus η = some n ∧
      ∀ i : Int, 0 ≤ i → i < n → b.Holds entry focus η v i

/-- Assertions read the focus; old terms always read the frozen entry.
Logical existential values are valid at their own focused state only. -/
def Assertion.Holds (entry focus : State) (m : Nat) (η : LogicalEnv) : Assertion → Prop
  | .truth => True
  | .falsity => False
  | .atom a => a.Holds entry focus η
  | .and F G => F.Holds entry focus m η ∧ G.Holds entry focus m η
  | .or F G => F.Holds entry focus m η ∨ G.Holds entry focus m η
  | .existsValue F => ∃ v, isSourceVal v = true ∧ HeapRefs focus.heap.h v ∧
      F.Holds entry focus m { η with values := push v η.values }
  | .separated p q => PathSpinesApart focus.heap.h (p.root.eval focus.env η.values) p.fields
      (q.root.eval focus.env η.values) q.fields
  | .apart p q => Parity.Apart (mixedEnv focus.env η.values) focus.heap.h
      ⟨p.encode, []⟩ ⟨q.encode, []⟩
  | .fresh r => Fresh r (mixedEnv focus.env η.values) m focus.heap
  | .box Φ F => ∀ t, Action Φ (mixedEnv focus.env η.values) focus.heap t →
      F.Holds entry { focus with heap := t } m η

def Post.Holds (c : Context) (η : LogicalEnv) : Post → Prop
  | .assertion F => F.Holds c.entry c.current c.mark η
  | .old F => F.Holds c.entry c.entry c.mark η
  | .transition Φ => Action Φ (mixedEnv c.entry.env η.values) c.entry.heap c.current.heap
  | .and Q R => Q.Holds c η ∧ R.Holds c η
  | .or Q R => Q.Holds c η ∨ R.Holds c η
  | .implication Q R => Q.Holds c η → R.Holds c η
  | .forallIndex Q => ∀ i : Int, Q.Holds c { η with indices := pushIndex i η.indices }
  | .forallValue Q => ∀ v : Val, isSourceVal v = true → HeapRefs c.current.heap.h v → Q.Holds c { η with values := push v η.values }

/-- A logical valuation is explicit. Closed admission ensures its unused
slots cannot affect interpretation. No proof-search completeness is claimed. -/
def Post.meaning (η : LogicalEnv) (Q : Post) : Postcondition :=
  fun ρ ρ' m s t => Q.Holds ⟨⟨ρ, s⟩, ⟨ρ', t⟩, m⟩ η

/-- Logical scope tracks binder depths; numeric scope also distinguishes the
entry from the current program names. This is not declared-type admission. -/
def Root.Scoped (programs : Nat → Prop) (values : Nat) : Root → Prop
  | .program x => programs x
  | .value x => x < values

def Path.Scoped (programs : Nat → Prop) (values : Nat) (p : Path) : Prop := p.root.Scoped programs values

def BaseValue.Scoped (programs : Nat → Prop) (values : Nat) : BaseValue → Prop
  | .root r => r.Scoped programs values
  | .literal _ => True

def Value.Scoped (programs : Nat → Prop) (values : Nat) : Value → Prop
  | .base v | .converted _ v => v.Scoped programs values

mutual
def Term.Scoped (entryPrograms programs : Nat → Prop) (indices values : Nat) : Term → Prop
  | .literal _ => True
  | .index x => x < indices
  | .path _ p => p.Scoped programs values
  | .element _ p e _ _ => p.Scoped programs values ∧ e.Scoped entryPrograms programs indices values
  | .old t => t.Scoped entryPrograms entryPrograms indices values

def Expression.Scoped (entryPrograms programs : Nat → Prop) (indices values : Nat) : Expression → Prop
  | .constant _ => True
  | .scale _ t => t.Scoped entryPrograms programs indices values
  | .add e f => e.Scoped entryPrograms programs indices values ∧ f.Scoped entryPrograms programs indices values
end

def BodyTerm.Scoped (entryPrograms programs : Nat → Prop) (indices values : Nat) : BodyTerm → Prop
  | .free t => t.Scoped entryPrograms programs indices values
  | _ => True

def BodyExpression.Scoped (entryPrograms programs : Nat → Prop) (indices values : Nat) : BodyExpression → Prop
  | .constant _ => True
  | .scale _ t => t.Scoped entryPrograms programs indices values
  | .add e f => e.Scoped entryPrograms programs indices values ∧ f.Scoped entryPrograms programs indices values

def Clause.Scoped (entryPrograms programs : Nat → Prop) (indices values : Nat) : Clause → Prop
  | .le e f => e.Scoped entryPrograms programs indices values ∧ f.Scoped entryPrograms programs indices values
  | .or c d => c.Scoped entryPrograms programs indices values ∧ d.Scoped entryPrograms programs indices values

def Body.Scoped (entryPrograms programs : Nat → Prop) (indices values : Nat) : Body → Prop
  | .clause c => c.Scoped entryPrograms programs indices values
  | .and c d => c.Scoped entryPrograms programs indices values ∧ d.Scoped entryPrograms programs indices values

def Atom.Scoped (entryPrograms programs : Nat → Prop) (indices values : Nat) : Atom → Prop
  | .le e f => e.Scoped entryPrograms programs indices values ∧ f.Scoped entryPrograms programs indices values
  | .equal p v | .optionalEqual p _ v => p.Scoped programs values ∧ v.Scoped programs values
  | .dense r e => r.Scoped programs values ∧ e.Scoped entryPrograms programs indices values
  | .contents p _ => p.Scoped programs values
  | .element p e v => p.Scoped programs values ∧ e.Scoped entryPrograms programs indices values ∧ v.Scoped programs values
  | .every p e b => p.Scoped programs values ∧ e.Scoped entryPrograms programs indices values ∧ b.Scoped entryPrograms programs indices values

/-- Scope of a shared encoded region, including the helpers in raw syntax. -/
def RegionScoped (programs : Nat → Prop) (values : Nat) : Region → Prop
  | .field x _ | .fields x | .cells x | .path x _ _ | .pathFields x _ | .pathCells x _ | .spine x _ =>
      if x % 2 = 0 then programs (x / 2) else x / 2 < values
  | .inCls r _ => RegionScoped programs values r
  | .cls _ | .all => True

def EffectScoped (programs : Nat → Prop) (values : Nat) (Φ : Footprint) : Prop :=
  ∀ e ∈ Φ, RegionScoped programs values e.1

/-- Regions additionally require the paper's declared-type admission. -/
def Assertion.Scoped (entryPrograms programs : Nat → Prop) (indices values : Nat) : Assertion → Prop
  | .truth | .falsity => True
  | .atom a => a.Scoped entryPrograms programs indices values
  | .and F G | .or F G => F.Scoped entryPrograms programs indices values ∧ G.Scoped entryPrograms programs indices values
  | .existsValue F => F.Scoped entryPrograms programs indices (values + 1)
  | .separated p q => p.Scoped programs values ∧ q.Scoped programs values
  | .apart p q => p.Scoped programs values ∧ q.Scoped programs values
  | .fresh r => RegionScoped programs values r
  | .box Φ F => EffectScoped programs values Φ ∧ F.Scoped entryPrograms programs indices values

def Post.Scoped (entryPrograms programs : Nat → Prop) (indices values : Nat) : Post → Prop
  | .assertion F => F.Scoped entryPrograms programs indices values
  | .old F => F.Scoped entryPrograms entryPrograms indices values
  | .transition Φ => EffectScoped entryPrograms values Φ
  | .and Q R | .or Q R | .implication Q R => Q.Scoped entryPrograms programs indices values ∧ R.Scoped entryPrograms programs indices values
  | .forallIndex Q => Q.Scoped entryPrograms programs (indices + 1) values
  | .forallValue Q => Q.Scoped entryPrograms programs indices (values + 1)

/-- Root interpretation agrees with the shared region/path environment. -/
theorem mixedEnv_root (ρ : Env) (ν : Nat → Val) (r : Root) : mixedEnv ρ ν r.encode = r.eval ρ ν := by
  cases r with
  | program x => simp [mixedEnv, Root.encode, Root.eval]
  | value x =>
    have hd : (2 * x + 1) / 2 = x := by omega
    simp [mixedEnv, Root.encode, Root.eval, Nat.add_mod, hd]

theorem Path.read_shared (p : Path) (s : State) (ν : Nat → Val) :
    p.shared.read (mixedEnv s.env ν) s.heap.h = p.read s ν := by
  simp only [Parity.Path.read, Path.shared, Path.read, mixedEnv_root]

/-- Index quantification leaves logical values untouched, and conversely. -/
theorem LogicalEnv.push_commutes (η : LogicalEnv) (i : Int) (v : Val) :
    ({ { η with indices := pushIndex i η.indices } with values := push v η.values } : LogicalEnv) =
      { { η with values := push v η.values } with indices := pushIndex i η.indices } := rfl

/-- The two old spellings select the same frozen entry for every term. -/
theorem Term.old_frozen (t : Term) (entry focus : State) (η : LogicalEnv) :
    (Term.old t).eval entry focus η = t.eval entry entry η := rfl

end TwoState
end Verification.Paper.TolerantFrames
