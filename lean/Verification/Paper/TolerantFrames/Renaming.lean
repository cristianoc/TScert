import Verification.Paper.TolerantFrames.Assertions

/-! # Capture-avoiding renaming of the general assertion language

This extends the shared path/region renaming semantics to every constructor of
`Assertions`, including arbitrary quantified bodies and disjunctions. Renaming
is simultaneous, need not be injective, and lifts below logical value binders.
This is renaming of free variables, not arbitrary substitution of field paths
into grammar positions that require a variable.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.TolerantFrames
open Verification.Parity (Path)

/-- Leave the newly bound value at zero, shifting all free images. -/
def liftRenaming (σ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | x + 1 => σ x + 1

theorem liftRenaming_push (σ : Nat → Nat) (ρ : Env) (v : Val) :
    (fun x => push v ρ (liftRenaming σ x)) = push v (fun x => ρ (σ x)) := by
  funext x; cases x <;> rfl

/-- A path keeps its complete suffix while its free root is renamed. -/
def renamePath (σ : Nat → Nat) (p : Path) : Path := ⟨σ p.root, p.fields⟩

theorem read_renamePath (σ : Nat → Nat) (ρ : Env) (h : Heap) (p : Path) :
    (renamePath σ p).read ρ h = p.read (fun x => ρ (σ x)) h := rfl

mutual
def Term.rename (σ : Nat → Nat) : Term → Term
  | .literal n => .literal n
  | .path k p => .path k (renamePath σ p)
  | .element k p e fs valid => .element k (renamePath σ p) (e.rename σ) fs valid

def Expression.rename (σ : Nat → Nat) : Expression → Expression
  | .constant n => .constant n
  | .scale c t => .scale c (t.rename σ)
  | .add e f => .add (e.rename σ) (f.rename σ)
end

mutual
theorem Term.eval_rename (σ : Nat → Nat) (ρ : Env) (h : Heap) : ∀ t : Term,
    (t.rename σ).eval ρ h = t.eval (fun x => ρ (σ x)) h
  | .literal _ => rfl
  | .path _ _ => rfl
  | .element k p e fs valid => by simp only [Term.rename, Term.eval, read_renamePath, Expression.eval_rename]

theorem Expression.eval_rename (σ : Nat → Nat) (ρ : Env) (h : Heap) : ∀ e : Expression,
    (e.rename σ).eval ρ h = e.eval (fun x => ρ (σ x)) h
  | .constant _ => rfl
  | .scale c t => by simp only [Expression.rename, Expression.eval, Term.eval_rename]
  | .add e f => by simp only [Expression.rename, Expression.eval, Expression.eval_rename]
end

def BodyTerm.rename (σ : Nat → Nat) : BodyTerm → BodyTerm
  | .index => .index
  | .element d => .element d
  | .project k fs valid => .project k fs valid
  | .free t => .free (t.rename σ)

def BodyExpression.rename (σ : Nat → Nat) : BodyExpression → BodyExpression
  | .constant n => .constant n
  | .scale c t => .scale c (t.rename σ)
  | .add e f => .add (e.rename σ) (f.rename σ)

def Clause.rename (σ : Nat → Nat) : Clause → Clause
  | .le e f => .le (e.rename σ) (f.rename σ)
  | .or c d => .or (c.rename σ) (d.rename σ)

def Body.rename (σ : Nat → Nat) : Body → Body
  | .clause c => .clause (c.rename σ)
  | .and c d => .and (c.rename σ) (d.rename σ)

theorem BodyTerm.eval_rename (σ : Nat → Nat) (ρ : Env) (h : Heap) (z : Val) (i : Int) (t : BodyTerm) :
    (t.rename σ).eval ρ h z i = t.eval (fun x => ρ (σ x)) h z i := by
  cases t <;> simp only [BodyTerm.rename, BodyTerm.eval, Term.eval_rename]

theorem BodyExpression.eval_rename (σ : Nat → Nat) (ρ : Env) (h : Heap) (z : Val) (i : Int) (e : BodyExpression) :
    (e.rename σ).eval ρ h z i = e.eval (fun x => ρ (σ x)) h z i := by
  induction e <;> simp_all only [BodyExpression.rename, BodyExpression.eval, BodyTerm.eval_rename]

theorem Clause.holds_rename (σ : Nat → Nat) (ρ : Env) (h : Heap) (z : Val) (i : Int) (c : Clause) :
    (c.rename σ).Holds ρ h z i ↔ c.Holds (fun x => ρ (σ x)) h z i := by
  induction c <;> simp_all only [Clause.rename, Clause.Holds, BodyExpression.eval_rename]

theorem Body.holds_rename (σ : Nat → Nat) (ρ : Env) (h : Heap) (z : Val) (i : Int) (b : Body) :
    (b.rename σ).Holds ρ h z i ↔ b.Holds (fun x => ρ (σ x)) h z i := by
  induction b <;> simp_all only [Body.rename, Body.Holds, Clause.holds_rename]

def BaseValue.rename (σ : Nat → Nat) : BaseValue → BaseValue
  | .variable x => .variable (σ x)
  | .literal v => .literal v

def Value.rename (σ : Nat → Nat) : Value → Value
  | .base v => .base (v.rename σ)
  | .converted f v => .converted f (v.rename σ)

theorem BaseValue.eval_rename (σ : Nat → Nat) (ρ : Env) (v : BaseValue) :
    (v.rename σ).eval ρ = v.eval (fun x => ρ (σ x)) := by cases v <;> rfl

theorem Value.eval_rename (σ : Nat → Nat) (ρ : Env) (v : Value) :
    (v.rename σ).eval ρ = v.eval (fun x => ρ (σ x)) := by
  cases v <;> simp only [Value.rename, Value.eval, BaseValue.eval_rename]

def Atom.rename (σ : Nat → Nat) : Atom → Atom
  | .le e f => .le (e.rename σ) (f.rename σ)
  | .equal p v => .equal (renamePath σ p) (v.rename σ)
  | .optionalEqual p f v => .optionalEqual (renamePath σ p) f (v.rename σ)
  | .dense x e => .dense (σ x) (e.rename σ)
  | .contents p V => .contents (renamePath σ p) V
  | .element p e v => .element (renamePath σ p) (e.rename σ) (v.rename σ)
  | .every p e b => .every (renamePath σ p) (e.rename σ) (b.rename σ)

theorem optionalRead_rename (σ : Nat → Nat) (ρ : Env) (h : Heap) (p : Path) (f : String) :
    optionalRead ρ h (renamePath σ p) f = optionalRead (fun x => ρ (σ x)) h p f := rfl

theorem Atom.holds_rename (σ : Nat → Nat) (ρ : Env) (h : Heap) (a : Atom) :
    (a.rename σ).Holds ρ h ↔ a.Holds (fun x => ρ (σ x)) h := by
  cases a <;> simp only [Atom.rename, Atom.Holds, Expression.eval_rename, Value.eval_rename,
    read_renamePath, optionalRead_rename, Every, Body.holds_rename]

/-- All constructors participate; under a binder both paths and effects use
liftRenaming. No heap-reading substitution or rigidity certificate is hidden. -/
def Formula.rename (σ : Nat → Nat) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (a.rename σ)
  | .and F G => .and (F.rename σ) (G.rename σ)
  | .or F G => .or (F.rename σ) (G.rename σ)
  | .existsValue F => .existsValue (F.rename (liftRenaming σ))
  | .separated p q => .separated (renamePath σ p) (renamePath σ q)
  | .apart x y => .apart (σ x) (σ y)
  | .fresh r => .fresh (r.rename σ)
  | .box Φ F => .box (Footprint.rename σ Φ) (F.rename σ)

theorem Formula.holds_rename (σ : Nat → Nat) (ρ : Env) (m : Nat) (s : IndexedHeap) (F : Formula) :
    (F.rename σ).Holds ρ m s ↔ F.Holds (fun x => ρ (σ x)) m s := by
  induction F generalizing σ ρ s with
  | truth | falsity => rfl
  | atom a => exact a.holds_rename σ ρ s.h
  | and F G ihF ihG | or F G ihF ihG => simp only [Formula.rename, Formula.Holds, ihF, ihG]
  | existsValue F ih =>
    simp only [Formula.rename, Formula.Holds, ih, liftRenaming_push]
  | separated p q => rfl
  | apart x y => rfl
  | fresh r => simp only [Formula.rename, Formula.Holds, Fresh, Region.mem_rename]
  | box Φ F ih =>
    simp only [Formula.rename, Formula.Holds, ih]
    exact forall_congr' fun t => imp_congr (Verification.Parity.EffectAction.rename_iff σ) Iff.rfl

/-- Renaming leaves the invocation mark unchanged and preserves the valid
root context even when several formals name the same actual variable. -/
theorem ValidContext.rename {ρ m s} (hv : ValidContext ρ m s) (σ : Nat → Nat) :
    ValidContext (fun x => ρ (σ x)) m s :=
  ⟨fun x => hv.1 (σ x), fun x => hv.2.1 (σ x), hv.2.2⟩

/-- Identity and composition as semantic equivalences, for all constructors. -/
theorem Formula.rename_identity (F : Formula) (ρ : Env) (m : Nat) (s : IndexedHeap) :
    (F.rename id).Holds ρ m s ↔ F.Holds ρ m s := F.holds_rename id ρ m s

theorem Formula.rename_composition (F : Formula) (σ τ : Nat → Nat) (ρ : Env) (m : Nat) (s : IndexedHeap) :
    ((F.rename σ).rename τ).Holds ρ m s ↔ (F.rename (fun x => τ (σ x))).Holds ρ m s :=
  (Formula.holds_rename τ ρ m s (F.rename σ)).trans
    ((F.holds_rename σ (fun x => ρ (τ x)) m s).trans (F.holds_rename _ ρ m s).symm)

end Verification.Paper.TolerantFrames
