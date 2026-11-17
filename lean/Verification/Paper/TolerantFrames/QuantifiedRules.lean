import Verification.Paper.TolerantFrames.Assertions
import Verification.Semantics.RegionBounds

/-! # Full body instantiation and the Empty rule

Body indices have their own syntax, distinct from free terms. Instantiation
therefore replaces them capture-free with an arbitrary linear expression,
retaining shifted elements, projections, partial definedness and disjunction.
Empty uses the actual defined array/view length premise and valid root
references, not a density or separately supplied collection-entry premise.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.TolerantFrames
open Verification.Parity (Path)

/-- Scale an entire expression without dropping any mentioned term. -/
def Expression.scaleBy (c : Int) : Expression → Expression
  | .constant n => .constant (c * n)
  | .scale d t => .scale (c * d) t
  | .add e f => .add (e.scaleBy c) (f.scaleBy c)

def BodyTerm.instantiate (z : Path) (k : Expression) : BodyTerm → Expression
  | .index => k
  | .element d => .scale 1 (.element .value z (.add k (.constant d)) [] (.inl rfl))
  | .project kind fs valid => .scale 1 (.element kind z k fs valid)
  | .free t => .scale 1 t

def BodyExpression.instantiate (z : Path) (k : Expression) : BodyExpression → Expression
  | .constant n => .constant n
  | .scale c t => (t.instantiate z k).scaleBy c
  | .add e f => .add (e.instantiate z k) (f.instantiate z k)

def Clause.instantiate (z : Path) (k : Expression) : Clause → Formula
  | .le e f => .atom (.le (e.instantiate z k) (f.instantiate z k))
  | .or e f => .or (e.instantiate z k) (f.instantiate z k)

def Body.instantiate (z : Path) (k : Expression) : Body → Formula
  | .clause c => c.instantiate z k
  | .and a b => .and (a.instantiate z k) (b.instantiate z k)

/-- Exactly the two inequalities 0≤k and k+1≤bound. -/
def IndexBounds (k bound : Expression) : Formula :=
  .and (.atom (.le (.constant 0) k)) (.atom (.le (.add k (.constant 1)) bound))

/-- Definedness as the reflexive inequality of the actual path term. -/
def PathDefined (kind : Reading) (z : Path) : Formula :=
  .atom (.le (.scale 1 (.path kind z)) (.scale 1 (.path kind z)))

theorem Expression.eval_scaleBy (c : Int) (e : Expression) (ρ : Env) (h : Heap) :
    (e.scaleBy c).eval ρ h = (e.eval ρ h).map (c * ·) := by
  cases e with
  | constant n => rfl
  | scale d t => simp [Expression.scaleBy, Expression.eval, Option.map_map, Function.comp_def, Int.mul_assoc]
  | add e f =>
    simp only [Expression.scaleBy, Expression.eval, Expression.eval_scaleBy c e ρ h, Expression.eval_scaleBy c f ρ h]
    cases e.eval ρ h <;> cases f.eval ρ h <;> simp [Int.mul_add]

theorem BodyTerm.eval_instantiate {z : Path} {k : Expression} {ρ : Env} {h : Heap} {v : Val} {i : Int}
    (hz : z.read ρ h = some v) (hk : k.eval ρ h = some i) (t : BodyTerm) :
    (t.instantiate z k).eval ρ h = t.eval ρ h v i := by
  cases t <;> simp [BodyTerm.instantiate, Expression.eval, Term.eval, BodyTerm.eval, hz, hk, kindValue, readPath]
  case project kind fs valid => cases kind <;> rfl

theorem BodyExpression.eval_instantiate {z : Path} {k : Expression} {ρ : Env} {h : Heap} {v : Val} {i : Int}
    (hz : z.read ρ h = some v) (hk : k.eval ρ h = some i) (e : BodyExpression) :
    (e.instantiate z k).eval ρ h = e.eval ρ h v i := by
  induction e with
  | constant n => rfl
  | scale c t => simp only [BodyExpression.instantiate, Expression.eval_scaleBy, t.eval_instantiate hz hk, BodyExpression.eval]
  | add e f ih₁ ih₂ => simp only [BodyExpression.instantiate, Expression.eval, ih₁, ih₂, BodyExpression.eval]

theorem Clause.holds_instantiate {z : Path} {k : Expression} {ρ : Env} {m : Nat} {s : IndexedHeap} {v : Val} {i : Int}
    (hz : z.read ρ s.h = some v) (hk : k.eval ρ s.h = some i) (c : Clause) :
    (c.instantiate z k).Holds ρ m s ↔ c.Holds ρ s.h v i := by
  induction c with
  | le e f => simp only [Clause.instantiate, Formula.Holds, Atom.Holds, e.eval_instantiate hz hk, f.eval_instantiate hz hk, Clause.Holds]
  | or _ _ ih₁ ih₂ => exact or_congr ih₁ ih₂

theorem Body.holds_instantiate {z : Path} {k : Expression} {ρ : Env} {m : Nat} {s : IndexedHeap} {v : Val} {i : Int}
    (hz : z.read ρ s.h = some v) (hk : k.eval ρ s.h = some i) (b : Body) :
    (b.instantiate z k).Holds ρ m s ↔ b.Holds ρ s.h v i := by
  induction b with
  | clause c => exact c.holds_instantiate hz hk
  | and _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂

theorem IndexBounds.holds_iff {k bound : Expression} {ρ : Env} {m : Nat} {s : IndexedHeap} :
    (IndexBounds k bound).Holds ρ m s ↔
      ∃ i n, k.eval ρ s.h = some i ∧ bound.eval ρ s.h = some n ∧ 0 ≤ i ∧ i < n := by
  cases hk : k.eval ρ s.h <;> cases hb : bound.eval ρ s.h <;>
    simp [IndexBounds, Formula.Holds, Atom.Holds, Expression.eval, hk, hb] <;> omega

/-- Inst with the paper's exact premises and a syntactic instantiated goal. -/
theorem inst_rule {z : Path} {bound k : Expression} {body : Body} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (he : Every ρ s.h z bound body) (hk : (IndexBounds k bound).Holds ρ m s) :
    (body.instantiate z k).Holds ρ m s := by
  obtain ⟨v, _, n, hz, _, hn, hbody⟩ := he
  obtain ⟨i, n', hi, hn', h0, hlt⟩ := IndexBounds.holds_iff.mp hk
  have hnn : n' = n := Option.some.inj (hn'.symm.trans hn)
  subst n'
  exact (body.holds_instantiate hz hi).mpr (hbody i h0 hlt)

/-- Prefix with both actual linear expressions and a syntactic inequality. -/
theorem prefix_rule {z : Path} {bound smaller : Expression} {body : Body} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (he : Every ρ s.h z bound body)
    (hle : (Formula.atom (.le smaller bound)).Holds ρ m s) : Every ρ s.h z smaller body := by
  obtain ⟨n', n, hn', hn, hle⟩ := hle
  exact every_prefix he hn hn' hle

theorem PathDefined.holds_iff {kind : Reading} {z : Path} {ρ : Env} {m : Nat} {s : IndexedHeap} :
    (PathDefined kind z).Holds ρ m s ↔
      ∃ v n, z.read ρ s.h = some v ∧ kindValue s.h kind v = some n := by
  cases hz : z.read ρ s.h <;>
    simp [PathDefined, Formula.Holds, Atom.Holds, Expression.eval, Term.eval, hz]
  rename_i v
  cases kindValue s.h kind v <;> simp

private theorem entries_of_array_length {h : Heap} {v : Val} {n : Int} (hn : lengthOf h v = some n) :
    ∃ es, collectionEntries h v = some es := by
  obtain ⟨st, es, hst, hes, _, _⟩ := lengthOf_spine hn
  have he : elementsOf v = some st := by
    cases v <;> simp_all [spineOf, fieldsOf, elementsOf]
  exact ⟨es, by simp [collectionEntries, he, hes, spineEntries]⟩

private theorem entries_of_view_length {s : IndexedHeap} {v : Val} {n : Int}
    (hr : HeapRefs s.h v) (hn : viewLengthOf v = some n) : ∃ es, collectionEntries s.h v = some es := by
  obtain ⟨fs, oid, st, f, N, rfl, _⟩ := viewLengthOf_inv hn
  obtain ⟨hp, cs, hu, _⟩ := hr (.view st f N (fs.lookup arraySpineKey).isNone) (by simp [refs])
  have hfs : fs.lookup arraySpineKey = none := by simpa using hp
  exact ⟨cs.map some, by simp [collectionEntries, elementsOf, hfs, hu, spineEntries]⟩

/-- Empty from a defined array or typed-array length, without a density or
pre-supplied collection-entry assumption. Heap-valid roots supply shapes; actual heap readings use W3. -/
theorem empty_rule {kind : Reading} (hkind : kind = .length ∨ kind = .view)
    {z : Path} {bound : Expression} {body : Body} {ρ : Env} {m : Nat} {s : IndexedHeap}
    (hv : HeapContext ρ m s) (hd : (PathDefined kind z).Holds ρ m s)
    (hb : (Formula.atom (.le bound (.constant 0))).Holds ρ m s) : Every ρ s.h z bound body := by
  obtain ⟨v, len, hz, hlen⟩ := PathDefined.holds_iff.mp hd
  obtain ⟨n, zero, hn, hz0, hle⟩ := hb
  have hz0' : zero = 0 := (Option.some.inj hz0).symm
  subst zero
  have hr : HeapRefs s.h v := readPath_heapRefs z.fields (hv.1 z.root) hz
  have hes : ∃ es, collectionEntries s.h v = some es := by
    rcases hkind with rfl | rfl
    · exact entries_of_array_length hlen
    · exact entries_of_view_length hr hlen
  obtain ⟨es, hes⟩ := hes
  exact every_empty hz hes hn hle

end Verification.Paper.TolerantFrames
