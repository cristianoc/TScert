import Verification.Paper.TolerantFrames.PostconditionAdmission

/-! # The paper's quantified exact postconditions

These are the actual first-order formulas Q_< and Q_≠i. Their bound indices
are mathematical integers and their value witnesses are shared across old and
current reads. This module proves their interpretation; it does not assume
or implement the native command contracts that establish them.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge TolerantFrames

/-- Every successful in-bounds collection reading is a source value, including
an ordinary array's holes. Heap roles justify this without assuming density. -/
theorem elementValue_source {s : IndexedHeap} {z : Val} {i : Int} {u : Val}
    (he : elementValue s.h z i = some u) : isSourceVal u = true := by
  by_cases hi : i < 0
  · simp [elementValue, hi] at he
  · simp only [elementValue, hi, ↓reduceIte, bind, Option.bind_eq_some_iff] at he
    obtain ⟨es, hes, he⟩ := he
    split at he
    · cases he
    · cases he; rfl
    · rename_i l hl
      simp only [collectionEntries, Option.bind_eq_some_iff] at hes
      obtain ⟨st, _, v, hv, hentries⟩ := hes
      have hent : s.h[st]?.bind spineEntries = some es := by simp [hv, hentries]
      have hr := (s.ok.entries_cells hent (List.mem_of_getElem? hl)).1
      obtain ⟨w, hw, hsource, _⟩ := s.ok.2 l .elem hr
      have huw := Option.some.inj (he.symm.trans hw)
      subst u
      exact hsource

namespace TwoState

def variablePath (x : Nat) : Path := ⟨.program x, []⟩

def indexExpression : Expression := .scale 1 (.index 0)

def variableExpression (kind : Reading) (x : Nat) : Expression :=
  .scale 1 (.path kind (variablePath x))

def oldLength (x : Nat) : Expression := .scale 1 (.old (.path .length (variablePath x)))

def elementAtIndex (x : Nat) : Assertion :=
  .atom (.element (variablePath x) indexExpression (.base (.root (.value 0))))

/-- ∀j. 0≤j<old(len x) → ∀u. old(x[j]≐u) → x[j]≐u. -/
def keptPrefix (x : Nat) : Post :=
  .forallIndex (.implication
    (.assertion (.and (.atom (.le (.constant 0) indexExpression))
      (.atom (.le (.add indexExpression (.constant 1)) (oldLength x)))))
    (.forallValue (.implication (.old (elementAtIndex x)) (.assertion (elementAtIndex x)))))

/-- ∀j. j≠k → ∀u. old(b[j]≐u) → b[j]≐u, where ≠ is the
integer disjunction j+1≤k ∨ k+1≤j, not an added negation connective. -/
def keptOther (x k : Nat) : Post :=
  let unequal : Post := .or
    (.assertion (.atom (.le (.add indexExpression (.constant 1)) (variableExpression .value k))))
    (.assertion (.atom (.le (.add (variableExpression .value k) (.constant 1)) indexExpression)))
  .forallIndex (.implication unequal
    (.forallValue (.implication (.old (elementAtIndex x)) (.assertion (elementAtIndex x)))))

/-- Interpretation of the bound-value equality at the selected phase. -/
theorem elementAtIndex_holds (x : Nat) (entry focus : State) (m : Nat) (η : LogicalEnv) :
    (elementAtIndex x).Holds entry focus m η ↔
      elementValue focus.heap.h (focus.env x) (η.indices 0) = some (η.values 0) := by
  simp [elementAtIndex, Assertion.Holds, Atom.Holds, indexExpression, Expression.eval, Term.eval,
    variablePath, Path.read, readPath, Root.eval, Value.eval, BaseValue.eval]

/-- The complete kept-prefix relation, with the universal source-value
quantifier derived from successful old element readings. -/
theorem keptPrefix_holds {x : Nat} {c : Context} {η : LogicalEnv} {n : Int}
    (hn : lengthOf c.entry.heap.h (c.entry.env x) = some n) :
    (keptPrefix x).Holds c η ↔
      ∀ j u, 0 ≤ j → j < n →
        elementValue c.entry.heap.h (c.entry.env x) j = some u →
        elementValue c.current.heap.h (c.current.env x) j = some u := by
  have hformula : (keptPrefix x).Holds c η ↔
      ∀ j : Int, (0 ≤ j ∧ j + 1 ≤ n) → ∀ u : Val, isSourceVal u = true →
        elementValue c.entry.heap.h (c.entry.env x) j = some u →
        elementValue c.current.heap.h (c.current.env x) j = some u := by
    simp [keptPrefix, Post.Holds, Assertion.Holds, Atom.Holds, indexExpression,
      oldLength, variablePath, Expression.eval, Term.eval, Path.read, Root.eval,
      readPath, kindValue, hn, pushIndex, elementAtIndex_holds, push]
  rw [hformula]
  constructor
  · intro h j u h0 hj he
    exact h j ⟨h0, by omega⟩ u (elementValue_source he) he
  · intro h j ⟨h0, hj⟩ u _ he
    exact h j u h0 (by omega) he

/-- Other-index preservation uses the same bound j and u at both states. -/
theorem keptOther_holds {x k : Nat} {c : Context} {η : LogicalEnv} {i : Int}
    (hi : intValue (c.current.env k) = some i) :
    (keptOther x k).Holds c η ↔
      ∀ j u, j ≠ i → elementValue c.entry.heap.h (c.entry.env x) j = some u →
        elementValue c.current.heap.h (c.current.env x) j = some u := by
  have hformula : (keptOther x k).Holds c η ↔
      ∀ j : Int, (j + 1 ≤ i ∨ i + 1 ≤ j) → ∀ u : Val, isSourceVal u = true →
        elementValue c.entry.heap.h (c.entry.env x) j = some u →
        elementValue c.current.heap.h (c.current.env x) j = some u := by
    simp [keptOther, Post.Holds, Assertion.Holds, Atom.Holds, indexExpression,
      variableExpression, variablePath, Expression.eval, Term.eval, Path.read, Root.eval,
      readPath, kindValue, hi, pushIndex, elementAtIndex_holds, push]
  rw [hformula]
  constructor
  · intro h j u hne he
    exact h j (by omega) u (elementValue_source he) he
  · intro h j hj u _ he
    exact h j u (by omega) he

/-- The quantified prefix formula has no free logical slot. Its only
program variable is x, which is needed at entry and current phases. -/
theorem keptPrefix_scoped {x : Nat} {entryPrograms currentPrograms : Nat → Prop}
    (he : entryPrograms x) (hc : currentPrograms x) :
    (keptPrefix x).Scoped entryPrograms currentPrograms 0 0 := by
  simp [keptPrefix, Post.Scoped, Assertion.Scoped, Atom.Scoped, Expression.Scoped,
    Term.Scoped, variablePath, Path.Scoped, Root.Scoped, oldLength, indexExpression,
    elementAtIndex, Value.Scoped, BaseValue.Scoped, he, hc]

theorem keptPrefix_wellFormed (x : Nat) (entryTypes currentTypes : DeclaredPaths) :
    (keptPrefix x).WellFormed entryTypes currentTypes := by
  simp [keptPrefix, Post.WellFormed, Assertion.WellFormed, Atom.WellFormed,
    Expression.WellFormed, Term.WellFormed, Term.NoOld, variablePath, oldLength,
    indexExpression, elementAtIndex, Assertion.NoOld, Atom.NoOld, Expression.NoOld]

/-- The exact normal postcondition of Push, including both universal binders. -/
def pushPost (x v : Nat) : Post :=
  let increased : Assertion := .and
    (.atom (.le (variableExpression .length x) (.add (oldLength x) (.constant 1))))
    (.atom (.le (.add (oldLength x) (.constant 1)) (variableExpression .length x)))
  .and (.assertion increased) (.and
    (.assertion (.atom (.element (variablePath x) (oldLength x) (.base (.root (.program v))))))
    (keptPrefix x))

theorem pushPost_holds {x v : Nat} {c : Context} {η : LogicalEnv}
    (hx : c.current.env x = c.entry.env x) :
    (pushPost x v).Holds c η ↔
      PushPost c.entry.heap.h c.current.heap.h (c.entry.env x) (c.current.env v) := by
  have increased : (Assertion.and
      (.atom (.le (variableExpression .length x) (.add (oldLength x) (.constant 1))))
      (.atom (.le (.add (oldLength x) (.constant 1)) (variableExpression .length x)))).Holds
        c.entry c.current c.mark η ↔
      ∃ n, lengthOf c.entry.heap.h (c.entry.env x) = some n ∧
        lengthOf c.current.heap.h (c.entry.env x) = some (n + 1) := by
    cases h0 : lengthOf c.entry.heap.h (c.entry.env x) <;>
      cases h1 : lengthOf c.current.heap.h (c.entry.env x) <;>
      simp [Assertion.Holds, Atom.Holds, variableExpression, variablePath, oldLength,
        Expression.eval, Term.eval, Path.read, Root.eval, readPath, kindValue, hx, h0, h1] <;> omega
  have appended {n : Int} (hn : lengthOf c.entry.heap.h (c.entry.env x) = some n) :
      (Assertion.atom (.element (variablePath x) (oldLength x) (.base (.root (.program v))))).Holds
          c.entry c.current c.mark η ↔
      elementValue c.current.heap.h (c.entry.env x) n = some (c.current.env v) := by
    simp [Assertion.Holds, Atom.Holds, variablePath, oldLength, Expression.eval, Term.eval,
      Path.read, Root.eval, readPath, kindValue, Value.eval, BaseValue.eval, hx, hn]
  change (_ ∧ _ ∧ _) ↔ _
  dsimp only [Post.Holds]
  rw [increased]
  constructor
  · rintro ⟨⟨n, hn, hnext⟩, happ, hkeep⟩
    exact ⟨n, hn, hnext, (appended hn).mp happ, (by simpa only [hx] using (keptPrefix_holds hn).mp hkeep)⟩
  · rintro ⟨n, hn, hnext, happ, hkeep⟩
    exact ⟨⟨n, hn, hnext⟩, (appended hn).mpr happ, (keptPrefix_holds hn).mpr (by simpa only [hx] using hkeep)⟩

theorem keptOther_scoped {x k : Nat} {entryPrograms currentPrograms : Nat → Prop}
    (he : entryPrograms x) (hc : currentPrograms x) (hk : currentPrograms k) :
    (keptOther x k).Scoped entryPrograms currentPrograms 0 0 := by
  simp [keptOther, Post.Scoped, Assertion.Scoped, Atom.Scoped, Expression.Scoped,
    Term.Scoped, variablePath, Path.Scoped, Root.Scoped, variableExpression, indexExpression,
    elementAtIndex, Value.Scoped, BaseValue.Scoped, he, hc, hk]

theorem keptOther_wellFormed (x k : Nat) (entryTypes currentTypes : DeclaredPaths) :
    (keptOther x k).WellFormed entryTypes currentTypes := by
  simp [keptOther, Post.WellFormed, Assertion.WellFormed, Atom.WellFormed,
    Expression.WellFormed, Term.WellFormed, Term.NoOld, variablePath, variableExpression,
    indexExpression, elementAtIndex, Assertion.NoOld, Atom.NoOld, Expression.NoOld]

/-- The exact normal View-Write postcondition for this view: converted stored
value and universal preservation of all other indices. -/
def viewWritePost (x k v : Nat) (format : ViewFormat) : Post :=
  .and (.assertion (.atom (.element (variablePath x) (variableExpression .value k)
    (.converted format (.root (.program v)))))) (keptOther x k)

theorem viewWritePost_holds {x k v : Nat} {format : ViewFormat} {c : Context} {η : LogicalEnv}
    {i : Int} {converted : Val} (hx : c.current.env x = c.entry.env x)
    (hi : intValue (c.current.env k) = some i)
    (hv : (Value.converted format (.root (.program v))).eval c.current η.values = some converted) :
    (viewWritePost x k v format).Holds c η ↔
      ViewWritePost c.entry.heap.h c.current.heap.h (c.entry.env x) i converted := by
  have stored : (Assertion.atom (.element (variablePath x) (variableExpression .value k)
      (.converted format (.root (.program v))))).Holds c.entry c.current c.mark η ↔
      elementValue c.current.heap.h (c.entry.env x) i = some converted := by
    simp [Assertion.Holds, Atom.Holds, variablePath, variableExpression, Expression.eval,
      Term.eval, Path.read, Root.eval, readPath, kindValue, hx, hi, hv]
  change (_ ∧ _) ↔ _
  dsimp only [Post.Holds]
  rw [stored]
  constructor
  · rintro ⟨hs, ho⟩
    exact ⟨hs, by simpa only [hx] using (keptOther_holds hi).mp ho⟩
  · rintro ⟨hs, ho⟩
    exact ⟨hs, (keptOther_holds hi).mpr (by simpa only [hx] using ho)⟩

/-- All constructors have their existing semantic target interpretations. -/
theorem Post.meaning_and (η : LogicalEnv) (Q R : Post) :
    (Post.and Q R).meaning η = PostAnd (Q.meaning η) (R.meaning η) := rfl

theorem Post.meaning_or (η : LogicalEnv) (Q R : Post) :
    (Post.or Q R).meaning η = PostOr (Q.meaning η) (R.meaning η) := rfl

theorem Post.meaning_implication (η : LogicalEnv) (Q R : Post) :
    (Post.implication Q R).meaning η = PostImp (Q.meaning η) (R.meaning η) := rfl

theorem Post.meaning_forallIndex (η : LogicalEnv) (Q : Post) :
    (Post.forallIndex Q).meaning η = ForallIndex (fun i => Q.meaning {η with indices := pushIndex i η.indices}) := rfl

theorem Post.meaning_forallValue (η : LogicalEnv) (Q : Post) :
    (Post.forallValue Q).meaning η = ForallValue (fun v => Q.meaning {η with values := push v η.values}) := rfl

end TwoState
end Verification.Paper.TolerantFrames
