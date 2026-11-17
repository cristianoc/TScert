import Verification.Paper.TolerantFrames.Assertions

/-! # General consequences of element postconditions

The existing mechanism extended here is partial element reading. The principles
below range over arbitrary predicates of index and read value; their use for a
paper body requires preserving its free terms, rather than treating free-term
preservation as automatic. They do not assert contracts of a native library.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge
open Verification.TolerantFrames

/-- A property of each element reading in a prefix. This is the semantic
shape of a body over its index, its one element, and fixed free terms. -/
def EveryValue (h : Heap) (z : Val) (n : Int) (P : Int → Val → Prop) : Prop :=
  ∀ i : Int, 0 ≤ i → i < n → ∃ v, elementValue h z i = some v ∧ P i v

/-- The complete Push postcondition on one receiver, including holes in the
kept prefix. The return value is deliberately unspecified, as in the paper. -/
def PushPost (before after : Heap) (z v : Val) : Prop :=
  ∃ n, lengthOf before z = some n ∧ lengthOf after z = some (n + 1) ∧
    elementValue after z n = some v ∧
    ∀ j u, 0 ≤ j → j < n → elementValue before z j = some u → elementValue after z j = some u

/-- The complete exact postcondition of View-Write for the written view.
The effect on all views is a separate regional action premise. -/
def ViewWritePost (before after : Heap) (b : Val) (k : Int) (converted : Val) : Prop :=
  elementValue after b k = some converted ∧
    ∀ j u, j ≠ k → elementValue before b j = some u → elementValue after b j = some u

/-- Write-Kept's underlying principle: a read is unchanged or reads the
written value, and both possible values satisfy the predicate. -/
theorem write_kept {P : Val → Prop} {old new written : Val}
    (hold : P old) (hwrite : P written) (hnew : new = old ∨ new = written) : P new := by
  rcases hnew with rfl | rfl
  · exact hold
  · exact hwrite

/-- A single write preserves an arbitrary family of facts when the written
value satisfies the family's predicate at each index the write can reach. -/
theorem every_written {before after : Heap} {z written : Val} {n k : Int} {P : Int → Val → Prop}
    (he : EveryValue before z n P)
    (hpost : ViewWritePost before after z k written) (hw : P k written) : EveryValue after z n P := by
  intro i hi hin
  by_cases hik : i = k
  · subst i
    exact ⟨written, hpost.1, hw⟩
  · obtain ⟨v, hv, hp⟩ := he i hi hin
    exact ⟨v, hpost.2 i v hik hv, hp⟩

/-- Push-Every at any predicate, including a conjunction of disjunctive
linear bodies. The old bound is the whole old array length. -/
theorem push_every {before after : Heap} {z written : Val} {n : Int} {P : Int → Val → Prop}
    (he : EveryValue before z n P) (hpost : PushPost before after z written)
    (hlen : lengthOf before z = some n) (hw : P n written) : EveryValue after z (n + 1) P := by
  obtain ⟨n', hn', -, hlast, hkeep⟩ := hpost
  have hn : n' = n := Option.some.inj (hn'.symm.trans hlen)
  subst n'
  intro i hi hin
  by_cases heq : i = n
  · subst i
    exact ⟨written, hlast, hw⟩
  · have hlt : i < n := by omega
    obtain ⟨v, hv, hp⟩ := he i hi hlt
    exact ⟨v, hkeep i v hi hlt hv, hp⟩

/-- View-Every, preservation and conditional extension with exactly the
converted value. No assumption that conversion is the identity is made. -/
theorem view_every {before after : Heap} {z converted : Val} {n k : Int} {P : Int → Val → Prop}
    (he : EveryValue before z n P) (hpost : ViewWritePost before after z k converted)
    (hw : P k converted) :
    EveryValue after z n P ∧ (k = n → EveryValue after z (n + 1) P) := by
  refine ⟨every_written he hpost hw, ?_⟩
  intro hkn i hi hin
  by_cases hik : i = k
  · subst i
    exact ⟨converted, hpost.1, hw⟩
  · have hlt : i < n := by omega
    obtain ⟨v, hv, hp⟩ := he i hi hlt
    exact ⟨v, hpost.2 i v hik hv, hp⟩

/-- Element substitution is replacement of the very same partial value,
not an inference that an arbitrary element exists. -/
theorem element_substitution {h : Heap} {z v : Val} {i : Int} {P : Val → Prop}
    (hr : elementValue h z i = some v) :
    (∃ u, elementValue h z i = some u ∧ P u) ↔ P v := by
  constructor
  · rintro ⟨u, hu, hp⟩
    have he : u = v := Option.some.inj (hu.symm.trans hr)
    exact he ▸ hp
  · exact fun hp => ⟨v, hr, hp⟩

/-- A two-state postcondition has the paper's usual implication and
quantification meanings, not a finite list of selected instances. -/
abbrev Postcondition := Env → Env → Nat → IndexedHeap → IndexedHeap → Prop

def Now (F : Assertion) : Postcondition := fun _ ρ m _ s => F ρ m s

def Old (F : Assertion) : Postcondition := fun ρ _ m s _ => F ρ m s

def Transition (Φ : Footprint) : Postcondition := fun ρ _ _ s t => Action Φ ρ s t

def PostAnd (Q R : Postcondition) : Postcondition := fun ρ ρ' m s t => Q ρ ρ' m s t ∧ R ρ ρ' m s t

def PostOr (Q R : Postcondition) : Postcondition := fun ρ ρ' m s t => Q ρ ρ' m s t ∨ R ρ ρ' m s t

def PostImp (Q R : Postcondition) : Postcondition := fun ρ ρ' m s t => Q ρ ρ' m s t → R ρ ρ' m s t

def ForallIndex (Q : Int → Postcondition) : Postcondition := fun ρ ρ' m s t => ∀ i, Q i ρ ρ' m s t

def ForallValue (Q : Val → Postcondition) : Postcondition :=
  fun ρ ρ' m s t => ∀ v, isSourceVal v = true → Q v ρ ρ' m s t

theorem implication_elim {Q R : Postcondition} {ρ ρ' m s t}
    (hi : PostImp Q R ρ ρ' m s t) (hq : Q ρ ρ' m s t) : R ρ ρ' m s t := hi hq

theorem instantiate_index {Q : Int → Postcondition} {ρ ρ' m s t}
    (hq : ForallIndex Q ρ ρ' m s t) (i : Int) : Q i ρ ρ' m s t := hq i

theorem instantiate_value {Q : Val → Postcondition} {ρ ρ' m s t}
    (hq : ForallValue Q ρ ρ' m s t) {v : Val} (hv : isSourceVal v = true) : Q v ρ ρ' m s t := hq v hv

/-- Modal elimination across a regional action, with the same valuation.
Fresh bindings require scope agreement on the assertion, not on all slots. -/
theorem modal_elimination {F : Assertion} {Φ : Footprint} {ρ ρ' m s t}
    (hscope : F ρ m t ↔ F ρ' m t)
    (hb : Old (Box Φ F) ρ ρ' m s t) (ha : Transition Φ ρ ρ' m s t) : Now F ρ ρ' m s t :=
  hscope.mp (hb t ha)

end Verification.Paper.TolerantFrames
