import Verification.Paper.TolerantFrames.Commands

/-! # Own-field reads in symbolic graph code

The shared pure test mechanism reifies the paper's own-field lookup without
restricting prototypes. This is finite administrative reduction, not a supplied
native contract or a separate heap model. Nonobjects retain readAt stuckness.
-/
namespace Verification.Paper.TolerantFrames
open Verification HeapObservations

/-- Concatenate actual shared reductions, retaining both counts. -/
theorem steps_append {i j h t h₁ t₁ h₂ t₂}
    (a : Steps i h t h₁ t₁) (b : Steps j h₁ t₁ h₂ t₂) :
    Steps (i + j) h t h₂ t₂ := by
  induction a with
  | refl => simpa using b
  | next hs _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.next hs (ih b)

/-- Determinism cancels a known prefix from any completed raw run. The final
term may be a value or an uncaught raise; only absence of a next step is used. -/
theorem steps_cancel_terminal {i h t h₁ t₁}
    (initial : Steps i h t h₁ t₁) :
    ∀ {n h₂ t₂}, Steps n h t h₂ t₂ →
      (∀ h₃ t₃, ¬ Step h₂ t₂ h₃ t₃) →
      ∃ j, n = i + j ∧ Steps j h₁ t₁ h₂ t₂ := by
  induction initial with
  | refl => intro n h₂ t₂ hr _; exact ⟨n, by omega, hr⟩
  | next first _ ih =>
    intro n h₂ t₂ hr terminal
    cases hr with
    | refl => exact False.elim (terminal _ _ first)
    | next actual rest =>
      obtain ⟨rfl, rfl⟩ := Step_det first actual
      obtain ⟨j, hn, hj⟩ := ih rest terminal
      exact ⟨j, by omega, hj⟩

/-- A graph-level test and branch cost two shared reductions. -/
theorem steps_test_ite {h tag v a b} (hv : isVal v = true) :
    Steps 2 h (.ite (.test tag v) a b) h (if tagHoldsIn h tag v then a else b) := by
  have hs := Step.iteC (t := a) (e := b) (Step.testV (h := h) (k := tag) hv)
  cases ht : tagHoldsIn h tag v <;> simp only [ht] at hs ⊢
  · exact .next hs (.next .iteF .refl)
  · exact .next hs (.next .iteT .refl)

/-- A fixed symbolic term, independent of the eventual object's fields. -/
def ownFieldCode (key : PropKey) (v : Tm) : Tm :=
  let own := Tm.ite (.test (.hasOwnKey key) v) (.readAt key v) .undef
  .ite (.test .isRef v) own (.ite (.test .isFun v) own (.readAt key v))

/-- The same closed-value case analysis used by Operation.fieldRead. -/
def ownFieldResult (key : PropKey) (v : Tm) : Tm := match v with
  | .objAt fs _ _ => if (fs.lookup key).isSome then .readAt key v else .undef
  | _ => .readAt key v

private theorem ownFieldResult_tests (key : PropKey) (v : Tm) :
    ownFieldResult key v =
      if tagHolds .isRef v || tagHolds .isFun v then
        (if tagHolds (.hasOwnKey key) v then .readAt key v else .undef)
      else .readAt key v := by
  cases v <;> try rfl
  rename_i fs code oid
  cases code <;> rfl

/-- All machine values, including callable objects, views and internal
spines, execute the symbolic own-read prefix in at most six pure reductions.
No assumption excludes a prototype or constrains the field map. -/
theorem ownFieldCode_prefix {h v} (key : PropKey) (hv : isVal v = true) :
    ∃ n, n ≤ 6 ∧ Steps n h (ownFieldCode key v) h (ownFieldResult key v) := by
  let own := Tm.ite (.test (.hasOwnKey key) v) (.readAt key v) .undef
  let rest := Tm.ite (.test .isFun v) own (.readAt key v)
  have hs₁ : Steps 2 h (ownFieldCode key v) h (if tagHolds .isRef v then own else rest) := by
    have run := steps_test_ite (h := h) (tag := .isRef) (a := own) (b := rest) hv
    have hp : tagHoldsIn h .isRef v = tagHolds .isRef v := by cases v <;> rfl
    rw [hp] at run
    exact run
  have hs₂ : Steps 2 h rest h (if tagHolds .isFun v then own else .readAt key v) := by
    have run := steps_test_ite (h := h) (tag := .isFun) (a := own) (b := .readAt key v) hv
    have hp : tagHoldsIn h .isFun v = tagHolds .isFun v := by cases v <;> rfl
    rw [hp] at run
    exact run
  have hs₃ : Steps 2 h own h (if tagHolds (.hasOwnKey key) v then .readAt key v else .undef) := by
    have run := steps_test_ite (h := h) (tag := .hasOwnKey key) (a := .readAt key v) (b := .undef) hv
    have hp : tagHoldsIn h (.hasOwnKey key) v = tagHolds (.hasOwnKey key) v := by cases v <;> rfl
    rw [hp] at run
    exact run
  rw [ownFieldResult_tests]
  cases hr : tagHolds .isRef v <;> cases hf : tagHolds .isFun v <;>
    simp only [hr, hf] at hs₁ hs₂ ⊢
  · exact ⟨4, by omega, steps_append hs₁ hs₂⟩
  · exact ⟨6, by omega, steps_append hs₁ (steps_append hs₂ hs₃)⟩
  · exact ⟨4, by omega, steps_append hs₁ hs₃⟩
  · exact ⟨4, by omega, steps_append hs₁ hs₃⟩

/-- In particular, the fixed symbolic term realizes B's actual field-read
code after its environment has supplied a machine value. -/
theorem Operation.fieldRead_prefix {host ρ h x field} (hv : isVal (ρ x) = true) :
    ∃ n, n ≤ 6 ∧ Steps n h (ownFieldCode (.str field) (ρ x)) h
      ((Operation.fieldRead x field).code host ρ) :=
  by
    have eq : (Operation.fieldRead x field).code host ρ = ownFieldResult (.str field) (ρ x) := by
      cases he : ρ x <;> simp only [Operation.code, ownFieldResult, he]
    rw [eq]
    exact ownFieldCode_prefix (h := h) (.str field) hv

/-- Completed symbolic own-reads invert to exactly the original operation,
with its primitive count plus a bounded administrative prefix. -/
theorem Operation.fieldRead_invert {host ρ h x field n h' t}
    (hv : isVal (ρ x) = true)
    (run : Steps n h (ownFieldCode (.str field) (ρ x)) h' t)
    (terminal : ∀ h₂ t₂, ¬ Step h' t h₂ t₂) :
    ∃ a p, a ≤ 6 ∧ n = a + p ∧
      Steps p h ((Operation.fieldRead x field).code host ρ) h' t := by
  obtain ⟨a, ha, initial⟩ := Operation.fieldRead_prefix (host := host) (h := h) hv
  obtain ⟨p, hn, hp⟩ := steps_cancel_terminal initial run terminal
  exact ⟨a, p, ha, hn, hp⟩

end Verification.Paper.TolerantFrames
