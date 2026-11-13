import Verification.Source.Claims.PassUnitFile

/-! # The single pass's unit theorem: linking modules through interfaces

Modules publish interfaces in an order: the components of the import graph
(its strongly connected components) in dependency order, the members of a
component in a fixed order, each module reading only entries published by
modules before it. An entry holds once its module's own check, run with the
entries it reads holding, establishes it. This module proves the induction
over that order, parameterised by that soundness of each module's step
(`linkModules`); the statement of the step against the integration branch's
`establishModules` and its proof plan are in docs/SINGLE-PASS-THEOREM.md,
section 7. -/

namespace Verification.SourceClaimJson.PassUnit

/-- **A publication order is well founded**: every entry a module reads was
published by a module strictly before it. -/
def ReadsEarlier {M E : Type} (order : List M) (est reads : M → List E) : Prop :=
  ∀ (i : Nat) m, order[i]? = some m → ∀ e ∈ reads m, ∃ j < i, ∃ m', order[j]? = some m' ∧ e ∈ est m'

/-- **Linking modules through their interfaces** (proved): over an order in
which every module reads only entries published before it, where each
module establishes its entries from the entries it reads (`hstep`, the
interface soundness of one module's check), every published entry holds. By
strong induction on the position in the order: the import graph's cycles
are inside components, whose members read later members at their declared
contracts only, so no entry is assumed before it is established. -/
theorem linkModules {M E : Type} (order : List M) (est reads : M → List E) (Holds : E → Prop)
    (hord : ReadsEarlier order est reads)
    (hstep : ∀ m ∈ order, (∀ e ∈ reads m, Holds e) → ∀ e ∈ est m, Holds e) :
    ∀ m ∈ order, ∀ e ∈ est m, Holds e := by
  have key : ∀ (i : Nat) m, order[i]? = some m → ∀ e ∈ est m, Holds e := by
    intro i
    induction i using Nat.strongRecOn with
    | _ i ih =>
      intro m hm
      apply hstep m (List.mem_of_getElem? hm)
      intro e he
      obtain ⟨j, hj, m', hm', he'⟩ := hord i m hm e he
      exact ih j hj m' hm' e he'
  intro m hm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  exact key i _ (List.getElem?_eq_getElem hi)

/-- **The entries a sequence of checks publishes**: each module's step run
with the entries published before it, as a fold threads them; reading only
earlier entries holds by construction. -/
def published {M E : Type} (step : List E → M → List E) : List M → List E → List E
  | [], acc => acc
  | m :: ms, acc => published step ms (acc ++ step acc m)

/-- **Linking the entries a fold publishes** (proved): where each step adds
only entries that hold once every entry it is given holds (`hstep`), every
entry the fold publishes from holding entries holds. The form of
`establishModules`' loop: each module's check reads `established` and
appends its own entries. -/
theorem published_holds {M E : Type} (step : List E → M → List E) (Holds : E → Prop)
    (hstep : ∀ acc m, (∀ e ∈ acc, Holds e) → ∀ e ∈ step acc m, Holds e) :
    ∀ ms acc, (∀ e ∈ acc, Holds e) → ∀ e ∈ published step ms acc, Holds e := by
  intro ms
  induction ms with
  | nil => intro acc h; exact h
  | cons m ms ih =>
    intro acc h
    apply ih
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact h e he
    · exact hstep acc m h e he

end Verification.SourceClaimJson.PassUnit
