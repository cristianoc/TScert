import Verification.Programs.VariadicTyping
import Verification.Programs.LinkingCaptures

/-! # Stable exports in dependency order

This model covers completed initialization, stable exports and an acyclic
import graph. Live-binding writes, re-exports and cyclic initialization are
outside its scope. Self-recursion uses the invocation's implicit self slot.
-/
namespace Verification.Linking
open PositiveGraphs PositiveNormalization PositiveRules Tower ProgramTyping
open CallEffects (Arrow RestArrow)

/-- One initialized export, with the code and capture layout certified for it.
Each unit may use its own frozen graph and label type. -/
structure Export (ι : Type) where
  graph : NormalGraph ι
  signature : Ty ι
  arity : Nat
  expressions : List Tm
  continuations : List (ControlFlow.Continuation × Option ControlFlow.Target)
  start : Nat
  captureTypes : List (Ty ι)
  captures : List Tm
  fields : List (PropKey × Nat)
  identity : Nat
  kind : Invoke
  arrows : List (Arrow (Ty ι))
  rests : List (RestArrow (Ty ι))

@[nospecialize] def Export.value (e : Export ι) : Tm :=
  .objAt e.fields (.graph e.arity e.expressions e.continuations e.start e.captures e.kind false)
    e.identity

/-- Structural links and independently certified bodies. A linked slot holds
the designated export and transports its interpreted signature. External
slots carry their own contracts and exclude every value in the export family.
A rank strictly decreases along capture imports;
no premise asserts membership of a linked export in its own signature. -/
structure WellLinked {labels : Fin count → Type} (exports : (i : Fin count) → Export (labels i)) where
  rank : Fin count → Nat
  layout : ∀ i, (exports i).captureTypes.length = (exports i).captures.length
  closed : ∀ i v, v ∈ (exports i).captures → Scoped 0 v
  values : ∀ i, CallArguments.Values (exports i).captures
  represents : ∀ i, Represents (exports i).graph (exports i).signature
    (.arrs (exports i).arrows (exports i).rests)
  kind : ∀ i, KindOffers (exports i).graph (exports i).kind
    (exports i).arrows (exports i).rests
  code : ∀ i, CodeOffers (exports i).graph (exports i).arity
    (exports i).expressions (exports i).continuations (exports i).start
    ((exports i).captureTypes ++ [(exports i).signature]) false
    (exports i).arrows (exports i).rests []
  slots : ∀ i k A, (exports i).captureTypes[k]? = some A →
    ((∀ j, envOf (exports i).captures .nul k ≠ (exports j).value) ∧
      ∀ n W, meaning (exports i).graph A n W (envOf (exports i).captures .nul k)) ∨
    ∃ j, rank j < rank i ∧ envOf (exports i).captures .nul k = (exports j).value ∧
      ∀ n W v, meaning (exports j).graph (exports j).signature n W v ↔
        meaning (exports i).graph A n W v

/-- Dependency-order induction constructs every export contract, including
its certified effects. The step-index induction needed for self-recursion
is `ProgramTyping.offers_self`. Scope: initialized, stable exports, acyclic
imports, no cyclic initialization, live-binding writes or re-exports.
The code premise is the certified invocation specification; external
contracts and signature transport are explicit in `WellLinked`. -/
theorem exports_safe {labels : Fin count → Type} {exports : (i : Fin count) → Export (labels i)}
    (linked : WellLinked exports) : ∀ i n W,
    meaning (exports i).graph (exports i).signature n W (exports i).value := by
  have go : ∀ r i, linked.rank i = r → ∀ n W,
      meaning (exports i).graph (exports i).signature n W (exports i).value := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro i hi n W
      apply offers_self (exports i).fields (linked.represents i) (linked.kind i)
        (linked.code i) (linked.layout i) (linked.closed i) (linked.values i)
      constructor
      · intro k
        simp only [envOf, List.getD]
        cases hv : (exports i).captures[k]? with
        | some v => exact linked.closed i v (List.mem_of_getElem? hv)
        | none => trivial
      · intro k A hA
        rcases linked.slots i k A hA with external | ⟨j, hj, hv, transport⟩
        · exact external.2 n W
        · rw [hv]
          exact (transport n W _).mp (ih (linked.rank j) (hi ▸ hj) j rfl n W)
  exact fun i => go (linked.rank i) i rfl

/-- Assemble an entry environment from external slots and linked exports.
Every typed slot names its exporter and transports the signature, or has an
external contract. This also applies to a certified request's input frame. -/
theorem entry_env {labels : Fin count → Type} {exports : (i : Fin count) → Export (labels i)}
    (linked : WellLinked exports) {κ : Type} {G : NormalGraph κ} {inputs : List (Ty κ)} {ρ : Env}
    (closed : ∀ k, Scoped 0 (ρ k))
    (slots : ∀ k A, inputs[k]? = some A →
      ((∀ j, ρ k ≠ (exports j).value) ∧ ∀ n W, meaning G A n W (ρ k)) ∨
      ∃ j, ρ k = (exports j).value ∧ ∀ n W v,
        meaning (exports j).graph (exports j).signature n W v ↔ meaning G A n W v)
    (n : Nat) (W : WorldT n) : EnvOk G inputs ρ n W := by
  refine ⟨closed, fun k A hA => ?_⟩
  rcases slots k A hA with external | ⟨j, hv, transport⟩
  · exact external.2 n W
  · rw [hv]
    exact (transport n W _).mp (exports_safe linked j n W)

end Verification.Linking
