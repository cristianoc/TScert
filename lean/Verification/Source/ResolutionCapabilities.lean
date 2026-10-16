import Verification.Types.ResolutionDescriptors

/-! Finite native-resolution classifications over a fixed, independently
interpreted native Promise constructor. These relations specify the instances
of external operation contracts; their constructors do not prove JavaScript
execution. Native callable membership remains a reviewed environment premise. -/
namespace Verification.ResolutionCapabilities
open PositiveGraphs PositiveNormalization ResolutionDescriptors

/-- Fresh resolution follows the literal payload of a native promise until
it reaches a stable family. Union arms share the declared target family. -/
inductive Resolves (P : Fam → Fam) (N : Fam) : Fam → Fam → Prop where
  | stable {A} : ValueFam A → FamLe A N → Resolves P N A A
  | native {A R} : Resolves P N A R → Resolves P N (P A) R
  | union {A B R S} : Resolves P N A R → Resolves P N B S →
      Resolves P N (unionT A B) (unionT R S)

/-- Observation reads a native promise's literal fulfillment family once. -/
inductive Observes (P : Fam → Fam) (N U : Fam) : Fam → Fam → Prop where
  | stable {A} : ValueFam A → FamLe A N → Observes P N U A A
  | native {A} : ValueFam A → FamLe A U → Observes P N U (P A) A
  | union {A B O Q} : Observes P N U A O → Observes P N U B Q →
      Observes P N U (unionT A B) (unionT O Q)

/-- The native constructor preserves value families and keeps every
application outside the stable family. -/
structure NativeSeparation (P : Fam → Fam) (N U : Fam) : Prop where
  valid : ∀ A, ValueFam A → ValueFam (P A)
  separate : ∀ A, ValueFam A → ¬ FamLe (P A) N
  native_source : ∀ A, ValueFam A → FamLe (P A) U
  stable_source : FamLe N U

private theorem union_valid {A B : Fam} (ha : ValueFam A) (hb : ValueFam B) :
    ValueFam (unionT A B) :=
  ⟨unionT_adm A B ha.1 hb.1, fun n W v h => h.elim (ha.2 n W v) (hb.2 n W v)⟩

section
variable {P : Fam → Fam} {N U : Fam}

theorem Resolves.input_valid (h : NativeSeparation P N U) {A R} (r : Resolves P N A R) :
    ValueFam A := by
  induction r with
  | stable hv _ => exact hv
  | native _ ih => exact h.valid _ ih
  | union _ _ ih₁ ih₂ => exact union_valid ih₁ ih₂

/-- Resolution is exact on stable inputs: a union of stable arms resolves
arm by arm to itself, and a native application is never stable. -/
theorem Resolves.exact (h : NativeSeparation P N U) {A R} (r : Resolves P N A R) :
    FamLe A N → R = A := by
  induction r with
  | stable => intro _; rfl
  | native r _ => intro hn; exact (h.separate _ (r.input_valid h) hn).elim
  | union _ _ ih₁ ih₂ =>
      intro hn
      rw [ih₁ (fun n W v hv => hn n W v (Or.inl hv)),
        ih₂ (fun n W v hv => hn n W v (Or.inr hv))]

/-- Observation is exact on stable inputs, by the same case analysis. -/
theorem Observes.exact (h : NativeSeparation P N U) {A O} (o : Observes P N U A O) :
    FamLe A N → O = A := by
  induction o with
  | stable => intro _; rfl
  | native hv _ => intro hn; exact (h.separate _ hv hn).elim
  | union _ _ ih₁ ih₂ =>
      intro hn
      rw [ih₁ (fun n W v hv => hn n W v (Or.inl hv)),
        ih₂ (fun n W v hv => hn n W v (Or.inr hv))]

/-- Resolution and observation carry only JavaScript values at every slot. -/
theorem Resolves.source (h : NativeSeparation P N U) {A R} (r : Resolves P N A R) :
    FamLe A U ∧ FamLe R U := by
  induction r with
  | stable _ hn => exact ⟨fun n W v hv => h.stable_source n W v (hn n W v hv),
      fun n W v hv => h.stable_source n W v (hn n W v hv)⟩
  | native r ih => exact ⟨h.native_source _ (r.input_valid h), ih.2⟩
  | union _ _ ih₁ ih₂ => exact ⟨fun n W v hv => hv.elim (ih₁.1 n W v) (ih₂.1 n W v),
      fun n W v hv => hv.elim (ih₁.2 n W v) (ih₂.2 n W v)⟩

theorem Observes.source (h : NativeSeparation P N U) {A O} (o : Observes P N U A O) :
    FamLe A U ∧ FamLe O U := by
  induction o with
  | stable _ hn => exact ⟨fun n W v hv => h.stable_source n W v (hn n W v hv),
      fun n W v hv => h.stable_source n W v (hn n W v hv)⟩
  | native hv hs => exact ⟨h.native_source _ hv, hs⟩
  | union _ _ ih₁ ih₂ => exact ⟨fun n W v hv => hv.elim (ih₁.1 n W v) (ih₂.1 n W v),
      fun n W v hv => hv.elim (ih₁.2 n W v) (ih₂.2 n W v)⟩

end

def capabilities {P : Fam → Fam} {N U : Fam} (h : NativeSeparation P N U) : Capabilities U N where
  resolve := Resolves P N
  observe := Observes P N U
  resolve_exact hn r := r.exact h hn
  observe_exact hn o := o.exact h hn
  resolve_source r := r.source h
  observe_source o := o.source h

section
variable {P : Fam → Fam} {N U : Fam} (h : NativeSeparation P N U)

/-- A stable leaf is its own observation. -/
def stableObservation (A : Fam) (ha : ValueFam A) (hn : FamLe A N) :
    Observation (capabilities h) where
  input := A
  observation := A
  input_valid := ha
  observation_valid := ha
  observed := .stable ha hn

/-- A native promise of any payload is observed at that payload. -/
def nativeObservation (A : Fam) (ha : ValueFam A) (hs : FamLe A U) : Observation (capabilities h) where
  input := P A
  observation := A
  input_valid := h.valid A ha
  observation_valid := ha
  observed := .native ha hs

/-- Every union arm contributes its input and observation. -/
def unionObservation (d e : Observation (capabilities h)) : Observation (capabilities h) where
  input := unionT d.input e.input
  observation := unionT d.observation e.observation
  input_valid := union_valid d.input_valid e.input_valid
  observation_valid := union_valid d.observation_valid e.observation_valid
  observed := .union d.observed e.observed

/-- A stable leaf uses one family for all three slots. -/
def stable (A : Fam) (ha : ValueFam A) (hn : FamLe A N) :
    Descriptor (capabilities h) where
  toObservation := stableObservation h A ha hn
  result := A
  result_valid := ha
  stable := hn
  resolved := .stable ha hn
  forwarded := .stable ha hn

/-- Native lifting preserves the child's associated result and observes its
input literally, including when that input is itself a native promise. -/
def native (d : Descriptor (capabilities h)) : Descriptor (capabilities h) where
  toObservation := nativeObservation h d.input d.input_valid (d.observed.source h).1
  result := d.result
  result_valid := d.result_valid
  stable := d.stable
  resolved := .native d.resolved
  forwarded := d.resolved

/-- Every union arm contributes its input, observation and result. -/
def union (d e : Descriptor (capabilities h)) : Descriptor (capabilities h) where
  toObservation := unionObservation h d.toObservation e.toObservation
  result := unionT d.result e.result
  result_valid := union_valid d.result_valid e.result_valid
  stable := fun n W v h => h.elim (d.stable n W v) (e.stable n W v)
  resolved := .union d.resolved e.resolved
  forwarded := .union d.forwarded e.forwarded

/-- **Resolvable inputs are described.** Every input with a fresh resolution
has a descriptor with that result: the classification rules construct its
observation alongside, so the observation exists also where no source type
names it, as for the observation of a qualified binder's observation. -/
theorem Resolves.describe {A R} (r : Resolves P N A R) :
    ∃ d : Descriptor (capabilities h), d.input = A ∧ d.result = R := by
  induction r with
  | stable hv hn => exact ⟨ResolutionCapabilities.stable h _ hv hn, rfl, rfl⟩
  | native _ ih =>
      obtain ⟨d, hd, hr⟩ := ih
      exact ⟨ResolutionCapabilities.native h d, by rw [← hd]; rfl, hr⟩
  | union _ _ ih₁ ih₂ =>
      obtain ⟨d, hd, hr⟩ := ih₁
      obtain ⟨e, he, hs⟩ := ih₂
      exact ⟨ResolutionCapabilities.union h d e, by rw [← hd, ← he]; rfl, by rw [← hr, ← hs]; rfl⟩

end

/-- The descriptor domain depends only on the constructor, the stable family and the value universe. -/
theorem domain_congr {ι : Type} {P P' : Fam → Fam} {N N' U U' : Fam}
    (h : NativeSeparation P N U) (h' : NativeSeparation P' N' U') (hp : P' = P) (hn : N' = N)
    (hu : U' = U) :
    descriptorDomain (ι := ι) (capabilities h') = descriptorDomain (capabilities h) := by
  subst hp hn hu
  rfl

#print axioms Resolves.source
#print axioms Observes.source
#print axioms Resolves.exact
#print axioms Observes.exact
#print axioms stableObservation
#print axioms nativeObservation
#print axioms unionObservation
#print axioms stable
#print axioms native
#print axioms union
#print axioms Resolves.describe

namespace OperationContract

end OperationContract


end Verification.ResolutionCapabilities
