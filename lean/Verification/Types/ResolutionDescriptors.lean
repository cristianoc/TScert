import Verification.Types.PositiveGraphs

/- Qualified generic parameters carry input and literal observation families,
and, where resolvable, a stable associated-result family. The operation
relations and stable family are fixed independently of recursive graph
approximations. -/
namespace Verification.ResolutionDescriptors
open PositiveGraphs

/-- Fresh settlement and observation retain independent operation contracts.
Both are exact on stable inputs: an input within `N` is its own observation
and its own resolved result. -/
structure Capabilities (U N : Fam) where
  resolve : Fam → Fam → Prop
  observe : Fam → Fam → Prop
  resolve_exact : ∀ {A R}, FamLe A N → resolve A R → R = A
  observe_exact : ∀ {A O}, FamLe A N → observe A O → O = A
  resolve_source : ∀ {A R}, resolve A R →
    FamLe A U ∧ FamLe R U
  observe_source : ∀ {A O}, observe A O →
    FamLe A U ∧ FamLe O U

/-- Stable inputs have their own type as both observation and resolved result.
Operation-output inclusions alone do not establish this type equality. -/
def StableExact (N A O R : Fam) : Prop :=
  FamLe A N → O = A ∧ R = A

/-- An awaitable input and its literal observation (`X : Awaitable`). -/
structure Observation {U N : Fam} (C : Capabilities U N) where
  input : Fam
  observation : Fam
  input_valid : ValueFam input
  observation_valid : ValueFam observation
  observed : C.observe input observation

/-- A resolvable input (`X : Resolvable`): an observation together with a
stable result that both the input and its observation resolve to. -/
structure Descriptor {U N : Fam} (C : Capabilities U N) extends Observation C where
  result : Fam
  result_valid : ValueFam result
  stable : FamLe result N
  resolved : C.resolve input result
  forwarded : C.resolve observation result

/-- A stable input is its own observation. -/
theorem Observation.exactStable {U N : Fam} {C : Capabilities U N} (o : Observation C)
    (h : FamLe o.input N) : o.observation = o.input :=
  C.observe_exact h o.observed

/-- Stable exactness follows from the capabilities' exactness. -/
theorem Descriptor.exactStable {U N : Fam} {C : Capabilities U N} (d : Descriptor C) :
    StableExact N d.input d.observation d.result :=
  fun h => ⟨C.observe_exact h d.observed, C.resolve_exact h d.resolved⟩

theorem Descriptor.result_eq_input {U N : Fam} {C : Capabilities U N}
    (d : Descriptor C) (h : FamLe d.input N) : d.result = d.input :=
  (d.exactStable h).2

abbrev ProtectedSlots (s : SchemeRow ι) := s.protectedSlots

/-- One allowed tuple retains the observation contract, and, where the group
has a result slot, both resolution contracts. The value projection permits
ordinary argument-list binders alongside resolution groups. -/
def SlotCoherent {U N : Fam} (C : Capabilities U N) (As : List MixedFamily)
    (g : ResolutionSlots) : Prop :=
  ∃ T O : MixedFamily,
    As[g.input]? = some T ∧ As[g.observation]? = some O ∧ C.observe T.value.1 O.value.1 ∧
    ∀ r ∈ g.result, ∃ R : MixedFamily, As[r]? = some R ∧
      FamLe R.value.1 N ∧ C.resolve T.value.1 R.value.1 ∧ C.resolve O.value.1 R.value.1

/-- The fixed descriptor universe is shared by all schemes in the graph.
Ordinary schemes retain their unrestricted substitutions. -/
def descriptorDomain {U N : Fam} (C : Capabilities U N) : SchemeDomain ι .mixed where
  allowed s As := ProtectedSlots s ∧ ∀ g ∈ s.resolution, SlotCoherent C As g
  ordinary_allowed := by
    intro s As hs
    simp [ProtectedSlots, SchemeRow.protectedSlots, hs]
  congr := by
    intro s t hm hp As
    exact and_congr hp (by rw [hm])

/-- Allowed-instance elimination exposes a genuine observation for every group. -/
theorem allowed_observation {U N : Fam} (C : Capabilities U N) (s : SchemeRow ι)
    (As : List MixedFamily) (ha : (descriptorDomain C).allowed s As)
    (g : ResolutionSlots) (hg : g ∈ s.resolution) :
    ∃ (o : Observation C) (T O : MixedFamily),
      As[g.input]? = some T ∧ As[g.observation]? = some O ∧
      T.value.1 = o.input ∧ O.value.1 = o.observation := by
  obtain ⟨T, O, hT, hO, ho, _⟩ := ha.2 g hg
  exact ⟨⟨T.value.1, O.value.1, T.value.2, O.value.2, ho⟩, T, O, hT, hO, rfl, rfl⟩

/-- A group with a result slot exposes a genuine descriptor, including the
literal observation family rather than a result inferred from the input alone. -/
theorem allowed_descriptor {U N : Fam} (C : Capabilities U N) (s : SchemeRow ι)
    (As : List MixedFamily) (ha : (descriptorDomain C).allowed s As)
    (g : ResolutionSlots) (hg : g ∈ s.resolution) (r : Nat) (hr : g.result = some r) :
    ∃ (d : Descriptor C) (T O R : MixedFamily),
      As[g.input]? = some T ∧ As[g.observation]? = some O ∧ As[r]? = some R ∧
      T.value.1 = d.input ∧ O.value.1 = d.observation ∧ R.value.1 = d.result := by
  obtain ⟨T, O, hT, hO, ho, hres⟩ := ha.2 g hg
  obtain ⟨R, hR, hs, hr, hf⟩ := hres r (by rw [hr]; rfl)
  exact ⟨⟨⟨T.value.1, O.value.1, T.value.2, O.value.2, ho⟩, R.value.1, R.value.2,
    hs, hr, hf⟩, T, O, R, hT, hO, hR, rfl, rfl, rfl⟩

#print axioms Observation.exactStable
#print axioms Descriptor.exactStable
#print axioms allowed_observation
#print axioms Descriptor.result_eq_input
#print axioms allowed_descriptor
end Verification.ResolutionDescriptors
