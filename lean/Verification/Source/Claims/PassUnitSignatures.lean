import Verification.Source.Claims.PassUnitInterfaces
import Verification.Types.StoreMaps
import Verification.Types.StoreMapsCheck
import Verification.Types.StoreMapsBuiltins
import Verification.Source.Claims.InterfaceRows

/-! # The single pass's unit theorem: signature agreement across two stores

An importer's slot reading an established entry is met where the two stores
agree on the entry's signature (`SignatureAgrees`). The module's store and
the importer's are two frozen equation stores, each with its own labels. A
store map from the module's graph to the importer's (`StoreMaps.StoreMap`)
on a region holding the entry's interface gives the agreement, both ways:
the interface renamed means in the importer's store what it means in the
module's (`StoreMaps.StoreMap.meaning_eq`). docs/drafts/pass-unit-theorem.md,
section 7. -/

namespace Verification.SourceClaimJson.PassUnit
open Lean PositiveGraphs LabelStore StoreMaps

/-- **Signature agreement from a store map** (proved): where a store map from
the entry's module graph to the importer's graph has the interface's labels
in its region and the slot's type is a union of the interface's labels
renamed, the stores agree on the signature. -/
theorem signatureAgrees_of_storeMap {e : Entry} (src : EntryRealized e) {ι : Type} [Labels ι]
    {G : NormalGraph ι} (m : StoreMap (graphOf src.fm) G)
    (hD : ∀ j ∈ src.layout.iface src.unit, m.D j) {A : List ι}
    (hA : ∀ x, x ∈ A ↔ x ∈ (src.layout.iface src.unit).map m.φ) : SignatureAgrees src G A := by
  intro j V w hw
  rw [m.meaning_eq_of_mem hD hA]
  exact hw

/-- **The stores' rows agree on the signature** (the lowering side, a
syntactic statement per read): a store map from the entry's module graph to
the importer's graph holds the interface's labels in its region, and the
slot's type is a union of the interface's labels renamed. The lemmas that
would prove it from the two lowerings are listed in
docs/drafts/pass-unit-theorem.md, section 7 ("The lowering side"). -/
def StoreMapAgrees {e : Entry} (src : EntryRealized e) {ι : Type} [Labels ι] (G : NormalGraph ι) (A : List ι) :
    Prop :=
  ∃ m : StoreMap (graphOf src.fm) G, (∀ j ∈ src.layout.iface src.unit, m.D j) ∧
    ∀ x, x ∈ A ↔ x ∈ (src.layout.iface src.unit).map m.φ

/-- Rows agreeing on the signature give its meaning's agreement (proved). -/
theorem signatureAgrees_of_maps {e : Entry} {src : EntryRealized e} {ι : Type} [Labels ι] {G : NormalGraph ι}
    {A : List ι} (h : StoreMapAgrees src G A) : SignatureAgrees src G A :=
  let ⟨m, hD, hA⟩ := h
  signatureAgrees_of_storeMap src m hD hA

/-- A frozen store's graph states no environment (proved). -/
theorem graphOf_env (f : FilePlans) : (graphOf f).env = ParameterAssignment.empty .mixed := rfl

/-- **Signature agreement from one check in one process** (proved): where
the importer holds the module's plans (`fragmentPlansWithModules`) and the
store-map check accepts the interface's labels against the slot's type,
the rows agree on the signature. -/
theorem storeMapAgrees_of_check {e : Entry} (src : EntryRealized e) {ι : Type} [Labels ι] [Inhabited ι]
    {G : NormalGraph ι} (hG : G.env = ParameterAssignment.empty .mixed) {canon : List ι → List ι}
    (hcanon : ∀ S x, x ∈ canon S ↔ x ∈ S) {fuel : Nat} {A : List ι} {mp}
    (h : matchStores (graphOf src.fm) G canon fuel (src.layout.iface src.unit) A = some mp) :
    StoreMapAgrees src G A :=
  matchStores_sound hcanon (env_empty_agree (graphOf_env src.fm) hG) h

/-- **Signature agreement through an interface's rows** (proved): the
interface entry carries a graph `Gs` and a type `Is` of it (the module's
rows reachable from the interface, as the wire's decoder reads them); the
module's check accepts its interface against them and the importer's check
accepts them against the slot's type. Then the stores agree on the
signature: the meanings are equal along both maps. -/
theorem signatureAgrees_of_checks {e : Entry} (src : EntryRealized e) {σ : Type} [DecidableEq σ]
    [Hashable σ] [Inhabited σ] {Gs : NormalGraph σ} (hGs : Gs.env = ParameterAssignment.empty .mixed)
    {Is : List σ} {ι : Type} [Labels ι] [Inhabited ι] {G : NormalGraph ι}
    (hG : G.env = ParameterAssignment.empty .mixed)
    {canon₁ : List σ → List σ} (hc₁ : ∀ S x, x ∈ canon₁ S ↔ x ∈ S)
    {canon₂ : List ι → List ι} (hc₂ : ∀ S x, x ∈ canon₂ S ↔ x ∈ S) {fuel₁ fuel₂ : Nat} {A : List ι} {mp₁ mp₂}
    (h₁ : matchStores (graphOf src.fm) Gs canon₁ fuel₁ (src.layout.iface src.unit) Is = some mp₁)
    (h₂ : matchStores Gs G canon₂ fuel₂ Is A = some mp₂) : SignatureAgrees src G A := by
  obtain ⟨m₁, hD₁, hI₁⟩ := matchStores_sound hc₁ (env_empty_agree (graphOf_env src.fm) hGs) h₁
  obtain ⟨m₂, hD₂, hI₂⟩ := matchStores_sound hc₂ (env_empty_agree hGs hG) h₂
  intro j V w hw
  rw [m₂.meaning_eq_of_mem hD₂ hI₂, m₁.meaning_eq_of_mem hD₁ hI₁]
  exact hw

/-- **Signature agreement from the front's two row checks** (proved): the
module published the entry where the store-map check relates its interface
type to the table's (`moduleRowsAgree`), and the importer reads it where
the check relates the table's type to its slot's type `A`
(`importerRowsAgree`). Then the stores agree on the signature; and where the
module's store states the built-ins, so do the table and the importer's
store, with the same keys and the same exception family. -/
theorem signatureAgrees_of_rows {e : Entry} (src : EntryRealized e) (t : RowTable) (name : String)
    {f : FilePlans} {A : List (Lab f)}
    (hm : moduleRowsAgree src.fm.F.store t name (src.layout.iface src.unit) = true)
    (hi : importerRowsAgree f.F.store t name A = true) :
    SignatureAgrees src (graphOf f) A ∧
      ∀ r, (graphOf src.fm).builtins = some r → ∃ r', (graphOf f).builtins = some r' ∧ r'.keys = r.keys ∧
        PositiveRules.excOf (graphOf f) = PositiveRules.excOf (graphOf src.fm) := by
  letI : Inhabited (Lab f) := ⟨Labels.nul⟩
  unfold moduleRowsAgree at hm
  unfold importerRowsAgree at hi
  cases hl : t.interfaces.lookup name with
  | none => rw [hl] at hm; cases hm
  | some Is =>
    rw [hl] at hm hi
    obtain ⟨mp₁, h₁⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨mp₂, h₂⟩ := Option.isSome_iff_exists.mp hi
    have hc₁ : ∀ (S : List Nat) x, x ∈ id S ↔ x ∈ S := fun _ _ => Iff.rfl
    have hc₂ : ∀ (S : List (Lab f)) x, x ∈ (S.mergeSort Labels.le).eraseDups ↔ x ∈ S := by
      intro S x; simp only [List.mem_eraseDups, List.mem_mergeSort]
    refine ⟨signatureAgrees_of_checks src rfl (graphOf_env f) hc₁ hc₂ h₁ h₂, ?_⟩
    intro r hr
    obtain ⟨_, r₁, -, -, hb₁, hk₁, -, -, -, -, he₁⟩ :=
      StoreMaps.matchStores_sound_builtins hc₁ (env_empty_agree (graphOf_env src.fm) rfl) hr h₁
    obtain ⟨_, r₂, -, -, hb₂, hk₂, -, -, -, -, he₂⟩ :=
      StoreMaps.matchStores_sound_builtins hc₂ (env_empty_agree rfl (graphOf_env f)) hb₁ h₂
    exact ⟨r₂, hb₂, hk₂.trans hk₁, he₂.trans he₁⟩

end Verification.SourceClaimJson.PassUnit
