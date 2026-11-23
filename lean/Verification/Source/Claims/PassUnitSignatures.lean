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
module's (`StoreMaps.StoreMap.meaning_eq`). docs/SINGLE-PASS-THEOREM.md,
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
docs/SINGLE-PASS-THEOREM.md, section 7 ("The lowering side"). -/
def StoreMapAgrees {e : Entry} (src : EntryRealized e) {ι : Type} [Labels ι] (G : NormalGraph ι) (A : List ι) :
    Prop :=
  ∃ m : StoreMap (graphOf src.fm) G, (∀ j ∈ src.layout.iface src.unit, m.D j) ∧
    ∀ x, x ∈ A ↔ x ∈ (src.layout.iface src.unit).map m.φ

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

/-- **Signature agreement through an interface's rows, the importer's map
the other way** (proved): the module's check accepts its interface against
the table, and the check from the slot's type to the table's accepts. The
meanings are equal along both maps. -/
theorem signatureAgrees_of_checks_back {e : Entry} (src : EntryRealized e) {σ : Type} [DecidableEq σ]
    [Hashable σ] [Inhabited σ] {Gs : NormalGraph σ} (hGs : Gs.env = ParameterAssignment.empty .mixed)
    {Is : List σ} {ι : Type} [Labels ι] [Inhabited ι] {G : NormalGraph ι}
    (hG : G.env = ParameterAssignment.empty .mixed)
    {canon₁ : List σ → List σ} (hc₁ : ∀ S x, x ∈ canon₁ S ↔ x ∈ S)
    {canon₂ : List σ → List σ} (hc₂ : ∀ S x, x ∈ canon₂ S ↔ x ∈ S) {fuel₁ fuel₂ : Nat} {A : List ι} {mp₁ mp₂}
    (h₁ : matchStores (graphOf src.fm) Gs canon₁ fuel₁ (src.layout.iface src.unit) Is = some mp₁)
    (h₂ : matchStores G Gs canon₂ fuel₂ A Is = some mp₂) : SignatureAgrees src G A := by
  obtain ⟨m₁, hD₁, hI₁⟩ := matchStores_sound hc₁ (env_empty_agree (graphOf_env src.fm) hGs) h₁
  obtain ⟨m₂, hD₂, hI₂⟩ := matchStores_sound hc₂ (env_empty_agree hG hGs) h₂
  intro j V w hw
  rw [← m₂.meaning_eq_of_mem hD₂ hI₂, m₁.meaning_eq_of_mem hD₁ hI₁]
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
    have hc₁ : ∀ (S : List Nat) x, x ∈ id S ↔ x ∈ S := fun _ _ => Iff.rfl
    have hc₂ : ∀ (S : List (Lab f)) x, x ∈ (S.mergeSort Labels.le).eraseDups ↔ x ∈ S := by
      intro S x; simp only [List.mem_eraseDups, List.mem_mergeSort]
    have hcid : ∀ (S : List Nat) x, x ∈ id S ↔ x ∈ S := fun _ _ => Iff.rfl
    rcases Bool.or_eq_true_iff.mp hi with hi | hi
    · obtain ⟨mp₂, h₂⟩ := Option.isSome_iff_exists.mp hi
      refine ⟨signatureAgrees_of_checks src rfl (graphOf_env f) hc₁ hc₂ h₁ h₂, ?_⟩
      intro r hr
      obtain ⟨_, r₁, -, -, hb₁, hk₁, -, -, -, -, he₁⟩ :=
        StoreMaps.matchStores_sound_builtins hc₁ (env_empty_agree (graphOf_env src.fm) rfl) hr h₁
      obtain ⟨_, r₂, -, -, hb₂, hk₂, -, -, -, -, he₂⟩ :=
        StoreMaps.matchStores_sound_builtins hc₂ (env_empty_agree rfl (graphOf_env f)) hb₁ h₂
      exact ⟨r₂, hb₂, hk₂.trans hk₁, he₂.trans he₁⟩
    · obtain ⟨mp₂, h₂⟩ := Option.isSome_iff_exists.mp hi
      refine ⟨signatureAgrees_of_checks_back src rfl (graphOf_env f) hc₁ hcid h₁ h₂, ?_⟩
      intro r hr
      obtain ⟨_, r₁, -, -, hb₁, hk₁, -, -, -, -, he₁⟩ :=
        StoreMaps.matchStores_sound_builtins hc₁ (env_empty_agree (graphOf_env src.fm) rfl) hr h₁
      obtain ⟨m₂, -, -⟩ := StoreMaps.matchStores_sound hcid (env_empty_agree (graphOf_env f) rfl) h₂
      have hb := m₂.builtins
      rw [hb₁] at hb
      cases hh : (graphOf f).builtins with
      | none => rw [hh] at hb; exact absurd hb (by simp [StoreMaps.BuiltinsRel])
      | some r₂ =>
        rw [hh] at hb
        exact ⟨r₂, rfl, hb.1.symm.trans hk₁, m₂.excOf_eq.symm.trans he₁⟩


/-- **Signature agreement from the cached row-table checks** (proved): where
the module checked its row-table map once (`checkModuleTable`) and the entry's
roots (`checkModuleEntry`), or fell back to `moduleRowsAgree`, and the importer
checked the read against a map verified by `importerRowsMap` (`checkImporterEntry`),
or by `importerRowsMap` directly, the stores agree on the signature and on the
built-in keys and exception family. -/
theorem signatureAgrees_of_cached_rows {e : Entry} (src : EntryRealized e) (t : RowTable) (name : String)
    {f : FilePlans} {A : List (Lab f)}
    {pos : Std.HashMap (Lab src.fm) Nat}
    (hm : (checkModuleTable src.fm.F.store t pos && checkModuleEntry t pos name (src.layout.iface src.unit)) = true ∨
      moduleRowsAgree src.fm.F.store t name (src.layout.iface src.unit) = true)
    (hi : (∃ name₀ A₀ m, importerRowsMap f.F.store t name₀ A₀ = some m ∧ checkImporterEntry t m name A = true) ∨
      (importerRowsMap f.F.store t name A).isSome = true) :
    SignatureAgrees src (graphOf f) A ∧
      ∀ r, (graphOf src.fm).builtins = some r → ∃ r', (graphOf f).builtins = some r' ∧ r'.keys = r.keys ∧
        PositiveRules.excOf (graphOf f) = PositiveRules.excOf (graphOf src.fm) := by
  letI : Inhabited (Lab f) := ⟨Labels.nul⟩
  have hc₁ : ∀ (S : List Nat) x, x ∈ id S ↔ x ∈ S := fun _ _ => Iff.rfl
  have hc₂ : ∀ (S : List (Lab f)) x, x ∈ (S.mergeSort Labels.le).eraseDups ↔ x ∈ S := by
    intro S x; simp only [List.mem_eraseDups, List.mem_mergeSort]
  have hmod : ∃ Is mp₁, t.interfaces.lookup name = some Is ∧
      StoreMaps.checkMap (graphOf src.fm) t.graph id mp₁ (src.layout.iface src.unit) Is = true := by
    rcases hm with hfast | hslow
    · simp only [Bool.and_eq_true, checkModuleTable, checkModuleEntry] at hfast
      cases hl : t.interfaces.lookup name with
      | none => rw [hl] at hfast; exact absurd hfast.2 (by simp)
      | some Is =>
        rw [hl] at hfast
        exact ⟨Is, pos, rfl, StoreMaps.checkMap_of_body_roots hfast.1 hfast.2⟩
    · unfold moduleRowsAgree at hslow
      cases hl : t.interfaces.lookup name with
      | none => rw [hl] at hslow; cases hslow
      | some Is =>
        rw [hl] at hslow
        obtain ⟨mp₁, h₁⟩ := Option.isSome_iff_exists.mp hslow
        unfold StoreMaps.matchStores at h₁
        by_cases hc : StoreMaps.checkMap (graphOf src.fm) t.graph id
            (StoreMaps.propose (graphOf src.fm) t.graph (matchFuel t.rows.size)
              (StoreMaps.startPairs (graphOf src.fm) t.graph (src.layout.iface src.unit) Is) {})
            (src.layout.iface src.unit) Is = true
        · simp only [hc, ↓reduceIte, Option.some.injEq] at h₁
          exact ⟨Is, mp₁, rfl, h₁ ▸ hc⟩
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h₁
  obtain ⟨Is, mp₁, hlookup, hcheck₁⟩ := hmod
  obtain ⟨m₁, hD₁, hI₁⟩ := StoreMaps.checkMap_sound hc₁ (env_empty_agree (graphOf_env src.fm) rfl) hcheck₁
  have himp : (∃ mp₂, StoreMaps.checkMap t.graph (graphOf f) (fun S => (S.mergeSort Labels.le).eraseDups) mp₂ Is A = true) ∨
      (∃ mp₂, StoreMaps.checkMap (graphOf f) t.graph id mp₂ A Is = true) := by
    rcases hi with ⟨name₀, A₀, m, hmap, hentry⟩ | hdirect
    · unfold checkImporterEntry at hentry
      rw [hlookup] at hentry
      unfold importerRowsMap at hmap
      cases hl₀ : t.interfaces.lookup name₀ with
      | none => rw [hl₀] at hmap; cases hmap
      | some I₀ =>
        rw [hl₀] at hmap
        dsimp only at hmap hentry
        cases hf : StoreMaps.matchStores t.graph (StoreView.graph f.F.store) (fun S => (S.mergeSort Labels.le).eraseDups)
            (matchFuel t.rows.size) I₀ A₀ with
        | some mp =>
          rw [hf] at hmap; cases hmap
          exact Or.inl ⟨mp, StoreMaps.checkMap_of_body_roots (StoreMaps.checkMapBody_of_matchStores hf) hentry⟩
        | none =>
          rw [hf] at hmap
          cases hb : StoreMaps.matchStores (StoreView.graph f.F.store) t.graph id (matchFuel t.rows.size) A₀ I₀ with
          | none => rw [hb] at hmap; cases hmap
          | some mp =>
            rw [hb] at hmap; cases hmap
            exact Or.inr ⟨mp, StoreMaps.checkMap_of_body_roots (StoreMaps.checkMapBody_of_matchStores hb) hentry⟩
    · obtain ⟨m, hmap⟩ := Option.isSome_iff_exists.mp hdirect
      unfold importerRowsMap at hmap
      rw [hlookup] at hmap
      dsimp only at hmap
      cases hf : StoreMaps.matchStores t.graph (StoreView.graph f.F.store) (fun S => (S.mergeSort Labels.le).eraseDups)
          (matchFuel t.rows.size) Is A with
      | some mp =>
        unfold StoreMaps.matchStores at hf
        by_cases hc : StoreMaps.checkMap t.graph (StoreView.graph f.F.store) (fun S => (S.mergeSort Labels.le).eraseDups)
            (StoreMaps.propose t.graph (StoreView.graph f.F.store) (matchFuel t.rows.size)
              (StoreMaps.startPairs t.graph (StoreView.graph f.F.store) Is A) {}) Is A = true
        · simp only [hc, ↓reduceIte, Option.some.injEq] at hf
          exact Or.inl ⟨mp, hf ▸ hc⟩
        · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hf
      | none =>
        rw [hf] at hmap
        cases hb : StoreMaps.matchStores (StoreView.graph f.F.store) t.graph id (matchFuel t.rows.size) A Is with
        | none => rw [hb] at hmap; cases hmap
        | some mp =>
          unfold StoreMaps.matchStores at hb
          by_cases hc : StoreMaps.checkMap (StoreView.graph f.F.store) t.graph id
              (StoreMaps.propose (StoreView.graph f.F.store) t.graph (matchFuel t.rows.size)
                (StoreMaps.startPairs (StoreView.graph f.F.store) t.graph A Is) {}) A Is = true
          · simp only [hc, ↓reduceIte, Option.some.injEq] at hb
            exact Or.inr ⟨mp, hb ▸ hc⟩
          · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hb
  have hb_of : ∀ r, (graphOf src.fm).builtins = some r →
      ∃ r₁, t.graph.builtins = some r₁ ∧ r₁.keys = r.keys ∧ PositiveRules.excOf t.graph = PositiveRules.excOf (graphOf src.fm) := by
    intro r hr
    have hb := m₁.builtins
    rw [hr] at hb
    cases ht : t.graph.builtins with
    | none => rw [ht] at hb; exact absurd hb (by simp [StoreMaps.BuiltinsRel])
    | some r₁ => rw [ht] at hb; exact ⟨r₁, rfl, hb.1, m₁.excOf_eq⟩
  rcases himp with ⟨mp₂, hcheck₂⟩ | ⟨mp₂, hcheck₂⟩
  · obtain ⟨m₂, hD₂, hI₂⟩ := StoreMaps.checkMap_sound hc₂ (env_empty_agree rfl (graphOf_env f)) hcheck₂
    refine ⟨fun j V w hw => ?_, fun r hr => ?_⟩
    · rw [m₂.meaning_eq_of_mem hD₂ hI₂, m₁.meaning_eq_of_mem hD₁ hI₁]; exact hw
    · obtain ⟨r₁, ht, hk₁, he₁⟩ := hb_of r hr
      have hb := m₂.builtins
      rw [ht] at hb
      cases hf' : (graphOf f).builtins with
      | none => rw [hf'] at hb; exact absurd hb (by simp [StoreMaps.BuiltinsRel])
      | some r₂ => rw [hf'] at hb; exact ⟨r₂, rfl, hb.1.trans hk₁, m₂.excOf_eq.trans he₁⟩
  · obtain ⟨m₂, hD₂, hI₂⟩ := StoreMaps.checkMap_sound hc₁ (env_empty_agree (graphOf_env f) rfl) hcheck₂
    refine ⟨fun j V w hw => ?_, fun r hr => ?_⟩
    · rw [← m₂.meaning_eq_of_mem hD₂ hI₂, m₁.meaning_eq_of_mem hD₁ hI₁]; exact hw
    · obtain ⟨r₁, ht, hk₁, he₁⟩ := hb_of r hr
      have hb := m₂.builtins
      rw [ht] at hb
      cases hf' : (graphOf f).builtins with
      | none => rw [hf'] at hb; exact absurd hb (by simp [StoreMaps.BuiltinsRel])
      | some r₂ => rw [hf'] at hb; exact ⟨r₂, rfl, hb.1.symm.trans hk₁, m₂.excOf_eq.symm.trans he₁⟩

end Verification.SourceClaimJson.PassUnit
