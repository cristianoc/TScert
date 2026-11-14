import Verification.Semantics.HeapAtoms
import Verification.Semantics.ValueSets

/-! Finite current-content assertions. They constrain the current heap, never
change a world's contract, and carry no ownership or disjointness promise.
Edge entailment selects facts by runtime-environment slots and weakens their
primitive predicates. The representation has no execution indices in its syntax. -/
namespace Verification.HeapFacts
open ProgramTyping PositiveRules PositiveGraphs HeapObservations

/-- The result of an own-property read. An absent key yields undefined when
there is no prototype to consult. -/
def ReadGave (flds : List (PropKey × Nat)) (field : PropKey) (h : Heap) (v : Tm) : Prop :=
  match flds.lookup field with
  | some l => h[l]? = some v
  | none => flds.lookup CallArguments.protoField = none ∧ v = .undef

theorem ReadGave.present {flds field h l v} (hf : flds.lookup field = some l)
    (hv : h[l]? = some v) : ReadGave flds field h v := by simp [ReadGave, hf, hv]

/-- A read gives one value: the object's lookup of the field, or `undefined`
where the object has no prototype and no such field. -/
theorem ReadGave.unique {flds : List (PropKey × Nat)} {f : PropKey} {h : Heap} {u v : Tm}
    (hu : ReadGave flds f h u) (hv : ReadGave flds f h v) : u = v := by
  unfold ReadGave at hu hv
  cases hl : flds.lookup f with
  | some l =>
    rw [hl] at hu hv
    simp only at hu hv
    rw [hu] at hv; exact Option.some.inj hv
  | none => rw [hl] at hu hv; rw [hu.2, hv.2]

theorem ReadGave.alloc_frames {flds field h v} (vs : List Val) (hr : ReadGave flds field h v) :
    ReadGave flds field (h ++ vs) v := by
  unfold ReadGave at hr ⊢
  cases hl : flds.lookup field with
  | some l => rw [hl] at hr; exact HeapObservations.alloc_frames vs hr
  | none => rw [hl] at hr; exact hr

theorem ReadGave.step {flds field h v c oid} (hr : ReadGave flds field h v) :
    Step h (.readAt field (.objAt flds c oid)) h v := by
  unfold ReadGave at hr
  cases hf : flds.lookup field with
  | some l => rw [hf] at hr; exact .readField hf hr
  | none => rw [hf] at hr; rw [hr.2]; exact .readMissing hf hr.1

/-- **A stable key frames its read** (HOST-FAMILIES.md, "Stable links"):
what a read of a key the object reads one way for its life (`StableAt`) gave,
every heap a normally returning execution reaches gives again. A present
key's location holds its contract's one value
(`HeapObservations.stable_frame`); an absent key of an object without a
prototype reads `undefined` from the value alone. A thrown outcome carries no
postcondition, so this supplies nothing to an exceptional edge. -/
theorem ReadGave.stable_frame {T Q} {flds : List (PropKey × Nat)} {field : PropKey} {u : Tm} :
    ∀ {n W h t}, StableAt W flds field → HeapOk n W h → ReadGave flds field h u →
      HeapObservations.SafePost Ξ T Q n W h t →
      HeapObservations.SafePost Ξ T (fun h' v => Q h' v ∧ ReadGave flds field h' u) n W h t := by
  intro n W h t hs hh hr hp
  cases n with
  | zero => trivial
  | succ n =>
    unfold ReadGave at hr
    cases hl : flds.lookup field with
    | none =>
      rw [hl] at hr
      exact HeapObservations.consequence (fun _ _ _ h => h)
        (fun _ _ hq => ⟨hq, by simp only [ReadGave, hl]; exact hr⟩) hp
    | some l =>
      rw [hl] at hr
      obtain ⟨c, value, hw, hc⟩ := hs.present hl
      have hval := hh.stable_value (Nat.zero_lt_succ n) hw hc
      rw [hr] at hval
      obtain rfl := Option.some.inj hval
      exact HeapObservations.consequence (fun _ _ _ h => h)
        (fun _ _ hq => ⟨hq.1, ReadGave.present hl hq.2⟩) (HeapObservations.stable_frame hw hc hh hp)

/-- A property-read observation at the current heap. The field may be absent.
Value facts reuse the shape and ignore the field. -/
structure Fact where
  slot : Nat
  contents : ValueSets.ValueSet
  field : PropKey := valueField
  deriving DecidableEq, Repr

abbrev Facts := List Fact

def Holds (facts : Facts) (ρ : Env) (h : Heap) : Prop :=
  ∀ f ∈ facts, ∃ flds c oid v, ρ f.slot = .objAt flds c oid ∧ ReadGave flds f.field h v ∧ f.contents.mem v = true

theorem holds_nil (ρ h) : Holds [] ρ h := by simp [Holds]

/-- All target facts must have an incoming justification. Repeated slot maps
retain aliases; different slot numbers do not imply different locations. -/
def check (source target : Facts) (mapping : PointClaims.Mapping) : Bool :=
  target.all fun f =>
    let s := PointClaims.slot mapping f.slot
    source.any fun g => g.slot == s && g.field == f.field && g.contents.le f.contents

theorem check_sound {source target mapping ρ h}
    (hc : check source target mapping = true) (hs : Holds source ρ h) :
    Holds target (PointClaims.mapEnv mapping ρ) h := by
  intro f hmem
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc f hmem)
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨flds,c,oid,v,hl,hr,hm⟩ := hs g hg
  refine ⟨flds,c,oid,v,?_,?_,ValueSets.ValueSet.le_sound hc.2 hm⟩
  · simpa [PointClaims.mapEnv,hc.1.1] using hl
  · rw [← hc.1.2]; exact hr

/-- The value added by a bind shifts every old environment slot. -/
def shift (facts : Facts) : Facts := facts.map fun f => { f with slot := f.slot+1 }

theorem shift_holds {facts ρ h v} (hf : Holds facts ρ h) :
    Holds (shift facts) (push v ρ) h := by
  intro f hm
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
  exact hf g hg

/-- A read's value is a heap location's contents or `undefined`: its
references are valid where the heap is well formed. -/
theorem ReadGave.refs {flds field h v n W} (hr : ReadGave flds field h v) (hh : HeapOk n W h) :
    RefsOk W v := by
  unfold ReadGave at hr
  split at hr
  · exact hh.refs_at hr
  · rw [hr.2]; exact RefsOk_undef

/-- A read observation gives both its value and its unchanged heap. -/
theorem ReadGave.observed {flds field h v c oid n W}
    (hr : ReadGave flds field h v) (hv : isVal v = true)
    (hw : WorldAdm W) (hh : HeapOk n W h) (href : RefsOk W (.readAt field (.objAt flds c oid))) :
    SafePost Ξ (exact v) (fun h' u => h' = h ∧ u = v) n W h
      (.readAt field (.objAt flds c oid)) := by
  cases n with
  | zero => exact href
  | succ n =>
    have hvr : RefsOk (trunc n (Nat.le_succ n) W) v := RefsOk_trunc _ (hr.refs hh)
    exact ⟨href, .inr ⟨trunc n (Nat.le_succ n) W, h, v, WExt_refl _,
      WorldAdm_trunc _ hw, hr.step, HeapOk_trunc n W h hh,
      HeapObservations.value hv rfl ⟨rfl, rfl⟩ hvr⟩⟩

end Verification.HeapFacts
