import Verification.Paper.TolerantFrames.PathSupports
import Verification.Paper.TolerantFrames.Admission
import Verification.Paper.TolerantFrames.KindsModelRules

/-! # A failed path's vacuous freshness need not survive reads_keep

All six locations predate the invocation mark. Initially x.f is null; y.g
holds the old array a. The only change puts y into x.f. The intermediate grow
entry permits this scalar step, and the last field's region was empty. Thus
fresh(x.f.g.spine) changes from vacuously true to false. No new axiom or changed
paper rule makes this into a valid freshness-support theorem.
-/
namespace Verification.Paper.TolerantFrames.FreshnessCounterexample
open Verification Footprints HeapKnowledge TolerantFrames
open Verification.Kinds (roleWorld roleAt_roleWorld roleWorld_meets)

private def roles : List Role := [.spine .array, .field, .identity, .identity, .field, .identity]
private def array : Val := .objAt [(arraySpineKey, 0)] .absent 2
private def oldObject : Val := .objAt [("g", 1)] .absent 3
private def root : Val := .objAt [("f", 4)] .absent 5
private def heap (changed : Bool) : Heap := [.arr [], array, .nul, .nul, if changed then oldObject else .nul, .nul]
private def env : Env
  | 0 => root
  | 1 => oldObject
  | _ => .undef
private def omitted : OmittedFields := fun _ _ => false
private def path : Parity.Path := ⟨0, ["f", "g"]⟩
private def region : Region := .spine 0 ["f", "g"]

private theorem array_refs {n : Nat} : RefsOk (roleWorld (k := n) roles) array := by
  intro r hr
  simp only [array, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp [RefOk, SlotRole, roleAt_roleWorld, roles]

private theorem object_refs {n : Nat} : RefsOk (roleWorld (k := n) roles) oldObject := by
  intro r hr
  simp only [oldObject, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp [RefOk, SlotRole, roleAt_roleWorld, roles, arraySpineKey]

private theorem root_refs {n : Nat} : RefsOk (roleWorld (k := n) roles) root := by
  intro r hr
  simp only [root, refs, objRefs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp [RefOk, SlotRole, roleAt_roleWorld, roles, arraySpineKey]

private theorem heap_ok (changed : Bool) (n : Nat) : HeapOk n (roleWorld roles) (heap changed) := by
  refine ⟨roleWorld_meets rfl (by cases changed <;> simp [heap, array, oldObject, isVal]), fun l r hr => ?_⟩
  rw [roleAt_roleWorld] at hr
  rcases l with _ | _ | _ | _ | _ | _ | l <;> simp [roles] at hr <;> subst hr <;>
    cases changed <;> refine ⟨_, rfl, ?_, ?_⟩ <;>
    first
      | exact array_refs
      | exact object_refs
      | exact RefsOk_of_nil rfl
      | simp [Cat, isSourceVal, array, oldObject]

private theorem world_adm (n : Nat) : WorldAdm (roleWorld (k := n) roles) := by
  refine ⟨fun l c hc => ?_, fun l f N hr => ?_⟩
  · simp only [lookup, toList, roleWorld, entries_ofEntries, List.map_map, List.getElem?_map,
      Option.map_eq_some_iff, Function.comp_apply] at hc
    obtain ⟨r, _, rfl⟩ := hc
    exact ⟨fun _ _ _ _ _ _ hv => hv, fun _ _ _ _ hv => hv⟩
  · rw [roleAt_roleWorld] at hr
    rcases l with _ | _ | _ | _ | _ | _ | l <;> simp [roles] at hr

private def state (changed : Bool) : IndexedHeap :=
  ⟨1, roleWorld roles, heap changed, Nat.one_pos, world_adm 1, heap_ok changed 1⟩

private theorem valid (changed : Bool) : ValidContext env 6 (state changed) := by
  refine ⟨?_, ?_, by cases changed <;> decide⟩
  · intro x
    rcases x with _ | _ | x
    · exact root_refs
    · exact object_refs
    · exact RefsOk_undef
  · intro x
    rcases x with _ | _ | x <;> rfl

private theorem transition : Admissible (state false) (state true) := by
  change WorldReach (roleWorld (k := 1) roles) (roleWorld roles)
  exact WorldReach.refl _

private theorem constraints : Supported (reads omitted .keep path) env (state false).h (state true).h := by
  intro e he l v hm hv
  simp [reads, readsFrom, fieldReads, omitted, path] at he
  rcases he with rfl | rfl
  · simp [fieldRegion, Region.mem, env, root, fieldsOf] at hm
    subst l
    have hv' : v = .nul := by simpa [state, heap] using hv.symm
    subst v
    refine ⟨oldObject, rfl, ?_⟩
    exact .inr (.inr (.inl ⟨rfl, rfl, rfl⟩))
  · simp [fieldRegion, Region.mem, env, root, readPath, state, heap, fieldsOf] at hm

private theorem fresh_before : (Formula.fresh region).Holds env 6 (state false) := by
  intro l hm
  simp [region, Region.mem, env, root, readPath, state, heap] at hm

private theorem not_fresh_after : ¬ (Formula.fresh region).Holds env 6 (state true) := by
  intro h
  have h0 := h 0 (by decide)
  exact (by decide : ¬ 6 ≤ 0) h0

/-- These are the classifications of x:{f:{g:array}|null}. The nullable
intermediate is an object path, and x.f.g is a collection path. -/
private def types : DeclaredPaths where
  collection p := p.root = 0 ∧ p.fields = ["f", "g"]
  object p := p.root = 0 ∧ (p.fields = [] ∨ p.fields = ["f"])
  field p f := p.root = 0 ∧ ((p.fields = [] ∧ f = "f") ∨ (p.fields = ["f"] ∧ f = "g"))

/-- Neither the fresh region nor its proposed support uses malformed regions. -/
theorem admitted : (Formula.fresh region).WellFormed types ∧ EffectWellFormed types (reads omitted .keep path) := by
  refine ⟨RegionWellFormed.spine ⟨rfl, rfl⟩, ?_⟩
  intro e he
  simp [reads, readsFrom, fieldReads, omitted, path] at he
  rcases he with rfl | rfl
  · exact RegionWellFormed.field ⟨rfl, .inl rfl⟩ ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  · exact RegionWellFormed.field ⟨rfl, .inr rfl⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩

/-- A concrete valid-context admissible countermodel to the unconditional
freshness row with grow at intermediate reads. All old locations are kept
except the one permitted null-to-old-object change. -/
theorem failed_path_freshness_not_supported :
    ¬ Supports (OmissionCondition omitted) (Formula.fresh region).meaning (reads omitted .keep path) := by
  intro hs
  have hc : OmissionCondition omitted env 6 (state false) (state true) := by
    intro p f h; cases h
  exact not_fresh_after (hs env 6 (state false) (state true) transition ⟨valid false, hc⟩ fresh_before constraints)

end Verification.Paper.TolerantFrames.FreshnessCounterexample
