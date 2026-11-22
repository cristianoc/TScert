import Verification.Source.Claims.CallbackGraphDispatch
namespace Verification.SourceClaimJson.CallbackInferencePlan
open Footprints

private theorem prefix_get {h h' : Heap} (extendsBy : h.IsPrefix h') {i : Nat} {v : Tm}
    (old : h[i]? = some v) : h'[i]? = some v := by
  obtain ⟨_,rfl⟩ := extendsBy
  simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp old).1] using old

private theorem path_prefix {h h' : Heap} (extendsBy : h.IsPrefix h') {v p w}
    (old : HeapKnowledge.readPath h v p = some w) : HeapKnowledge.readPath h' v p = some w := by
  induction p generalizing v with
  | nil => exact old
  | cons f p ih =>
    cases v <;> try contradiction
    rename_i fs c oid
    simp only [HeapKnowledge.readPath] at old ⊢
    cases key : fs.lookup (.str f) with
    | none => simp [key] at old
    | some loc =>
      cases hit : h[loc]? with
      | none => simp [key,hit] at old
      | some v => simpa [key,prefix_get extendsBy hit] using ih (by simpa [key,hit] using old)

private theorem cells_prefix {h h' : Heap} (extendsBy : h.IsPrefix h') {v x}
    (old : x ∈ spineCells h v) : x ∈ spineCells h' v := by
  have entries (o : Option Nat) (hit : x ∈ entriesAt h o) : x ∈ entriesAt h' o := by
    cases o with
    | none => contradiction
    | some l =>
      cases found : h[l]? with
      | none => simp [entriesAt,found] at hit
      | some t => simpa only [entriesAt,found,prefix_get extendsBy found] using hit
  exact (List.mem_append.mp old).elim (fun a => List.mem_append_left _ (entries _ a))
    (fun a => List.mem_append_right _ (entries _ a))

private theorem region_prefix {h h' : Heap} {ρ r l} (extendsBy : h.IsPrefix h') (bound : l < h.length)
    (old : Region.mem ρ h r l = true) : Region.mem ρ h' r l = true := by
  have get : h'[l]? = h[l]? := by obtain ⟨_,rfl⟩ := extendsBy; exact List.getElem?_append_left bound
  induction r with
  | field | fields => exact old
  | all => exact decide_eq_true (Nat.lt_of_lt_of_le bound extendsBy.length_le)
  | cls => simpa only [Region.mem,get] using old
  | inCls r c ih => exact Bool.and_eq_true_iff.mpr ⟨ih (Bool.and_eq_true_iff.mp old).1,by simpa only [get] using (Bool.and_eq_true_iff.mp old).2⟩
  | cells => exact List.contains_iff_mem.mpr (cells_prefix extendsBy (List.contains_iff_mem.mp old))
  | path x p key | pathFields x p | pathCells x p | spine x p =>
    cases hit : HeapKnowledge.readPath h (ρ x) p with
    | none => simp only [Region.mem,hit] at old; contradiction
    | some v =>
      simp only [Region.mem,hit] at old
      simp only [Region.mem,path_prefix extendsBy hit]
      first | exact old | exact List.contains_iff_mem.mpr (cells_prefix extendsBy (List.contains_iff_mem.mp old))

/-- A rest-spine allocation only appends cells; every protected old
location satisfies any bound its subsequent callback execution satisfies. -/
theorem supported_after_prefix {h entry after ρ S} (extendsBy : h.IsPrefix entry)
    (body : Supported S ρ entry after) : Supported S ρ h after := by
  intro e mem l v hr old
  obtain ⟨v',hv,change⟩ := body e mem l v
    (region_prefix extendsBy (List.getElem?_eq_some_iff.mp old).1 hr) (prefix_get extendsBy old)
  exact ⟨v',hv,change.lower extendsBy.length_le⟩
end Verification.SourceClaimJson.CallbackInferencePlan
