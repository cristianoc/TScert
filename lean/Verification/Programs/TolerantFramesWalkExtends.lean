import Verification.Programs.TolerantFramesDriverWalk

/-! # Extension of the incoming records of a walk -/
namespace Verification.TolerantFrames
open Verification ControlFlow PositiveGraphs PositiveCertificates LabelStore

/-- Incoming states and implications grow together; merge edges grow by
prepending, and processed edges grow by appending. Label records are separate. -/
structure WalkExtends {ι : Type} (a b : SinglePass.Walk ι) : Prop where
  incoming : ∀ t : Nat, ∃ ns nis,
    (b.incoming[t]?).getD [] = ns ++ (a.incoming[t]?).getD [] ∧
    (b.incomingImpl[t]?).getD [] = nis ++ (a.incomingImpl[t]?).getD [] ∧ ns.length = nis.length
  incomingEdges : ∀ t : Nat, ∃ es,
    (b.incomingEdges[t]?).getD [] = es ++ (a.incomingEdges[t]?).getD []
  edges : ∃ es, b.edges.toList = a.edges.toList ++ es

variable {ι : Type}

theorem WalkExtends.refl (a : SinglePass.Walk ι) : WalkExtends a a :=
  ⟨fun _ => ⟨[], [], rfl, rfl, rfl⟩, fun _ => ⟨[], rfl⟩, ⟨[], (List.append_nil _).symm⟩⟩

theorem WalkExtends.trans {a b c : SinglePass.Walk ι} (hab : WalkExtends a b)
    (hbc : WalkExtends b c) : WalkExtends a c := by
  refine ⟨fun t => ?_, fun t => ?_, ?_⟩
  · obtain ⟨ns, nis, h1, h2, h3⟩ := hab.incoming t
    obtain ⟨ms, mis, g1, g2, g3⟩ := hbc.incoming t
    exact ⟨ms ++ ns, mis ++ nis, by rw [g1, h1, List.append_assoc],
      by rw [g2, h2, List.append_assoc], by simp only [List.length_append, h3, g3]⟩
  · obtain ⟨es, h⟩ := hab.incomingEdges t
    obtain ⟨fs, g⟩ := hbc.incomingEdges t
    exact ⟨fs ++ es, by rw [g, h, List.append_assoc]⟩
  · obtain ⟨es, h⟩ := hab.edges
    obtain ⟨fs, g⟩ := hbc.edges
    exact ⟨es ++ fs, by rw [g, h, List.append_assoc]⟩

/-- Paired incoming states retain their implications under extension. -/
theorem WalkExtends.incoming_mem {a b : SinglePass.Walk ι} (h : WalkExtends a b)
    {t : Nat} {e : SinglePass.State × List (PromiseCalls.Implication ι)}
    (he : e ∈ ((a.incoming[t]?).getD []).zip ((a.incomingImpl[t]?).getD [])) :
    e ∈ ((b.incoming[t]?).getD []).zip ((b.incomingImpl[t]?).getD []) := by
  obtain ⟨ns, nis, h1, h2, h3⟩ := h.incoming t
  rw [h1, h2, List.zip_append h3]
  exact List.mem_append_right _ he

/-- Every recorded merge edge remains available. -/
theorem WalkExtends.merge_mem {a b : SinglePass.Walk ι} (h : WalkExtends a b) {t : Nat}
    {e : List (ProgramTyping.Ty ι) × List (PromiseCalls.Implication ι) × PointClaims.Mapping}
    (he : e ∈ (a.incomingEdges[t]?).getD []) : e ∈ (b.incomingEdges[t]?).getD [] := by
  obtain ⟨es, hh⟩ := h.incomingEdges t
  rw [hh]
  exact List.mem_append_right _ he

/-- Every processed edge remains available. -/
theorem WalkExtends.edge_mem {a b : SinglePass.Walk ι} (h : WalkExtends a b)
    {e : SinglePass.EdgeWalk ι} (he : e ∈ a.edges.toList) : e ∈ b.edges.toList := by
  obtain ⟨es, hh⟩ := h.edges
  rw [hh]
  exact List.mem_append_left _ he

end Verification.TolerantFrames
