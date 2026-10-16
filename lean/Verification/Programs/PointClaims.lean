import Verification.Programs.ProgramCertificates

/-! Supplied point environments with checked incoming edges. Environment slots
keep their de Bruijn positions: an edge can widen slots and forget a suffix,
but cannot silently reorder values. No join or invariant inference is performed.
Explicit mappings additionally support selection, reordering and alias retention.
Every checker here takes a proved instance image checker (`InstanceImageCheck`);
the finite one is the default. -/
namespace Verification.PointClaims
open ProgramTyping PositiveGraphs PositiveRules ProgramCertificates
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

abbrev EdgeEvidence (ι : Type) := List (PositiveCertificates.SubtypeChoices ι)

/-- Check incoming slots against outgoing contracts, retaining unfinished comparisons. -/
@[nospecialize] def checkEdgeResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) :
    List (Ty ι) → List (Ty ι) → EdgeEvidence ι → CheckResult ι Unit
  | _, [], [] => pure ()
  | A :: Γ, B :: Δ, p :: ps =>
    (ProgramCertificates.checkSubtypeUsing G images A B p).bind fun _ => checkEdgeResult G images Γ Δ ps
  | _, _, _ => failure

@[nospecialize] def checkEdgeUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (ps : EdgeEvidence ι) : Bool :=
  (checkEdgeResult G images Γ Δ ps).accepted

theorem checkEdgeUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (ps : EdgeEvidence ι) :
    checkEdgeUsing G images Γ Δ ps = match Γ, Δ, ps with
    | _, [], [] => true
    | A :: Γ, B :: Δ, p :: ps =>
        PositiveCertificates.checkUsing G images A B p && checkEdgeUsing G images Γ Δ ps
    | _, _, _ => false := by
  cases Γ <;> cases Δ <;> cases ps <;>
    simp only [checkEdgeUsing, checkEdgeResult, CheckResult.accepted_bind,
      ProgramCertificates.checkSubtypeUsing_accepted] <;> rfl

/-- Coverage is per slot, with no least-upper-bound operation: each outgoing
slot's type contains its incoming slot's, as families. -/
def Covers (G : NormalGraph ι) (Γ Δ : List (Ty ι)) : Prop :=
  ∀ (i : Nat) B, Δ[i]? = some B → ∃ A, Γ[i]? = some A ∧ FamLe (meaning G A) (meaning G B)

theorem checkEdge_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {Γ Δ ps} (hc : checkEdgeUsing G images Γ Δ ps = true) : Covers G Γ Δ := by
  induction Δ generalizing Γ ps with
  | nil => simp [Covers]
  | cons B Δ ih =>
    cases Γ with
    | nil => cases ps <;> simp [checkEdgeUsing_eq] at hc
    | cons A Γ =>
      cases ps with
      | nil => simp [checkEdgeUsing_eq] at hc
      | cons p ps =>
        rw [checkEdgeUsing_eq] at hc
        simp only [Bool.and_eq_true] at hc
        intro i C hi
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst C
          exact ⟨A, rfl, PositiveCertificates.acceptedUsing hc.1⟩
        | succ i =>
          obtain ⟨D, hd, hs⟩ := ih hc.2 i C hi
          exact ⟨D, hd, hs⟩

/-- Explicit maps belong to the program: target slot i receives source slot
`slots[i]`. None preserves positions. Repetition retains aliases, never copies
heap contents. Out-of-range slots are rejected by the checker. -/
abbrev Mapping := Option (List Nat)

def slot (mapping : Mapping) (i : Nat) : Nat :=
  match mapping with
  | none => i
  | some slots => slots[i]?.getD 0

def mapEnv (mapping : Mapping) (ρ : Env) : Env := fun i => ρ (slot mapping i)

def MappedCovers (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (mapping : Mapping) : Prop :=
  ∀ i B, Δ[i]? = some B → ∃ A, Γ[slot mapping i]? = some A ∧ FamLe (meaning G A) (meaning G B)

/-- A mapped slot names existing source, target and evidence entries. -/
@[nospecialize] def checkSlotResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (source target : Option (Ty ι)) (evidence : Option (PositiveCertificates.SubtypeChoices ι)) : CheckResult ι Unit :=
  match source, target, evidence with
  | some A, some B, some p => ProgramCertificates.checkSubtypeUsing G images A B p
  | _, _, _ => failure

theorem checkSlotResult_accepted [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (source target : Option (Ty ι)) (evidence : Option (PositiveCertificates.SubtypeChoices ι)) :
    (checkSlotResult G images source target evidence).accepted = match source, target, evidence with
    | some A, some B, some p => PositiveCertificates.checkUsing G images A B p
    | _, _, _ => false := by
  cases source <;> cases target <;> cases evidence <;>
    simp only [checkSlotResult, ProgramCertificates.checkSubtypeUsing_accepted] <;> rfl

@[nospecialize] def checkMappedResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (mapping : Mapping) (ps : EdgeEvidence ι) : CheckResult ι Unit :=
  match mapping with
  | none => checkEdgeResult G images Γ Δ ps
  | some slots =>
      (CheckResult.ofBool (decide (slots.length = Δ.length ∧ ps.length = Δ.length))).bind fun _ =>
      CheckResult.all (List.range Δ.length) fun i =>
        checkSlotResult G images Γ[slot mapping i]? Δ[i]? ps[i]?

@[nospecialize] def checkMappedUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (mapping : Mapping) (ps : EdgeEvidence ι) : Bool :=
  (checkMappedResult G images Γ Δ mapping ps).accepted

theorem checkMappedUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (mapping : Mapping) (ps : EdgeEvidence ι) :
    checkMappedUsing G images Γ Δ mapping ps =
  match mapping with
  | none => checkEdgeUsing G images Γ Δ ps
  | some slots => decide (slots.length = Δ.length ∧ ps.length = Δ.length) &&
      (List.range Δ.length).all (fun i =>
        match Γ[slot mapping i]?, Δ[i]?, ps[i]? with
        | some A, some B, some p => PositiveCertificates.checkUsing G images A B p
        | _, _, _ => false) := by
  cases mapping <;> simp only [checkMappedUsing, checkMappedResult, CheckResult.accepted_bind,
    CheckResult.accepted_ofBool, CheckResult.accepted_all, checkSlotResult_accepted]
  rfl

theorem checkMapped_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {Γ Δ mapping ps}
    (hc : checkMappedUsing G images Γ Δ mapping ps = true) : MappedCovers G Γ Δ mapping := by
  cases mapping with
  | none => exact checkEdge_sound hc
  | some slots =>
    simp only [checkMappedUsing_eq, Bool.and_eq_true, List.all_eq_true] at hc
    intro i B hi
    have h := hc.2 i (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1)
    rw [hi] at h
    cases ha : Γ[slot (some slots) i]? with
    | none => simp [ha] at h
    | some A =>
      cases hp : ps[i]? with
      | none => simp [ha, hp] at h
      | some p => exact ⟨A, rfl, PositiveCertificates.acceptedUsing (by simpa [ha, hp] using h)⟩

theorem MappedCovers.env {G : NormalGraph ι} {Γ Δ mapping ρ n W}
    (hc : MappedCovers G Γ Δ mapping) (he : EnvOk G Γ ρ n W) :
    EnvOk G Δ (mapEnv mapping ρ) n W := by
  refine ⟨fun i => he.1 (slot mapping i), ?_⟩
  intro i B hi
  obtain ⟨A, ha, hab⟩ := hc i B hi
  exact hab n W (ρ (slot mapping i)) (he.2 _ A ha)

end Verification.PointClaims
