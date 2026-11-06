import Verification.Programs.Linking
import Verification.Programs.ProgramCertificates

/-! # Finite assembly data for one frozen graph

The table names each capture's export and a dependency rank. This closed
assembly fragment admits function links in every capture slot. External
captures require a separate checked contract and are refused here.
-/
namespace Verification.Linking.Assembly
open Lean PositiveGraphs PositiveRules PositiveNormalization ProgramTyping

structure Data where
  ranks : List Nat
  slots : List (List (Option Nat))
  deriving ToJson, FromJson, Repr

/-- Put every concrete export in the graph the assembly checks. -/
@[nospecialize] def family (G : NormalGraph ι) (es : Fin count → Export ι) :
    (i : Fin count) → Export ι := fun i => { es i with graph := G }

/-- The scope check and binding predicate describe the same free slots. -/
theorem checkScope_iff (d : Nat) (t : Tm) :
    ProgramCertificates.checkScope d t = true ↔ Scoped d t := by
  induction t using Tm.induct generalizing d <;>
    simp_all [ProgramCertificates.checkScope, ProgramCertificates.checkScopes_iff,
      Scoped, scopedArgs_iff, and_assoc]

@[nospecialize] def slotCheck [DecidableEq ι] (es : Fin count → Export ι) (a : Data)
    (i : Fin count) (k : Fin (es i).captureTypes.length) : Bool :=
  match (a.slots[i.val]?).bind (·[k.val]?) with
  | some (some j) =>
    if h : j < count then
      decide (a.ranks.getD j 0 < a.ranks.getD i.val 0 ∧
        envOf (es i).captures .nul k.val = (es ⟨j,h⟩).value ∧
        (es i).captureTypes[k.val] = (es ⟨j,h⟩).signature)
    else false
  | _ => false

/-- Structural checking consumes the concrete closure family and the complete
slot table. `certified` checks each exact invocation body separately. -/
@[nospecialize] def check [DecidableEq ι] (G : NormalGraph ι) (es : Fin count → Export ι)
    (a : Data) (certified : Fin count → Bool) : Bool :=
  decide (a.ranks.length = count ∧ a.slots.length = count) &&
    (List.finRange count).all fun i =>
      certified i && decide ((es i).captureTypes.length = (es i).captures.length) &&
      ProgramCertificates.checkScopes 0 (es i).captures && (es i).captures.all isVal &&
      decide (expand G (es i).signature = [.arrs (es i).arrows (es i).rests]) &&
      decide (KindOffers G (es i).kind (es i).arrows (es i).rests) &&
      decide ((a.slots[i.val]?).map List.length = some (es i).captureTypes.length) &&
      (List.finRange (es i).captureTypes.length).all (slotCheck es a i)

/-- A successful structural check, together with the body checker's proved
soundness, yields `WellLinked`. The slot checker compares concrete values,
labels and ranks; no capture contract or export membership is a premise. -/
theorem check_sound [DecidableEq ι] {G : NormalGraph ι} {es : Fin count → Export ι}
    {a : Data} {certified : Fin count → Bool}
    (code : ∀ i, certified i = true → CodeOffers G (es i).arity
      (es i).expressions (es i).continuations (es i).start
      ((es i).captureTypes ++ [(es i).signature]) false (es i).arrows (es i).rests [])
    (h : check G es a certified = true) : Nonempty (WellLinked (family G es)) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have rows := fun i => h.2 i (List.mem_finRange i)
  constructor
  refine {
    rank := fun i => a.ranks.getD i.val 0
    layout := fun i => (rows i).1.1.1.1.1.1.2
    closed := ?_
    values := ?_
    represents := fun i => (rows i).1.1.1.2
    kind := fun i => (rows i).1.1.2
    code := fun i => code i (rows i).1.1.1.1.1.1.1
    slots := ?_ }
  · intro i v hv
    exact (checkScope_iff 0 v).mp
      ((ProgramCertificates.checkScopes_iff _ _).mp (rows i).1.1.1.1.1.2 v hv)
  · intro i v hv
    exact (rows i).1.1.1.1.2 v hv
  · intro i k A hA
    obtain ⟨hk, ha⟩ := List.getElem_of_getElem? hA
    have hs := (rows i).2 ⟨k,hk⟩ (List.mem_finRange _)
    unfold slotCheck at hs
    split at hs
    · rename_i j hj
      split at hs
      · rename_i bound
        have hs := of_decide_eq_true hs
        right
        refine ⟨⟨j,bound⟩, hs.1, hs.2.1, ?_⟩
        have eqTy : A = (es ⟨j,bound⟩).signature := by
          exact ha.symm.trans hs.2.2
        intro n W v
        simp [family, eqTy]
      · cases hs
    · cases hs

end Verification.Linking.Assembly
