import Verification.Paper.TolerantFrames.AtomSupports

/-! # The table's restricted quantified-body support

Definition 14's Every row is for an ordinary-array receiver and a body over
unshifted numeric z[i] and index-independent terms. The judgment below gives
no constructor to the body index, shifted reads, string projections or fields.
Disjunction preserves only the branch that holds, not definedness of all
alternatives. The unrestricted assertion language retains all_support.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge TolerantFrames
open Verification.Parity (Path)

inductive BodyTermSupport (omitted : OmittedFields) : BodyTerm → Footprint → Prop where
  | element : BodyTermSupport omitted (.element 0) []
  | projectValue : BodyTermSupport omitted (.project .value [] (.inl rfl)) []
  | free {t S} : TermExactSupport omitted t S → BodyTermSupport omitted (.free t) S

inductive BodyExpressionSupport (omitted : OmittedFields) : BodyExpression → Footprint → Prop where
  | constant (n : Int) : BodyExpressionSupport omitted (.constant n) []
  | scale {t S} (c : Int) : BodyTermSupport omitted t S → BodyExpressionSupport omitted (.scale c t) S
  | add {e f S T} : BodyExpressionSupport omitted e S → BodyExpressionSupport omitted f T →
      BodyExpressionSupport omitted (.add e f) (S ++ T)

inductive ClauseSupport (omitted : OmittedFields) : Clause → Footprint → Prop where
  | le {e f S T} : BodyExpressionSupport omitted e S → BodyExpressionSupport omitted f T →
      ClauseSupport omitted (.le e f) (S ++ T)
  | or {c d S T} : ClauseSupport omitted c S → ClauseSupport omitted d T → ClauseSupport omitted (.or c d) (S ++ T)

inductive BodySupport (omitted : OmittedFields) : Body → Footprint → Prop where
  | clause {c S} : ClauseSupport omitted c S → BodySupport omitted (.clause c) S
  | and {b c S T} : BodySupport omitted b S → BodySupport omitted c T → BodySupport omitted (.and b c) (S ++ T)

/-- The array domain stated explicitly by the support table, not inferred
from Every's general collection semantics. -/
def ArrayReceiver (z : Path) (ρ : Env) (h : Heap) : Prop :=
  ∃ v st es, z.read ρ h = some v ∧ Parity.ArraySpine h v st es

def EverySupportCondition (omitted : OmittedFields) (z : Path) : ConditionOn IndexedHeap :=
  fun ρ m s t => OmissionCondition omitted ρ m s t ∧ ArrayReceiver z ρ s.h

private theorem support_left {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported S ρ h h' := fun e he => hs e (List.mem_append_left _ he)
private theorem support_right {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported T ρ h h' := fun e he => hs e (List.mem_append_right _ he)

theorem BodyTermSupport.sound {omitted t S} (ht : BodyTermSupport omitted t S) {ρ m s u z v i n}
    (hc : OmissionCondition omitted ρ m s u) (hp : z.read ρ s.h = some v)
    (hcol : Supported (collectionReads z) ρ s.h u.h) (hs : Supported S ρ s.h u.h)
    (he : t.eval ρ s.h v i = some n) : t.eval ρ u.h v i = some n := by
  cases ht with
  | free ht => exact ht.sound hc hs he
  | element =>
    simp only [BodyTerm.eval, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨w, hw, hn⟩ := he
    exact ⟨w, elementValue_supported hp hcol hw, hn⟩
  | projectValue =>
    simp only [BodyTerm.eval, readPath, Option.bind_some, kindValue, Option.bind_eq_some_iff] at he ⊢
    obtain ⟨w, hw, hn⟩ := he
    exact ⟨w, elementValue_supported hp hcol hw, hn⟩

theorem BodyExpressionSupport.sound {omitted e S} (he : BodyExpressionSupport omitted e S) {ρ m s u z v i n}
    (hc : OmissionCondition omitted ρ m s u) (hp : z.read ρ s.h = some v)
    (hcol : Supported (collectionReads z) ρ s.h u.h) (hs : Supported S ρ s.h u.h)
    (hv : e.eval ρ s.h v i = some n) : e.eval ρ u.h v i = some n := by
  induction he generalizing n with
  | constant _ => exact hv
  | scale c ht =>
    simp only [BodyExpression.eval, Option.map_eq_some_iff] at hv ⊢
    obtain ⟨n, hn, hv⟩ := hv
    exact ⟨n, ht.sound hc hp hcol hs hn, hv⟩
  | add he hf ihe ihf =>
    simp only [BodyExpression.eval, bind, pure, Option.bind_eq_some_iff] at hv ⊢
    obtain ⟨a, ha, b, hb, hv⟩ := hv
    exact ⟨a, ihe (support_left hs) ha, b, ihf (support_right hs) hb, hv⟩

theorem ClauseSupport.sound {omitted c S} (hc' : ClauseSupport omitted c S) {ρ m s u z v i}
    (hc : OmissionCondition omitted ρ m s u) (hp : z.read ρ s.h = some v)
    (hcol : Supported (collectionReads z) ρ s.h u.h) (hs : Supported S ρ s.h u.h)
    (hv : c.Holds ρ s.h v i) : c.Holds ρ u.h v i := by
  induction hc' with
  | le he hf =>
    obtain ⟨a, b, ha, hb, hab⟩ := hv
    exact ⟨a, b, he.sound hc hp hcol (support_left hs) ha,
      hf.sound hc hp hcol (support_right hs) hb, hab⟩
  | or he hf ihe ihf => exact hv.imp (ihe (support_left hs)) (ihf (support_right hs))

theorem BodySupport.sound {omitted b S} (hb : BodySupport omitted b S) {ρ m s u z v i}
    (hc : OmissionCondition omitted ρ m s u) (hp : z.read ρ s.h = some v)
    (hcol : Supported (collectionReads z) ρ s.h u.h) (hs : Supported S ρ s.h u.h)
    (hv : b.Holds ρ s.h v i) : b.Holds ρ u.h v i := by
  induction hb with
  | clause hc' => exact hc'.sound hc hp hcol hs hv
  | and hb hc' ihb ihc => exact ⟨ihb (support_left hs) hv.1, ihc (support_right hs) hv.2⟩

/-- Conditional support on precisely the table's array/body domain. The
separate bridge from declared array typing to ArrayReceiver is not inferred. -/
theorem every_array_support {omitted : OmittedFields} {bound : Expression} {body : Body} {S T : Footprint}
    (hb : ExpressionExactSupport omitted bound S) (hbody : BodySupport omitted body T) (z : Path) :
    Supports (EverySupportCondition omitted z) (Formula.atom (.every z bound body)).meaning
      (((reads omitted .grow z ++ collectionReads z) ++ S) ++ T) := by
  intro ρ m s t _ ⟨_, hc, _array⟩ hF hs
  obtain ⟨v, es, n, hp, hentries, hn, hbodyOld⟩ := hF
  have hcol := support_right (support_left (support_left hs))
  have hp' := reads_sound hc (support_left (support_left (support_left hs))) (collection_receiver_kept hentries) hp
  exact ⟨v, es, n, hp', collectionEntries_supported hp hcol hentries,
    hb.sound hc (support_right (support_left hs)) hn,
    fun i hi hin => hbody.sound hc hp hcol (support_right hs) (hbodyOld i hi hin)⟩

end Verification.Paper.TolerantFrames
