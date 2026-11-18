import Verification.Paper.TolerantFrames.Assertions
import Verification.Semantics.Survival

/-! # The paper's path-read supports

The existing mechanism extended here is shared `pathReads_sound`. The paper
support uses raw field regions, not its internal class intersections. A
transition-local omission condition reinserts any omitted field at keep; region
restriction then permits reuse of the shared traversal proof. No heap/world
semantics or traversal is duplicated, and omissions may occur at every prefix.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge TolerantFrames
open Verification.Parity (Path)

abbrev OmittedFields := Path → String → Bool

def fieldRegion (p : Path) (f : String) : Region := .path p.root p.fields (.str f)

def fieldReads (omitted : OmittedFields) (p : Path) (f : String) (δ : Change) : Footprint :=
  if omitted p f then [] else [(fieldRegion p f, δ)]

/-- The condition is local to this pair of heaps. The frame theorem separately
requires it on every relevant action. -/
def OmissionCondition (omitted : OmittedFields) : ConditionOn IndexedHeap :=
  fun ρ _ s t => ∀ p f, omitted p f = true → Supported [(fieldRegion p f, .keep)] ρ s.h t.h

/-- Field locations along the path: grow at every intermediate field and δ
at the last. The region itself is read at the old heap, as in Definition 14. -/
def readsFrom (omitted : OmittedFields) (δ : Change) (x : Nat) : List String → List String → Footprint
  | _, [] => []
  | pre, f :: q => fieldReads omitted ⟨x, pre⟩ f (if q.isEmpty then δ else .grow) ++
      readsFrom omitted δ x (pre ++ [f]) q

def reads (omitted : OmittedFields) (δ : Change) (p : Path) : Footprint :=
  readsFrom omitted δ p.root [] p.fields

private theorem support_left {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported S ρ h h' := fun e he => hs e (List.mem_append_left _ he)

private theorem support_right {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported T ρ h h' := fun e he => hs e (List.mem_append_right _ he)

/-- Reinsertion uses equality, hence meets every change by reflexivity. -/
theorem fieldReads_complete {omitted : OmittedFields} {ρ m s t}
    (hc : OmissionCondition omitted ρ m s t) {p f δ}
    (hs : Supported (fieldReads omitted p f δ) ρ s.h t.h) :
    Supported [(fieldRegion p f, δ)] ρ s.h t.h := by
  by_cases ho : omitted p f = true
  · intro e he l v hm hv
    cases List.mem_singleton.mp he
    obtain ⟨u, hu, hh⟩ := hc p f ho _ (List.mem_singleton_self _) l v hm hv
    have huv : u = v := hh
    subst u
    exact ⟨v, hu, Change.Holds.refl δ _ v⟩
  · simpa [fieldReads, ho] using hs

private theorem default_keyRead (x : Nat) (pre : List String) (f : String) (r : Region) (δ : Change) :
    keyRead ({} : ReadContext) x pre f r δ = [(r, δ)] := by
  unfold keyRead
  split <;> rfl

/-- Raw reads, after omission reinsertion, imply the shared implementation's
class-restricted reads. Its .inCls helpers are not the paper support syntax. -/
theorem readsFrom_shared {omitted : OmittedFields} {ρ m s t}
    (hc : OmissionCondition omitted ρ m s t) {δ : Change} {sel : Selector} {x : Nat} :
    ∀ pre q, Supported (readsFrom omitted δ x pre q) ρ s.h t.h →
      Supported (pathReads ({} : ReadContext) x δ sel pre q) ρ s.h t.h := by
  intro pre q
  induction q generalizing pre with
  | nil => intro _ e he; cases he
  | cons f q ih =>
    intro hs e he l v hm hv
    have hhead := fieldReads_complete hc (support_left hs)
    have htail := ih (pre ++ [f]) (support_right hs)
    simp only [pathReads, default_keyRead, List.mem_append, List.mem_singleton] at he
    rcases he with rfl | he
    · exact hhead _ (List.mem_singleton_self _) l v (((Bool.and_eq_true _ _).mp hm).1) hv
    · exact htail e he l v hm hv

/-- Successful reading is preserved at the exact final-value tolerance.
No presence, totality or array-only premise is inferred. -/
theorem reads_sound {omitted : OmittedFields} {ρ m s t} {p : Path} {δ : Change} {v : Val}
    (hc : OmissionCondition omitted ρ m s t) (hs : Supported (reads omitted δ p) ρ s.h t.h)
    (hk : Keeps δ v) (hp : p.read ρ s.h = some v) : p.read ρ t.h = some v := by
  have hshared := readsFrom_shared (sel := .all) hc [] p.fields hs
  have hctx : ({} : ReadContext).Holds ρ s.h t.h := by
    intro _ _ _ _ _ _ _ hfalse; cases hfalse
  exact pathReads_sound hctx p.fields [] hshared hk (Selector.has_all _) rfl rfl hp

/-- The exact equality-atom row at reads_keep(p). -/
theorem equal_support (omitted : OmittedFields) (p : Path) (w : Value) :
    Supports (OmissionCondition omitted) (Formula.atom (.equal p w)).meaning (reads omitted .keep p) := by
  intro ρ m s t _ ⟨_, hc⟩ hF hs
  obtain ⟨v, hp, hw⟩ := hF
  exact ⟨v, reads_sound hc hs (keeps_keep v) hp, hw⟩

/-- The contents row uses exactly the path's raw field reads. -/
theorem contents_support (omitted : OmittedFields) (p : Path) (V : ValueSet) :
    Supports (OmissionCondition omitted) (Formula.atom (.contents p V)).meaning (reads omitted .keep p) := by
  intro ρ m s t _ ⟨_, hc⟩ hF hs
  obtain ⟨v, hp, hV⟩ := hF
  exact ⟨v, reads_sound hc hs (keeps_keep v) hp, hV⟩

/-- Separation includes defined nonarray paths, not only two array variables. -/
theorem separated_support (omitted : OmittedFields) (p q : Path) :
    Supports (OmissionCondition omitted) (Formula.separated p q).meaning
      (reads omitted .keep p ++ reads omitted .keep q) := by
  intro ρ m s t _ ⟨_, hc⟩ hF hs
  obtain ⟨u, v, hp, hq, hne⟩ := hF
  exact ⟨u, v, reads_sound hc (support_left hs) (keeps_keep u) hp,
    reads_sound hc (support_right hs) (keeps_keep v) hq, hne⟩

/-- Appending the optional final field makes every preceding field intermediate.
This is exactly the displayed reads_keep(p.f), including an absent final field. -/
theorem readsFrom_snoc (omitted : OmittedFields) (δ : Change) (x : Nat) (f : String) :
    ∀ pre q, readsFrom omitted δ x pre (q ++ [f]) =
      readsFrom omitted .grow x pre q ++ fieldReads omitted ⟨x, pre ++ q⟩ f δ := by
  intro pre q
  induction q generalizing pre with
  | nil => simp [readsFrom]
  | cons g q ih => simp [readsFrom, ih, List.append_assoc]

theorem reads_snoc (omitted : OmittedFields) (δ : Change) (p : Path) (f : String) :
    reads omitted δ ⟨p.root, p.fields ++ [f]⟩ =
      reads omitted .grow p ++ fieldReads omitted p f δ := by
  simpa only [reads, List.nil_append] using readsFrom_snoc omitted δ p.root f [] p.fields

/-- Optional equality keeps a strict receiver path; only the final field is
optional. Missing earlier prefixes are not treated as an undefined value. -/
theorem optionalRead_supported {omitted : OmittedFields} {ρ m s t} {p : Path} {f : String} {u : Val}
    (hc : OmissionCondition omitted ρ m s t)
    (hs : Supported (reads omitted .keep ⟨p.root, p.fields ++ [f]⟩) ρ s.h t.h)
    (he : optionalRead ρ s.h p f = some u) : optionalRead ρ t.h p f = some u := by
  rw [reads_snoc] at hs
  simp only [optionalRead, bind, Option.bind_eq_some_iff] at he ⊢
  obtain ⟨v, hp, he⟩ := he
  cases v <;> try cases he
  rename_i fs cd oid
  have hp' := reads_sound hc (support_left hs) (keeps_obj (by decide) rfl) hp
  refine ⟨_, hp', ?_⟩
  have hfield := fieldReads_complete hc (support_right hs)
  simp only at he ⊢
  split at he
  · exact he
  · rename_i l hl
    have hm : (fieldRegion p f).mem ρ s.h l = true := by
      simp only [Parity.Path.read] at hp
      simp [fieldRegion, Region.mem, hp, fieldsOf, hl]
    obtain ⟨w, hw, hh⟩ := hfield _ (List.mem_singleton_self _) l u hm he
    exact hh ▸ hw

/-- Exact optional-equality row; support is reads_keep(p.f), even when f is
absent. The condition handles omitted reads at arbitrary prefixes. -/
theorem optionalEqual_support (omitted : OmittedFields) (p : Path) (f : String) (w : Value) :
    Supports (OmissionCondition omitted) (Formula.atom (.optionalEqual p f w)).meaning
      (reads omitted .keep ⟨p.root, p.fields ++ [f]⟩) := by
  intro ρ m s t _ ⟨_, hc⟩ hF hs
  obtain ⟨v, hp, hw⟩ := hF
  exact ⟨v, optionalRead_supported hc hs hp, hw⟩

end Verification.Paper.TolerantFrames
