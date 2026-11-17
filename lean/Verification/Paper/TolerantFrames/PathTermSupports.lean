import Verification.Paper.TolerantFrames.PathSupports

/-! # The paper's numeric path-term supports

This extends the raw-read bridge to the shared `Term.support_sound`, preserving
partial definedness rather than supplying a list of special formulas. Numeric
and string readings tolerate init, view descriptors tolerate grow, and only
ordinary array lengths may increase when the selected spine tolerates grow.
-/
namespace Verification.Paper.TolerantFrames
open Verification Footprints HeapKnowledge TolerantFrames
open Verification.Parity (Path)

def pathSpineReads (kind : Reading) (δ : Change) (p : Path) : Footprint :=
  match kind with
  | .length => [(.spine p.root p.fields, δ)]
  | _ => []

def pathTermReads (omitted : OmittedFields) (kind : Reading) (δ : Change) (p : Path) : Footprint :=
  reads omitted (lastChange kind) p ++ pathSpineReads kind δ p

private theorem support_left {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported S ρ h h' := fun e he => hs e (List.mem_append_left _ he)
private theorem support_right {S T : Footprint} {ρ h h'} (hs : Supported (S ++ T) ρ h h') :
    Supported T ρ h h' := fun e he => hs e (List.mem_append_right _ he)

private theorem spineRead_default (x : Nat) (fs : List String) (δ : Change) :
    spineRead ({} : ReadContext) x fs δ = [(.inCls (.path x fs arraySpineKey) .arrays, δ)] := by
  unfold spineRead keyRead
  split <;> rfl

/-- An object owning the array-spine slot selects it as its element spine. -/
private theorem arrayKey_in_spine {ρ : Env} {h : Heap} {x : Nat} {fs : List String} {l : Nat}
    (hm : (Region.path x fs arraySpineKey).mem ρ h l = true) :
    (Region.spine x fs).mem ρ h l = true := by
  simp only [Region.mem] at hm ⊢
  split at hm
  · rename_i v hp
    cases v with
    | objAt fields c i =>
      have hl : fields.lookup arraySpineKey = some l := by simpa [fieldsOf] using hm
      simp [elementsOf, hl]
    | _ => simp [fieldsOf] at hm
  · cases hm

/-- The exact raw support implies the shared sufficient support; internal
class intersections remain proof helpers rather than source regions. -/
theorem pathTermReads_shared {omitted : OmittedFields} {ρ m s t} {kind : Reading} {δ : Change} {p : Path}
    (hc : OmissionCondition omitted ρ m s t)
    (hs : Supported (pathTermReads omitted kind δ p) ρ s.h t.h) :
    Supported ((HeapKnowledge.Term.now kind p.root p.fields).support ({} : ReadContext) δ) ρ s.h t.h := by
  have hhead := readsFrom_shared (sel := .values) hc [] p.fields (support_left hs)
  have htail : Supported (match kind with
      | .length => spineRead ({} : ReadContext) p.root p.fields δ
      | _ => []) ρ s.h t.h := by
    cases kind with
    | value | view | strLength => intro e he; cases he
    | length =>
      rw [spineRead_default]
      intro e he l v hm hv
      cases List.mem_singleton.mp he
      exact support_right hs _ (List.mem_singleton_self _) l v
        (arrayKey_in_spine (((Bool.and_eq_true _ _).mp hm).1)) hv
  have hform : (HeapKnowledge.Term.now kind p.root p.fields).support ({} : ReadContext) δ =
      pathReads ({} : ReadContext) p.root (lastChange kind) .values [] p.fields ++
        (match kind with | .length => spineRead ({} : ReadContext) p.root p.fields δ | _ => []) := by
    cases kind <;> rfl
  rw [hform]

  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hhead e he
  · cases kind <;> exact htail e he

/-- Array length is nondecreasing under grow and exact under keep. All other
path reading kinds are exact at either annotation. -/
theorem path_term_supported {omitted : OmittedFields} {ρ m s t} {kind : Reading} {δ : Change} {p : Path} {n : Int}
    (hc : OmissionCondition omitted ρ m s t) (hδ : δ = .keep ∨ δ = .grow)
    (hs : Supported (pathTermReads omitted kind δ p) ρ s.h t.h)
    (he : (Term.path kind p).eval ρ s.h = some n) :
    ∃ n', (Term.path kind p).eval ρ t.h = some n' ∧ n ≤ n' ∧
      (δ = .keep ∨ kind ≠ .length → n' = n) := by
  have hctx : ({} : ReadContext).Holds ρ s.h t.h := by
    intro _ _ _ _ _ _ _ hfalse; cases hfalse
  have hshared := pathTermReads_shared hc hs
  have hterm : termValue ⟨ρ, s.h⟩ ρ s.h (HeapKnowledge.Term.now kind p.root p.fields) = some n := he
  by_cases hk : kind = .length
  · obtain ⟨n', hn', hle, heq⟩ := Verification.Footprints.Term.support_sound hctx hδ hshared hterm
    refine ⟨n', hn', hle, fun h => ?_⟩
    rcases h with hδ | hne
    · exact heq hδ
    · exact (hne hk).elim
  · have hsame : pathTermReads omitted kind .keep p = pathTermReads omitted kind δ p := by
      cases kind <;> try rfl
      exact (hk rfl).elim
    have hskeep : Supported (pathTermReads omitted kind .keep p) ρ s.h t.h := hsame ▸ hs
    obtain ⟨n', hn', hle, heq⟩ := Verification.Footprints.Term.support_sound hctx (.inl rfl)
      (pathTermReads_shared hc hskeep) hterm
    exact ⟨n', hn', hle, fun _ => heq rfl⟩

/-- Exact path-term reading at the keep annotation. -/
theorem path_term_keep (omitted : OmittedFields) (kind : Reading) (p : Path) (n : Int) :
    Supports (OmissionCondition omitted) (fun ρ _ s => (Term.path kind p).eval ρ s.h = some n)
      (pathTermReads omitted kind .keep p) := by
  intro ρ m s t _ ⟨_, hc⟩ he hs
  obtain ⟨n', hn', _, heq⟩ := path_term_supported hc (.inl rfl) hs he
  simpa only [heq (.inl rfl)] using hn'

end Verification.Paper.TolerantFrames
