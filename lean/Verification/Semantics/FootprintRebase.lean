import Verification.Semantics.ClosedFootprints

/-! # Rebasing a step's frame to the invocation's entry

A step's frame is read at the step's own positions `σ`, in the heap the step
starts in. The enclosing invocation's frame is read at its entry values
`ρ₀`, in its entry heap `h₀`. **Rebasing** maps each region of the step to
regions of the entry by checked evidence: a position's value is the value an
entry path reads (`link`), and a path read from it at the step's heap reads
the same value at the entry heap (`agree`). A class region and a cell are
read in themselves, as `transport` reads them. A position's store whose
location, where the position has one, is at or above the entry heap's
length (`fresh`, `FreshIfStore`) is no entry location and rebases to none.
Any other region, or a region without evidence, becomes `all`. `Post.compose_at` composes an entry
frame so far with the step's frame through it: the one composition of a
body's steps (FOOTPRINTS.md, "Argument-path store regions"). -/
namespace Verification.Footprints

/-- Resolving a concatenated path is resolving its suffix from the prefix's value. -/
theorem readPath_append (h : Heap) (x : Val) (p q : List String) :
    HeapKnowledge.readPath h x (p ++ q) =
      (HeapKnowledge.readPath h x p).bind (fun v => HeapKnowledge.readPath h v q) := by
  induction p generalizing x with
  | nil => rfl
  | cons f p ih =>
    cases x <;> simp only [List.cons_append, HeapKnowledge.readPath, Option.bind_none]
    rename_i fs code oid
    split
    · split
      · exact ih _
      · rfl
    · rfl

/-- The evidence of a rebasing: for a step position, the entry position and
path whose read at the entry heap is its value; and the step position's
paths whose read at the step's heap is its read at the entry heap. -/
structure RebaseEvidence where
  link : Nat → Option (Nat × List String)
  agree : Nat → List String → Bool
  fresh : Nat → Bool := fun _ => false

/-- **Selected-location freshness of a store**: where the value has an array
store, its location is at least `b`. It reads no heap; a value with no store
(`null`, a number, an object of no store field) meets it. -/
def FreshIfStore (b : Nat) (v : Tm) : Prop := ∀ s, storeOf v = some s → b ≤ s

theorem FreshAt.ifStore {b : Nat} {v : Tm} (h : FreshAt b v) : FreshIfStore b v := by
  obtain ⟨s, hs, hle⟩ := h
  intro s' hs'
  rw [hs] at hs'
  cases hs'
  exact hle

theorem FreshIfStore.lower {b b' : Nat} {v : Tm} (hb : b ≤ b') (h : FreshIfStore b' v) : FreshIfStore b v :=
  fun s hs => Nat.le_trans hb (h s hs)

/-- The evidence holds of the step's positions `σ` at heap `h`, against the
entry values `ρ₀` at the entry heap `h₀`. -/
structure RebaseOk (ev : RebaseEvidence) (σ ρ₀ : Env) (h₀ h : Heap) : Prop where
  link : ∀ s x q, ev.link s = some (x, q) → HeapKnowledge.readPath h₀ (ρ₀ x) q = some (σ s)
  agree : ∀ s p, ev.agree s p = true → ∀ v, HeapKnowledge.readPath h (σ s) p = some v →
    HeapKnowledge.readPath h₀ (σ s) p = some v
  fresh : ∀ s, ev.fresh s = true → FreshIfStore h₀.length (σ s)

/-- A region that selects the store of a position whose store is fresh. -/
def RebaseEvidence.freshStore (ev : RebaseEvidence) (s : Nat) (k : PropKey) : Bool :=
  k == arrayStoreKey && ev.fresh s

/-- A fresh store region selects no location of the entry heap. -/
theorem RebaseOk.fresh_store {ev σ ρ₀ h₀ h} (hk : RebaseOk ev σ ρ₀ h₀ h) {s k l}
    (hf : ev.freshStore s k = true) (hm : (fieldsOf (σ s)).lookup k = some l) : h₀.length ≤ l := by
  simp only [RebaseEvidence.freshStore, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨rfl, hf⟩ := hf
  exact hk.fresh s hf l hm

/-- Whether a step position's path is read at the entry heap as at the
step's: the empty path always. -/
def RebaseEvidence.reads (ev : RebaseEvidence) (s : Nat) (p : List String) : Bool :=
  p.isEmpty || ev.agree s p

/-- A path read from a linked position, where it agrees, as a path from the
entry position. -/
def RebaseEvidence.path (ev : RebaseEvidence) (s : Nat) (p : List String) : Option (Nat × List String) :=
  if ev.reads s p then (ev.link s).map fun (x, q) => (x, q ++ p) else none

/-- **Rebasing** a region read at the step's positions and heap into regions
read at the entry's. -/
def rebase (ev : RebaseEvidence) : Region → List Region
  | .field s k => if ev.freshStore s k then [] else match ev.path s [] with
    | some (x, q) => [.path x q k]
    | none => [.all]
  | .own s => match ev.path s [] with
    | some (x, q) => [.pathOwn x q]
    | none => [.all]
  | .path s p k => if p.isEmpty && ev.freshStore s k then [] else match ev.path s p with
    | some (x, q) => [.path x q k]
    | none => [.all]
  | .pathOwn s p => match ev.path s p with
    | some (x, q) => [.pathOwn x q]
    | none => [.all]
  | .cls c => [.cls c]
  | .cell b => [.cell b]
  | .inCls r c => (rebase ev r).map (·.inCls c)
  | _ => [.all]

def rebaseAll (ev : RebaseEvidence) (Ψ : Footprint) : Footprint :=
  Ψ.flatMap fun e => (rebase ev e.1).map (·, e.2)

/-- A path the evidence rebases reads, at the entry heap from the entry
position, the value it reads at the step's heap from the step position. -/
theorem RebaseOk.path {ev σ ρ₀ h₀ h} (hk : RebaseOk ev σ ρ₀ h₀ h) {s p x q v}
    (he : ev.path s p = some (x, q)) (hv : HeapKnowledge.readPath h (σ s) p = some v) :
    HeapKnowledge.readPath h₀ (ρ₀ x) q = some v := by
  unfold RebaseEvidence.path at he
  split at he
  · rename_i hr
    cases hl : ev.link s with
    | none => rw [hl] at he; cases he
    | some xq =>
      obtain ⟨x', q'⟩ := xq
      rw [hl] at he
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have h₀v : HeapKnowledge.readPath h₀ (σ s) p = some v := by
        simp only [RebaseEvidence.reads, Bool.or_eq_true, List.isEmpty_iff] at hr
        rcases hr with rfl | hr
        · simpa [HeapKnowledge.readPath] using hv
        · exact hk.agree s p hr v hv
      rw [readPath_append, hk.link s x' q' hl]
      simpa using h₀v
  · cases he

theorem rebase_sound {Φp ρ₀ σ h₀ h ev l} (hp : Post Φp ρ₀ h₀ h) (hk : RebaseOk ev σ ρ₀ h₀ h)
    (hl : l < h₀.length) :
    ∀ {r : Region}, r.mem σ h l = true →
    (∃ s ∈ rebase ev r, s.mem ρ₀ h₀ l = true) ∨ ∃ e ∈ Φp, e.1.mem ρ₀ h₀ l = true ∧ e.2 = .any := by
  intro r
  induction r with
  | field s k =>
    intro hm
    by_cases hf : ev.freshStore s k = true
    · have := hk.fresh_store hf (by simpa [Region.mem] using hm)
      omega
    simp only [Bool.not_eq_true] at hf
    cases he : ev.path s [] with
    | none => exact .inl ⟨.all, by simp [rebase, he, hf], rfl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine .inl ⟨.path x q k, by simp [rebase, he, hf], ?_⟩
      simp only [Region.mem, hk.path he (show HeapKnowledge.readPath h (σ s) [] = some (σ s) from rfl)]
      simpa [Region.mem] using hm
  | own s =>
    intro hm
    cases he : ev.path s [] with
    | none => exact .inl ⟨.all, by simp [rebase, he], rfl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine .inl ⟨.pathOwn x q, by simp [rebase, he], ?_⟩
      simp only [Region.mem, hk.path he (show HeapKnowledge.readPath h (σ s) [] = some (σ s) from rfl)]
      simpa [Region.mem] using hm
  | path s p k =>
    intro hm
    have hf : (p.isEmpty && ev.freshStore s k) = false := by
      cases hp : p.isEmpty
      · rfl
      · cases p with
        | cons _ _ => cases hp
        | nil =>
          cases hfs : ev.freshStore s k
          · rfl
          · have := hk.fresh_store hfs (by simpa [Region.mem, HeapKnowledge.readPath] using hm)
            omega
    cases he : ev.path s p with
    | none => exact .inl ⟨.all, by simp [rebase, he, hf], rfl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine .inl ⟨.path x q k, by simp [rebase, he, hf], ?_⟩
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv; rw [hk.path he hv]; exact hm
      · cases hm
  | pathOwn s p =>
    intro hm
    cases he : ev.path s p with
    | none => exact .inl ⟨.all, by simp [rebase, he], rfl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine .inl ⟨.pathOwn x q, by simp [rebase, he], ?_⟩
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv; rw [hk.path he hv]; exact hm
      · cases hm
  | cls c =>
    intro hm
    rcases cls_back (ρ := ρ₀) hp hl (by simpa [Region.mem] using hm) with h | h
    · exact .inl ⟨.cls c, by simp [rebase], h⟩
    · exact .inr h
  | cell b =>
    intro hm
    have hv : (Region.cls .value).mem ρ₀ h l = true := by simpa [Region.mem] using hm
    rcases cls_back hp hl hv with h | h
    · exact .inl ⟨.cell b, by simp [rebase], by simpa [Region.mem] using h⟩
    · exact .inr h
  | inCls r c ih =>
    intro hm
    simp only [Region.mem, Bool.and_eq_true] at hm
    have hc : (Region.cls c).mem ρ₀ h l = true := by simpa [Region.mem] using hm.2
    rcases ih hm.1 with ⟨s, hs, hsm⟩ | h
    · rcases cls_back hp hl hc with hc₀ | h
      · refine .inl ⟨s.inCls c, by simp only [rebase]; exact List.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
        simp only [Region.mem, Bool.and_eq_true]
        exact ⟨hsm, by simpa [Region.mem] using hc₀⟩
      · exact .inr h
    · exact .inr h
  | elems | all | pathElems =>
    intro _; exact .inl ⟨.all, by simp [rebase], rfl⟩

/-- **Composition at the step's positions.** An entry frame so far, a step's
frame at its own positions and heap, the rebasing evidence, and an inclusion
justified by class evidence valid at the entry heap give the next entry
frame. With `σ = ρ₀` and the identity link it is `Post.compose` at a step
reading no path. -/
theorem Post.compose_at {Φp Ψ Φq : Footprint} {cl ρ₀ σ h₀ h h' ev}
    (hp : Post Φp ρ₀ h₀ h) (hn : Post Ψ σ h h') (hk : RebaseOk ev σ ρ₀ h₀ h)
    (hle : Footprint.le cl (Φp ++ rebaseAll ev Ψ) Φq = true) (hc : ClassOk cl ρ₀ h₀) :
    Post Φq ρ₀ h₀ h' := by
  refine ⟨Nat.le_trans hp.1 hn.1, fun l v₀ hv₀ => ?_⟩
  have hl := (List.getElem?_eq_some_iff.mp hv₀).1
  have hb : h₀.length ≤ h.length := hp.1
  obtain ⟨v₁, hv₁, ha₁⟩ := hp.2 l v₀ hv₀
  obtain ⟨v₂, hv₂, ha₂⟩ := hn.2 l v₁ hv₁
  refine ⟨v₂, hv₂, Allowed.mono hle hc hl ?_⟩
  have viaAny : ∀ e ∈ Φp, e.1.mem ρ₀ h₀ l = true → e.2 = .any →
      Allowed (Φp ++ rebaseAll ev Ψ) ρ₀ h₀ l v₀ v₂ := fun e hm hem hany =>
    .inr ⟨e, List.mem_append_left _ hm, hem, by rw [hany]; trivial⟩
  have stepEntry : ∀ e ∈ Ψ, e.1.mem σ h l = true →
      (∃ s, (s, e.2) ∈ rebaseAll ev Ψ ∧ s.mem ρ₀ h₀ l = true) ∨
        ∃ e' ∈ Φp, e'.1.mem ρ₀ h₀ l = true ∧ e'.2 = .any := by
    intro e hem hm
    rcases rebase_sound hp hk hl hm with ⟨s, hs, hsm⟩ | h
    · exact .inl ⟨s, List.mem_flatMap.mpr ⟨e, hem, List.mem_map.mpr ⟨s, hs, rfl⟩⟩, hsm⟩
    · exact .inr h
  rcases ha₁ with rfl | ⟨e₁, he₁, hm₁, hh₁⟩
  · rcases ha₂ with rfl | ⟨e₂, he₂, hm₂, hh₂⟩
    · exact .inl rfl
    · rcases stepEntry e₂ he₂ hm₂ with ⟨s, hs, hsm⟩ | ⟨e', he', hm', hany⟩
      · exact .inr ⟨(s, e₂.2), List.mem_append_right _ hs, hsm, hh₂.lower hb⟩
      · exact viaAny e' he' hm' hany
  · rcases ha₂ with rfl | ⟨e₂, he₂, hm₂, hh₂⟩
    · exact .inr ⟨e₁, List.mem_append_left _ he₁, hm₁, hh₁⟩
    · rcases stepEntry e₂ he₂ hm₂ with ⟨s, hs, hsm⟩ | ⟨e', he', hm', hany⟩
      · have hseq := hh₁.seq hb hh₂
        rcases Change.max_cases e₁.2 e₂.2 with hmax | hmax
        · exact .inr ⟨e₁, List.mem_append_left _ he₁, hm₁, by rw [← hmax]; exact hseq⟩
        · exact .inr ⟨(s, e₂.2), List.mem_append_right _ hs, hsm, by rw [← hmax]; exact hseq⟩
      · exact viaAny e' he' hm' hany

end Verification.Footprints
