import Verification.Semantics.FootprintRebase
import Verification.Semantics.Support
import Verification.Semantics.SurvivalSeparation

/-! A support kept across one step of a run. The support `T` and every
rebased region are read at the run's entry heap `h₀`. A step whose rebased
writes respect `T` under a query sound at `h₀` keeps `T`, read at `h₀`, from
the step's prestate to its poststate, whatever ran before it. -/
namespace Verification.Footprints

/-- A location of a region read at the step's positions and heap is in one
of its rebased regions read at the entry heap, when the location existed at
entry and its contents kept their class since. -/
theorem rebase_mem_kept {ρ₀ σ : Env} {h₀ h : Heap} {ev : RebaseEvidence} {l : Nat}
    (hk : RebaseOk ev σ ρ₀ h₀ h) (hl : l < h₀.length) (hlen : h₀.length ≤ h.length)
    (same : ∀ (c : Selector) u u', h₀[l]? = some u → h[l]? = some u' → c.selects u' = c.selects u) :
    ∀ {r : Region}, r.mem σ h l = true → ∃ s ∈ rebase ev r, s.mem ρ₀ h₀ l = true := by
  have hlh : l < h.length := Nat.lt_of_lt_of_le hl hlen
  obtain ⟨u, hu⟩ : ∃ u, h[l]? = some u := ⟨h[l], List.getElem?_eq_getElem hlh⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u, h₀[l]? = some u := ⟨h₀[l], List.getElem?_eq_getElem hl⟩
  have clsBack : ∀ {c : Selector}, c.selects u = true → (Region.cls c).mem ρ₀ h₀ l = true := by
    intro c hc
    simp only [Region.mem, hu₀]
    rw [← same c u₀ u hu₀ hu]; exact hc
  intro r
  induction r with
  | field s k =>
    intro hm
    by_cases hf : ev.freshPath s [] k = true
    · have := hk.fresh_path hf (by simpa using hm)
      omega
    simp only [Bool.not_eq_true] at hf
    cases he : ev.path s [] with
    | none => exact ⟨.all, by simp [rebase, he, hf], by simpa [Region.mem] using hl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine ⟨.path x q k, by simp [rebase, he, hf], ?_⟩
      simp only [Region.mem, hk.path he (show HeapKnowledge.readPath h (σ s) [] = some (σ s) from rfl)]
      simpa [Region.mem] using hm
  | fields s =>
    intro hm
    cases he : ev.path s [] with
    | none => exact ⟨.all, by simp [rebase, he], by simpa [Region.mem] using hl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine ⟨.pathFields x q, by simp [rebase, he], ?_⟩
      simp only [Region.mem, hk.path he (show HeapKnowledge.readPath h (σ s) [] = some (σ s) from rfl)]
      simpa [Region.mem] using hm
  | path s p k =>
    intro hm
    have hf : ev.freshPath s p k = false := by
      cases hfs : ev.freshPath s p k
      · rfl
      · have := hk.fresh_path hfs hm
        omega
    cases he : ev.path s p with
    | none =>
      by_cases hp0 : p.isEmpty = true
      · exact ⟨.all, by simp [rebase, he, hf, hp0], by simpa [Region.mem] using hl⟩
      · have hne : p ≠ [] := by simpa using hp0
        simp only [Region.mem] at hm
        split at hm
        · rename_i v hv
          obtain ⟨l₀, hl₀⟩ := readPath_contents hne hv
          have hsel := hk.categories.fields l₀ v k l u hl₀ (by simpa using hm) hu
          refine ⟨.cls (keyClass k), ?_, clsBack hsel⟩
          simp [rebase, he, hf, show p.isEmpty = false from by simpa using hp0]
        · cases hm
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine ⟨.path x q k, by simp [rebase, he, hf], ?_⟩
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv; rw [hk.path he hv]; exact hm
      · cases hm
  | pathFields s p =>
    intro hm
    cases he : ev.path s p with
    | none => exact ⟨.all, by simp [rebase, he], by simpa [Region.mem] using hl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine ⟨.pathFields x q, by simp [rebase, he], ?_⟩
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv; rw [hk.path he hv]; exact hm
      · cases hm
  | cls c =>
    intro hm
    exact ⟨.cls c, by simp [rebase], clsBack (by simpa [Region.mem, hu] using hm)⟩
  | inCls r c ih =>
    intro hm
    simp only [Region.mem, Bool.and_eq_true] at hm
    have hc : c.selects u = true := by simpa [hu] using hm.2
    obtain ⟨s, hs, hsm⟩ := ih hm.1
    refine ⟨s.inCls c, by simp only [rebase]; exact List.mem_map.mpr ⟨s, hs, rfl⟩, ?_⟩
    have hc₀ := clsBack hc
    simp only [Region.mem, Bool.and_eq_true] at hc₀ ⊢
    exact ⟨hsm, by simpa [hu₀] using hc₀⟩
  | cells s =>
    intro hm
    have harr := hk.categories.elems (by simpa [Region.mem] using hm) hu
    exact ⟨.cls .values, by simp [rebase], clsBack (by rw [Selector.selects_values, harr]; rfl)⟩
  | pathCells s p =>
    intro hm
    simp only [Region.mem] at hm
    split at hm
    · have harr := hk.categories.elems (by simpa using hm) hu
      exact ⟨.cls .values, by simp [rebase], clsBack (by rw [Selector.selects_values, harr]; rfl)⟩
    · cases hm
  | all => intro _; exact ⟨.all, by simp [rebase], by simpa [Region.mem] using hl⟩
  | spine s p =>
    intro hm
    cases he : ev.path s p with
    | none => exact ⟨.all, by simp [rebase, he], by simpa [Region.mem] using hl⟩
    | some xq =>
      obtain ⟨x, q⟩ := xq
      refine ⟨.spine x q, by simp [rebase, he], ?_⟩
      simp only [Region.mem] at hm ⊢
      split at hm
      · rename_i v hv; rw [hk.path he hv]; exact hm
      · cases hm

/-- **A respected step keeps the support read at entry.** The step's frame,
at its own positions and heap, rebased to the entry positions and renamed to
a caller's slots by `τ`, respects `T` under a query sound at the entry heap
in the caller's environment `ρ`. Then a support kept from entry to the
step's prestate is kept from entry to its poststate. -/
theorem step_keeps {q : SepQuery} {T Ψ : Footprint} {ρ₀ σ ρ : Env} {τ : Nat → Option Nat}
    {h₀ h h' : Heap} {ev : RebaseEvidence}
    (hτ : ∀ i j, τ i = some j → ρ j = ρ₀ i)
    (resp : respects q T ((rebaseAll ev (Ψ.filter (·.2 != .keep))).renameM τ) = true) (hq : q.Sound ρ h₀)
    (hk : RebaseOk ev σ ρ₀ h₀ h) (hlen : h₀.length ≤ h.length) (stepPost : Post Ψ σ h h')
    (kept : Supported T ρ h₀ h) : Supported T ρ h₀ h' := by
  intro e he l v hm hv
  have hl := (List.getElem?_eq_some_iff.mp hv).1
  obtain ⟨v₁, hv₁, hch₁⟩ := kept e he l v hm hv
  obtain ⟨v₂, hv₂, allowed⟩ := stepPost.2 l v₁ hv₁
  refine ⟨v₂, hv₂, ?_⟩
  by_cases hany : e.2 = .any
  · rw [hany]; trivial
  rcases allowed with rfl | ⟨f, hf, hfm, hh⟩
  · exact hch₁
  by_cases hkeep : f.2 = .keep
  · rw [hkeep] at hh
    change v₂ = v₁ at hh
    subst hh; exact hch₁
  have same : ∀ (c : Selector) u u', h₀[l]? = some u → h[l]? = some u' → c.selects u' = c.selects u := by
    intro c u u' hu hu'
    rw [hv] at hu; rw [hv₁] at hu'; cases hu; cases hu'
    exact hch₁.same_class hany c
  obtain ⟨s, hs, hsm⟩ := rebase_mem_kept hk hl hlen same hfm
  have hfw : (s.renameM τ, f.2) ∈ (rebaseAll ev (Ψ.filter (·.2 != .keep))).renameM τ :=
    List.mem_map.mpr ⟨(s, f.2), List.mem_flatMap.mpr ⟨f, List.mem_filter.mpr ⟨hf, by simpa using hkeep⟩,
      List.mem_map.mpr ⟨s, hs, rfl⟩⟩, rfl⟩
  have pair := List.all_eq_true.mp (List.all_eq_true.mp resp e he) _ hfw
  simp only [Bool.or_eq_true] at pair
  rcases pair with hle | hdis
  · exact hch₁.trans hlen (hh.mono hle)
  · exact (hq e.1 _ l hl hdis hm (Region.mem_renameM hτ hl s hsm)).elim

/-- **A support kept since entry stays kept** across a step whose writes
are `writes`, read at the entry positions `ρ₀`: in every caller environment
`ρ` agreeing with them through `τ`, a support `T` the renamed writes respect
under a query sound at the entry heap. -/
def KeepsAt (writes : Footprint) (ρ₀ : Env) (h₀ h h' : Heap) : Prop :=
  ∀ (q : SepQuery) (T : Footprint) (τ : Nat → Option Nat) (ρ : Env), (∀ i j, τ i = some j → ρ j = ρ₀ i) →
    respects q T (writes.renameM τ) = true → q.Sound ρ h₀ →
    h₀.length ≤ h.length → Supported T ρ h₀ h → Supported T ρ h₀ h'

theorem KeepsAt.of_rebase {Ψ : Footprint} {ρ₀ σ : Env} {h₀ h h' : Heap} {ev : RebaseEvidence}
    (hk : RebaseOk ev σ ρ₀ h₀ h) (stepPost : Post Ψ σ h h') :
    KeepsAt (rebaseAll ev (Ψ.filter (·.2 != .keep))) ρ₀ h₀ h h' :=
  fun _ _ _ _ hτ resp hq hlen kept => step_keeps hτ resp hq hk hlen stepPost kept

/-- A step leaving the heap unchanged keeps every support. -/
theorem KeepsAt.same (W : Footprint) (ρ₀ : Env) (h₀ h : Heap) : KeepsAt W ρ₀ h₀ h h :=
  fun _ _ _ _ _ _ _ _ kept => kept

/-- A respected footprint admits fewer writes. -/
theorem respects_sub {q : SepQuery} {T a b : Footprint} (hsub : ∀ e ∈ a, e ∈ b)
    (hb : respects q T b = true) : respects q T a = true := by
  simp only [respects, List.all_eq_true] at hb ⊢
  exact fun e he f hf => hb e he f (hsub f hf)

theorem KeepsAt.mono {a b : Footprint} {ρ₀ : Env} {h₀ h h' : Heap} (hsub : ∀ e ∈ a, e ∈ b)
    (ha : KeepsAt a ρ₀ h₀ h h') : KeepsAt b ρ₀ h₀ h h' := by
  intro q T τ ρ hτ resp hq hlen kept
  refine ha q T τ ρ hτ (respects_sub ?_ resp) hq hlen kept
  intro e he
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  exact List.mem_map.mpr ⟨f, hsub f hf, rfl⟩

/-- An unrestricted step at closed classes keeps what its classes respect. -/
theorem KeepsAt.closed {c : Closed} {ρ₀ : Env} {h₀ h h' : Heap} (hcat : HeapCategories h)
    (stepPost : Post c.fp ρ₀ h h') : KeepsAt c.fp ρ₀ h₀ h h' := by
  have hk : RebaseOk { link := fun _ => none, agree := fun _ _ => false } ρ₀ ρ₀ h₀ h :=
    ⟨by intros; contradiction, by intros; contradiction, by intros; contradiction, hcat⟩
  refine (KeepsAt.of_rebase hk stepPost).mono ?_
  intro e he
  simp only [rebaseAll, List.mem_flatMap, List.mem_filter, List.mem_map] at he
  obtain ⟨f, ⟨hf, -⟩, s, hs, rfl⟩ := he
  simp only [Closed.fp, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> simp only [rebase, List.mem_singleton] at hs <;> subst hs <;>
    simp [Closed.fp]

end Verification.Footprints
