import Verification.Semantics.ExitPosts
import Verification.Semantics.FootprintRebase

/-! # Composing exits across entries

The semantic foundation of composition (the note *Tolerant frames*, §6,
Seq-Eff, Fresh-Eff, Entry and the definition "Rebasing"), stated over the
effect action and the assertion semantics alone, so that callable and body
typing compose with it: consequence between lists of two-state formulas
(`Consequence`), inclusion of frames (`Footprint.le`), rebasing with
absorption (`Rebases`) and the general Seq-Eff (`Post.compose_rebases`).

An exit of a schema reached from a later entry is an exit from an earlier
entry (`Exits.compose_entry`) when an action of a frame leads from the
earlier entry to the later, the later exit's frame is rebased to the
earlier entry, and the postconditions follow by consequence. An allocation
between the two entries keeps every old location (`Post.of_prefix`), and a
frame whose entries select no new old location across it rebases to itself
(`Rebases.of_prefix`). -/
namespace Verification.CallEffects
open Verification Footprints HeapKnowledge TolerantFrames Parity

/-! ## Checked consequence -/

/-- **Consequence**: at every two-state where the premises hold, the goals
hold. -/
def Consequence (arena : AssertionArena) (Γ goals : List Formula) : Prop :=
  ∀ s, (∀ F ∈ Γ, Parity.Holds arena s F) → ∀ G ∈ goals, Parity.Holds arena s G

theorem Consequence.nil (arena : AssertionArena) (Γ : List Formula) : Consequence arena Γ [] :=
  fun _ _ _ hG => by cases hG

/-- Each premise is a consequence. -/
theorem Consequence.refl (arena : AssertionArena) (Γ : List Formula) : Consequence arena Γ Γ :=
  fun _ hΓ G hG => hΓ G hG

/-- More premises keep a consequence. -/
theorem Consequence.mono {arena : AssertionArena} {Γ Γ' goals : List Formula} (hsub : ∀ F ∈ Γ, F ∈ Γ')
    (h : Consequence arena Γ goals) : Consequence arena Γ' goals :=
  fun s hΓ => h s fun F hF => hΓ F (hsub F hF)

/-- Consequences of consequences. -/
theorem Consequence.trans {arena : AssertionArena} {Γ Δ goals : List Formula} (h₁ : Consequence arena Γ Δ)
    (h₂ : Consequence arena Δ goals) : Consequence arena Γ goals :=
  fun s hΓ => h₂ s (h₁ s hΓ)

/-! ## Footprint inclusion -/

theorem _root_.Verification.Footprints.Change.le_refl (c : Change) : c.le c = true := by
  cases c <;> rfl

theorem _root_.Verification.Footprints.Region.sub_refl (cl : ClassEvidence) (r : Region) : Region.sub cl r r = true := by
  cases r <;> simp [Region.sub, Region.subBase]

theorem _root_.Verification.Footprints.Footprint.le_of_subset {cl : ClassEvidence} {Φ Ψ : Footprint} (h : ∀ e ∈ Φ, e ∈ Ψ) :
    Footprint.le cl Φ Ψ = true :=
  List.all_eq_true.mpr fun e he => List.any_eq_true.mpr
    ⟨e, h e he, by simp [Change.le_refl, Region.sub_refl]⟩

theorem _root_.Verification.Footprints.Footprint.le_refl (cl : ClassEvidence) (Φ : Footprint) : Footprint.le cl Φ Φ = true :=
  Footprint.le_of_subset fun _ h => h

theorem _root_.Verification.Footprints.Footprint.le_append_left (cl : ClassEvidence) (Φ Ψ : Footprint) : Footprint.le cl Φ (Φ ++ Ψ) = true :=
  Footprint.le_of_subset fun _ h => List.mem_append_left _ h

theorem _root_.Verification.Footprints.Footprint.le_append_right (cl : ClassEvidence) (Φ Ψ : Footprint) : Footprint.le cl Ψ (Φ ++ Ψ) = true :=
  Footprint.le_of_subset fun _ h => List.mem_append_right _ h

/-! ## Rebasing, with absorption -/

/-- **Rebasing** (the note, §6, the definition "Rebasing", with the
absorption of the design's correction 3): every location of the entry heap
`h₀` in a region of an entry of `Ψ`, read at the valuation `σ` and heap `h`
where the later command starts, is in a region of an entry of `Ψ'`, read at
the entry, at the same or a wider change, or in a region of an entry of the
frame so far `Φp` at `any`. -/
def Rebases (Φp Ψ' : Footprint) (ρ₀ : Env) (h₀ : Heap) (Ψ : Footprint) (σ : Env) (h : Heap) : Prop :=
  ∀ l, l < h₀.length → ∀ e ∈ Ψ, e.1.mem σ h l = true →
    (∃ e' ∈ Ψ', e'.1.mem ρ₀ h₀ l = true ∧ e.2.le e'.2 = true) ∨
      ∃ e' ∈ Φp, e'.1.mem ρ₀ h₀ l = true ∧ e'.2 = .any

/-- **Rebasing gives the note's direct coverage** (the note, §6, the
definition "Rebasing"): every location of the entry heap that `Ψ` covers at
a change is covered by `Φp ∪ Ψ'`, read at the entry, at the same or a wider
change. An absorbing entry of `Φp` is at `any`, the widest change. -/
theorem Rebases.covers {Φp Ψ' Ψ : Footprint} {ρ₀ σ : Env} {h₀ h : Heap}
    (hr : Rebases Φp Ψ' ρ₀ h₀ Ψ σ h) :
    ∀ l, l < h₀.length → ∀ e ∈ Ψ, e.1.mem σ h l = true →
      ∃ e' ∈ Φp ++ Ψ', e'.1.mem ρ₀ h₀ l = true ∧ e.2.le e'.2 = true := by
  intro l hl e he hm
  rcases hr l hl e he hm with ⟨e', he', hm', hle⟩ | ⟨e', he', hm', hany⟩
  · exact ⟨e', List.mem_append_right _ he', hm', hle⟩
  · exact ⟨e', List.mem_append_left _ he', hm', by rw [hany]; cases e.2 <;> rfl⟩

/-- **The computed rebasing rebases** (`rebase_sound`): under its evidence,
after an action of the frame so far. -/
theorem rebases_of_rebaseOk {Φp Ψ : Footprint} {ρ₀ σ : Env} {h₀ h : Heap} {ev : RebaseEvidence}
    (hp : Post Φp ρ₀ h₀ h) (hk : RebaseOk ev σ ρ₀ h₀ h) : Rebases Φp (rebaseAll ev Ψ) ρ₀ h₀ Ψ σ h := by
  intro l hl e he hm
  rcases rebase_sound hp hk hl hm with ⟨r, hr, hrm⟩ | h
  · exact .inl ⟨(r, e.2), List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨r, hr, rfl⟩⟩, hrm, Change.le_refl _⟩
  · exact .inr h

/-- **Seq-Eff, the general rule**: the frame so far `Φp` from the entry, a
later frame `Ψ` from where it starts, a rebasing `Ψ'` of `Ψ` to the entry,
and `Φp ∪ Ψ' ⊑_cl Φq` with `cl` valid at the entry heap give `Φq` from the
entry. The rebasing gives the note's direct coverage of `Ψ` by `Φp ∪ Ψ'`
(`Rebases.covers`), so the rule is the note's Seq-Eff over its printed
definition "Rebasing". -/
theorem Post.compose_rebases {Φp Ψ Ψ' Φq : Footprint} {cl : ClassEvidence} {ρ₀ σ : Env} {h₀ h h' : Heap}
    (hp : Post Φp ρ₀ h₀ h) (hn : Post Ψ σ h h') (hr : Rebases Φp Ψ' ρ₀ h₀ Ψ σ h)
    (hle : Footprint.le cl (Φp ++ Ψ') Φq = true) (hc : ClassOk cl ρ₀ h₀) : Post Φq ρ₀ h₀ h' := by
  refine ⟨Nat.le_trans hp.1 hn.1, fun l v₀ hv₀ => ?_⟩
  have hl := (List.getElem?_eq_some_iff.mp hv₀).1
  have hb : h₀.length ≤ h.length := hp.1
  obtain ⟨v₁, hv₁, ha₁⟩ := hp.2 l v₀ hv₀
  obtain ⟨v₂, hv₂, ha₂⟩ := hn.2 l v₁ hv₁
  refine ⟨v₂, hv₂, Allowed.mono hle hc hl ?_⟩
  have viaAny : ∀ e ∈ Φp, e.1.mem ρ₀ h₀ l = true → e.2 = .any → Allowed (Φp ++ Ψ') ρ₀ h₀ l v₀ v₂ :=
    fun e hm hem hany => .inr ⟨e, List.mem_append_left _ hm, hem, by rw [hany]; trivial⟩
  rcases ha₁ with rfl | ⟨e₁, he₁, hm₁, hh₁⟩
  · rcases ha₂ with rfl | ⟨e₂, he₂, hm₂, hh₂⟩
    · exact .inl rfl
    · rcases hr l hl e₂ he₂ hm₂ with ⟨e', he', hm', hle'⟩ | ⟨e', he', hm', hany⟩
      · exact .inr ⟨e', List.mem_append_right _ he', hm', (hh₂.mono hle').lower hb⟩
      · exact viaAny e' he' hm' hany
  · rcases ha₂ with rfl | ⟨e₂, he₂, hm₂, hh₂⟩
    · exact .inr ⟨e₁, List.mem_append_left _ he₁, hm₁, hh₁⟩
    · rcases hr l hl e₂ he₂ hm₂ with ⟨e', he', hm', hle'⟩ | ⟨e', he', hm', hany⟩
      · have hseq := hh₁.seq hb (hh₂.mono hle')
        rcases Change.max_cases e₁.2 e'.2 with hmax | hmax
        · exact .inr ⟨e₁, List.mem_append_left _ he₁, hm₁, by rw [← hmax]; exact hseq⟩
        · exact .inr ⟨e', List.mem_append_right _ he', hm', by rw [← hmax]; exact hseq⟩
      · exact viaAny e' he' hm' hany

/-- **Seq-Eff as the note displays it** (`c₁ : Φ`, `c₂ : Ψ`, `Ψ ⇝ Ψ'`,
`Φ ∪ Ψ' ⊑ Φ` give `c₁; c₂ : Φ`), the instance of `Post.compose_rebases`
whose bound is the first frame. -/
theorem Post.seq_eff {Φ Ψ Ψ' : Footprint} {cl : ClassEvidence} {ρ₀ σ : Env} {h₀ h h' : Heap}
    (hp : Post Φ ρ₀ h₀ h) (hn : Post Ψ σ h h') (hr : Rebases Φ Ψ' ρ₀ h₀ Ψ σ h)
    (hle : Footprint.le cl (Φ ++ Ψ') Φ = true) (hc : ClassOk cl ρ₀ h₀) : Post Φ ρ₀ h₀ h' :=
  Post.compose_rebases hp hn hr hle hc

/-! ## Allocation between two entries -/

/-- **Allocation keeps every old location**: a heap extending another by
allocation is reached from it by an action of every frame. -/
theorem Post.of_prefix (Φ : Footprint) (ρ : Env) {h h' : Heap} (hp : h.IsPrefix h') : Post Φ ρ h h' := by
  obtain ⟨t, rfl⟩ := hp
  exact ⟨by simp, fun l v hv => ⟨v, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).1, hv],
    .inl rfl⟩⟩

/-- **A frame rebases to itself across an allocation** where each of its
entries selects, among the locations of the earlier heap, at the later heap
only locations it selects at the earlier one. -/
theorem Rebases.of_prefix {Ψ : Footprint} {ρ : Env} {h₀ h : Heap}
    (hm : ∀ e ∈ Ψ, ∀ l, l < h₀.length → e.1.mem ρ h l = true → e.1.mem ρ h₀ l = true) :
    Rebases [] Ψ ρ h₀ Ψ ρ h :=
  fun l hl e he hme => .inl ⟨e, he, hm e he l hl hme, Change.le_refl _⟩

end Verification.CallEffects

namespace Verification.CallEffects
open Verification Footprints Parity TolerantFrames

/-! ## An exit from an earlier entry -/

/-- **An exit reached from a later entry is an exit from an earlier one**
(the note, §6, Seq-Eff with the definition "Rebasing", and Entry): from the
earlier entry `s₀` an action of `Φ` reaches the later entry `s₁`; `x`'s exit
by `c` from `s₁` to `s₂`, its frame rebased to `s₀` as `Ψ` with
`Φ ∪ Ψ ⊑_cl` the frame of `y`'s exit and `cl` valid at `s₀`, and `y`'s
postconditions consequences of `x`'s read from the other entry, give `y`'s
exit by `c` from `s₀` to `s₂`. -/
theorem Exits.compose_entry {x y : Exits ExitSchema} {c : Completion} {r : Tm} {args : List Tm}
    {s₀ s₁ s₂ : IndexedHeap} {v : Tm} {Φ Ψ : Footprint} {cl : ClassEvidence}
    (h₁ : EffectAction Φ (callEnv r args) s₀ s₁)
    (hr : Rebases Φ Ψ (callEnv r args) s₀.h (x.get c).frame (callEnv r args) s₁.h)
    (hle : Footprint.le cl (Φ ++ Ψ) (y.get c).frame = true) (hcl : ClassOk cl (callEnv r args) s₀.h)
    (hq : ∀ u z, (∀ F ∈ ((x.atArity args.length).get c).ensures,
        Parity.Holds AssertionArena.empty (callState r args z s₁.h.length s₁ u) F) →
      ∀ F ∈ ((y.atArity args.length).get c).ensures,
        Parity.Holds AssertionArena.empty (callState r args z s₀.h.length s₀ u) F)
    (h₂ : x.exitPost c r args s₁ s₂ v) : y.exitPost c r args s₀ s₂ v := by
  unfold Exits.exitPost at h₂ ⊢
  obtain ⟨hf, he⟩ := h₂
  rw [Exits.atArity_frame] at hf
  refine ⟨?_, hq s₂ v he⟩
  rw [Exits.atArity_frame]
  exact ⟨WorldReach.trans h₁.1 hf.1, Post.compose_rebases h₁.2 hf.2 hr hle hcl⟩

/-! ## An exit across an allocation before the call -/

/-- **Whether a region's membership of a location reads the heap at that
location alone**: a field, the own locations or the store of a call
position, a class region, a module cell, or such a region in a class. A
region reading a path through the heap, or a store's element cells, reads
other locations. -/
def _root_.Verification.Footprints.Region.atLocation : Region → Bool
  | .field .. | .own _ | .cls _ | .all | .cell _ => true
  | .path _ [] _ | .pathOwn _ [] | .store _ [] => true
  | .inCls r _ => r.atLocation
  | _ => false

/-- **A region reading the heap at the location alone selects an old
location alike across an allocation** (proved). -/
theorem _root_.Verification.Footprints.Region.mem_prefix {R : Region} (hR : R.atLocation = true) {ρ : Env}
    {h₀ h : Heap} (hp : h₀.IsPrefix h) {l : Nat} (hl : l < h₀.length) : R.mem ρ h l = R.mem ρ h₀ l := by
  have hgl : h[l]? = h₀[l]? := by
    obtain ⟨t, rfl⟩ := hp
    exact List.getElem?_append_left hl
  induction R with
  | field | own | all => rfl
  | cls _ | cell _ => simp only [Region.mem, hgl]
  | path _ p _ => cases p <;> simp_all [Region.atLocation, Region.mem, HeapKnowledge.readPath]
  | pathOwn _ p => cases p <;> simp_all [Region.atLocation, Region.mem, HeapKnowledge.readPath]
  | store _ p => cases p <;> simp_all [Region.atLocation, Region.mem, HeapKnowledge.readPath]
  | inCls r _ ih => simp only [Region.atLocation] at hR; simp only [Region.mem, ih hR, hgl]
  | elems | pathElems => simp [Region.atLocation] at hR

/-- **A schema whose exits carry across an allocation before the call**:
an exit from a later entry whose heap extends an earlier one's, at a world
the earlier reaches, is an exit from the earlier entry. A body run after
allocating its rest array meets its signature from the invocation's entry
by it. -/
def Exits.AllocStable (x : Exits ExitSchema) : Prop :=
  ∀ (c : Completion) (r : Tm) (args : List Tm) (s₀ s₁ s₂ : IndexedHeap) (v : Tm),
    Admissible s₀ s₁ → s₀.h.IsPrefix s₁.h → x.exitPost c r args s₁ s₂ v → x.exitPost c r args s₀ s₂ v

/-- **A sufficient check of carrying across an allocation** (proved,
`Exits.compose_entry`): each frame's regions read the heap at the location
alone (`Region.atLocation`), so the frame rebases to itself
(`Rebases.of_prefix`), and each postcondition is a fresh result, which the
earlier entry's lower mark keeps (`FreshAt.lower`). -/
theorem Exits.allocStable_of {x : Exits ExitSchema}
    (hfr : ∀ c, (x.get c).frame.all (·.1.atLocation) = true)
    (hens : ∀ c, ∀ F ∈ (x.get c).ensures, F = .operation (.freshStore 0)) : x.AllocStable := by
  intro c r args s₀ s₁ s₂ v hadm hprefix h
  refine Exits.compose_entry (Φ := []) (cl := fun _ _ => none) ⟨hadm, Post.of_prefix _ _ hprefix⟩
    (Rebases.of_prefix fun e he l hl hm => by
      rwa [← Region.mem_prefix (List.all_eq_true.mp (hfr c) e he) hprefix hl])
    (Footprint.le_refl _ _) (fun _ _ _ _ hc => by cases hc) ?_ h
  intro u z hF F hFm
  have hens' := hens c
  cases c <;>
  · simp only [Exits.atArity, Exits.map, Exits.get, ExitSchema.instantiate, List.mem_map] at hFm hF hens'
    obtain ⟨G, hG, rfl⟩ := hFm
    have hH := hF _ ⟨G, hG, rfl⟩
    rw [hens' G hG] at hH ⊢
    exact FreshAt.lower hprefix.length_le hH
