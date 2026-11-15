import Verification.Semantics.CommandSummaries

/-! # Composing command summaries

The summary of a composite command from its parts' summaries (the note
*Tolerant frames*, §6, Seq-Eff and the definition "Rebasing", with the
corrections 3 and 4 of `docs/drafts/effects-of-commands.md`).

**Rebasing** (`Rebases`) is the note's definition with its absorption made
explicit: every location of the composite's entry heap that a later frame,
read where the later command starts, covers at a change `δ` is covered by
the rebased frame at `δ` or a wider change, or by an entry of the frame so
far at `any`. The computed rebasing `rebaseAll` meets it under `RebaseOk`
(`rebases_of_rebaseOk`), and with a checked inclusion from the entry
(`Footprint.le`, class evidence valid at the entry heap) it composes the
frames (`Post.compose_rebases`); the note's displayed rule
`Φ ∪ Ψ' ⊑ Φ` is the instance whose bound is the frame so far
(`Post.seq_eff`).

**One exit followed by one exit** (`ThenEvidence`): a first command's exit
`q₁`, then a second command's exit `q₂` from the state and valuation that
exit leaves, are within `q` when the rebased frames are within `q`'s frame
and `q`'s postconditions are checked consequences of what the two exits
establish: the first's consequences reading its entry, and the second's
consequences reading its exit, derived from the second's postconditions and
the first's consequences reading the intermediate state, carried entry and
exit exchanged (`holds_carry`). The intermediate state stays explicit: no
postcondition of one command is read at the other's two-state.

**Sequence** (`Runs.seq`, `CommandSummary.seq_sound`): its normal exit is
the first's normal exit followed by the second's; its exceptional exit is
the first's throw, or the first's normal exit followed by the second's
throw. -/
namespace Verification.CallEffects
open Verification Footprints HeapKnowledge TolerantFrames Parity

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
entry. -/
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

/-! ## One exit followed by another -/

/-- **The evidence composing one exit with a later one**: the rebasing of
the later frame and the class evidence of the inclusion; the first exit's
consequences reading its entry (`entry`) and its exit (`carry`); and the
consequences over the later command reading its exit (`mid`). -/
structure ThenEvidence where
  rebase : RebaseEvidence
  cl : ClassEvidence
  entry : List Formula
  carry : List Formula
  mid : List Formula

/-- **The evidence holds of a first exit `q₁` and a later exit `q₂`** from
the entry condition `P`: its class evidence holds at every entry meeting
`P`, its rebasing at every exit `q₁` reaches from one, and each list is the
consequence it states, reading the phase it states. -/
structure ThenEvidence.Valid (arena : AssertionArena) (P : Assertion) (q₁ q₂ : ExitSpec) (ev : ThenEvidence) :
    Prop where
  classOk : ∀ η m st, P η m st → ClassOk ev.cl η st.h
  rebaseOk : ∀ s, s.Entry P → q₁.Holds arena s → RebaseOk ev.rebase s.afterEnv s.beforeEnv s.before.h s.after.h
  entryReads : ev.entry.all (Formula.reads .before) = true
  carryReads : ev.carry.all (Formula.reads .after) = true
  midReads : ev.mid.all (Formula.reads .after) = true
  entryOk : Consequence arena q₁.facts ev.entry
  carryOk : Consequence arena q₁.facts ev.carry
  midOk : Consequence arena (ev.carry.map Formula.swap ++ q₂.facts) ev.mid

/-- **The composite exit is within `q`**: the frames, rebased, within `q`'s
frame by checked inclusion, and `q`'s postconditions consequences of its
frame's transition, the entry consequences and the later consequences. -/
structure ThenEvidence.Into (arena : AssertionArena) (q₁ q₂ : ExitSpec) (ev : ThenEvidence) (q : ExitSpec) :
    Prop where
  frame : Footprint.le ev.cl (q₁.frame ++ rebaseAll ev.rebase q₂.frame) q.frame = true
  ensuresOk : Consequence arena (.transition q.frame :: (ev.entry ++ ev.mid)) q.ensures

/-- **The composite exit the evidence states**: the frame so far with the
rebased later frame, and the consequences reading the entry and the exit. -/
def ThenEvidence.spec (ev : ThenEvidence) (q₁ q₂ : ExitSpec) : ExitSpec :=
  ⟨q₁.frame ++ rebaseAll ev.rebase q₂.frame, ev.entry ++ ev.mid⟩

/-- The evidence's own composite exit is within itself. -/
theorem ThenEvidence.into_spec (arena : AssertionArena) (q₁ q₂ : ExitSpec) (ev : ThenEvidence) :
    ev.Into arena q₁ q₂ (ev.spec q₁ q₂) :=
  ⟨Footprint.le_refl _ _, Consequence.mono (fun _ h => List.mem_cons_of_mem _ h) (Consequence.refl _ _)⟩

/-- **One exit followed by another** (the note, §6, Seq-Eff and Entry, at
two exits): from an entry meeting `P`, the first command's exit `q₁` to the
intermediate state and valuation, and the later command's exit `q₂` from
there, give `q` from the entry to the later exit. -/
theorem ThenEvidence.sound {arena : AssertionArena} {P : Assertion} {q₁ q₂ q : ExitSpec} {ev : ThenEvidence}
    (hv : ev.Valid arena P q₁ q₂) (hi : ev.Into arena q₁ q₂ q) {ρ₀ η ρ₂ : Env} {m : Nat}
    {t₀ t₁ t₂ : IndexedHeap} (hP : P ρ₀ m t₀) (h₁ : q₁.Holds arena ⟨ρ₀, η, m, t₀, t₁⟩)
    (h₂ : q₂.Holds arena ⟨η, ρ₂, m, t₁, t₂⟩) : q.Holds arena ⟨ρ₀, ρ₂, m, t₀, t₂⟩ := by
  have hf₁ := ExitSpec.holds_iff_facts.mp h₁
  have hf₂ := ExitSpec.holds_iff_facts.mp h₂
  have hk := hv.rebaseOk ⟨ρ₀, η, m, t₀, t₁⟩ hP h₁
  have hfr : EffectAction q.frame ρ₀ t₀ t₂ :=
    ⟨Admissible.trans h₁.1.1 h₂.1.1,
      Post.compose_rebases h₁.1.2 h₂.1.2 (rebases_of_rebaseOk h₁.1.2 hk) hi.frame (hv.classOk _ _ _ hP)⟩
  refine ⟨hfr, hi.ensuresOk _ ?_⟩
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hfr
  rcases List.mem_append.mp hF with hF | hF
  · exact (holds_reads (p := .before) (s := ⟨ρ₀, η, m, t₀, t₁⟩) (s' := ⟨ρ₀, ρ₂, m, t₀, t₂⟩) rfl rfl rfl (List.all_eq_true.mp hv.entryReads F hF)).mp
      (hv.entryOk _ hf₁ F hF)
  · have hc : ∀ G ∈ ev.carry.map Formula.swap ++ q₂.facts, Parity.Holds arena ⟨η, ρ₂, m, t₁, t₂⟩ G := by
      intro G hG
      rcases List.mem_append.mp hG with hG | hG
      · obtain ⟨G₀, hG₀, rfl⟩ := List.mem_map.mp hG
        exact holds_carry (s₁ := ⟨ρ₀, η, m, t₀, t₁⟩) (s₂ := ⟨η, ρ₂, m, t₁, t₂⟩) rfl rfl rfl (List.all_eq_true.mp hv.carryReads G₀ hG₀) (hv.carryOk _ hf₁ G₀ hG₀)
      · exact hf₂ G hG
    exact (holds_reads (p := .after) (s := ⟨η, ρ₂, m, t₁, t₂⟩) (s' := ⟨ρ₀, ρ₂, m, t₀, t₂⟩) rfl rfl rfl
      (List.all_eq_true.mp hv.midReads F hF)).mp (hv.midOk _ hc F hF)

/-! ## Runs in sequence -/

/-- **A run completing by `k₁`, then a run from the state and valuation it
leaves completing by `k₂`.** -/
def Runs.then (R₁ : Runs) (k₁ : Completion) (R₂ : Runs) (k₂ : Completion) (s : TwoState) : Prop :=
  ∃ η t, R₁ k₁ ⟨s.beforeEnv, η, s.mark, s.before, t⟩ ∧ R₂ k₂ ⟨η, s.afterEnv, s.mark, t, s.after⟩

/-- **The runs of a sequence `c₁; c₂`** (the design's table "Composition
follows the control-flow exits"): it returns where `c₁` returns and then
`c₂` returns; it throws where `c₁` throws, or `c₁` returns and then `c₂`
throws. -/
def Runs.seq (R₁ R₂ : Runs) : Runs
  | .normal, s => R₁.then .normal R₂ .normal s
  | .exceptional, s => R₁ .exceptional s ∨ R₁.then .normal R₂ .exceptional s

/-- **Summaries compose along one exit followed by another**: the first's
summary sound from `P`, the later one's from `P₂`, `P₂` holding where the
first's exit `k₁` leaves an entry meeting `P`, and the evidence give `q`
for every such pair of runs. -/
theorem Runs.then_sound {arena : AssertionArena} {P P₂ : Assertion} {R₁ R₂ : Runs} {A B : CommandSummary}
    {k₁ k₂ : Completion} {ev : ThenEvidence} {q : ExitSpec} (hA : A.Sound arena P R₁) (hB : B.Sound arena P₂ R₂)
    (hmid : ∀ s, s.Entry P → (A.get k₁).Holds arena s → P₂ s.afterEnv s.mark s.after)
    (hv : ev.Valid arena P (A.get k₁) (B.get k₂)) (hi : ev.Into arena (A.get k₁) (B.get k₂) q) :
    ∀ s, s.Entry P → R₁.then k₁ R₂ k₂ s → q.Holds arena s := by
  rintro ⟨ρ₀, ρ₂, m, t₀, t₂⟩ hP ⟨η, t₁, r₁, r₂⟩
  have a₁ := hA k₁ ⟨ρ₀, η, m, t₀, t₁⟩ hP r₁
  have a₂ := hB k₂ ⟨η, ρ₂, m, t₁, t₂⟩ (hmid ⟨ρ₀, η, m, t₀, t₁⟩ hP a₁) r₂
  exact ev.sound (η := η) (t₁ := t₁) hv hi hP a₁ a₂

/-- **Seq-Eff on both exits** (the note, §6, Seq-Eff; the design's
corrections 3 and 4): the summary `C` of `c₁; c₂` is sound where its normal
exit is within `c₁`'s normal exit followed by `c₂`'s, its exceptional exit
within `c₁`'s throw, and within `c₁`'s normal exit followed by `c₂`'s
throw. -/
theorem CommandSummary.seq_sound {arena : AssertionArena} {P P₂ : Assertion} {R₁ R₂ : Runs}
    {A B C : CommandSummary} {evn evx : ThenEvidence} (hA : A.Sound arena P R₁) (hB : B.Sound arena P₂ R₂)
    (hmid : ∀ s, s.Entry P → A.normal.Holds arena s → P₂ s.afterEnv s.mark s.after)
    (hn : evn.Valid arena P A.normal B.normal) (hni : evn.Into arena A.normal B.normal C.normal)
    (hx : evx.Valid arena P A.normal B.exceptional) (hxi : evx.Into arena A.normal B.exceptional C.exceptional)
    (hw : A.exceptional.Weakens arena P C.exceptional) : C.Sound arena P (R₁.seq R₂) := by
  intro c s hP hr
  cases c with
  | normal => exact Runs.then_sound (k₁ := .normal) (k₂ := .normal) hA hB hmid hn hni s hP hr
  | exceptional =>
    rcases hr with hr | hr
    · exact hw s hP (hA .exceptional s hP hr)
    · exact Runs.then_sound (k₁ := .normal) (k₂ := .exceptional) hA hB hmid hx hxi s hP hr

end Verification.CallEffects
