import Verification.Semantics.CommandSummaries
import Verification.Semantics.FootprintJoin

/-! # Composing command summaries

The summary of a composite command from its parts' summaries (the note
*Tolerant frames*, §6, Seq-Eff and the definition "Rebasing", with the
corrections 3 and 4 of `docs/drafts/effects-of-commands.md`).

**Rebasing** (`Rebases`, with the general Seq-Eff `Post.compose_rebases`,
stated in `ExitComposition`) is the note's definition with its absorption made
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
throw.

**Handler** (`Runs.handle`, `CommandSummary.handle_sound`): the normal exit
of `try c catch (x) d` is `c`'s return, or `c`'s throw followed by `d`'s
return; its exceptional exit is `c`'s throw followed by `d`'s throw.

**Choice** (`Runs.choice`, `CommandSummary.join_sound`): the join of the
branches' summaries, the frames by entry-wise maximum (`Footprint.join`) and
the postconditions those both state or that checked consequence derives
from each.

**Fresh-Eff** (`Post.fresh_eff`, `ThenEvidence.into_fresh`) is part of
rebasing: a later entry for a spine the evidence states fresh relative to
the composite's entry heap rebases to none, while the entries of that
spine's cells and every class entry are kept (`rebaseAll_fresh_eff`). -/
namespace Verification.CallEffects
open Verification Footprints HeapKnowledge TolerantFrames Parity

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
  entryReads : ev.entry.all (FormulaF.reads .before) = true
  carryReads : ev.carry.all (FormulaF.reads .after) = true
  midReads : ev.mid.all (FormulaF.reads .after) = true
  entryOk : Consequence arena q₁.facts ev.entry
  carryOk : Consequence arena q₁.facts ev.carry
  midOk : Consequence arena (ev.carry.map FormulaF.swap ++ q₂.facts) ev.mid

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
  · have hc : ∀ G ∈ ev.carry.map FormulaF.swap ++ q₂.facts, Parity.Holds arena ⟨η, ρ₂, m, t₁, t₂⟩ G := by
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

/-! ## Handlers -/

/-- **The runs of a handler `try c catch (x) d`** (the note, §3, "The
effect of a command": a throw that a command catches is no exit of it): it
returns where `c` returns, or `c` throws and then `d` returns; it throws
where `c` throws and then `d` throws. `d` starts from the state and
valuation `c`'s throw leaves, whose slot `0` is the thrown value. -/
def Runs.handle (R₁ R₂ : Runs) : Runs
  | .normal, s => R₁ .normal s ∨ R₁.then .exceptional R₂ .normal s
  | .exceptional, s => R₁.then .exceptional R₂ .exceptional s

/-- **The handler's summary** (the design's corrections 4: a caught throw
contributes to the handler's eventual exit): the summary `C` of
`try c catch (x) d` is sound where its normal exit is within `c`'s normal
exit, and within `c`'s throw followed by `d`'s return, and its exceptional
exit within `c`'s throw followed by `d`'s throw. -/
theorem CommandSummary.handle_sound {arena : AssertionArena} {P P₂ : Assertion} {R₁ R₂ : Runs}
    {A B C : CommandSummary} {evn evx : ThenEvidence} (hA : A.Sound arena P R₁) (hB : B.Sound arena P₂ R₂)
    (hmid : ∀ s, s.Entry P → A.exceptional.Holds arena s → P₂ s.afterEnv s.mark s.after)
    (hw : A.normal.Weakens arena P C.normal)
    (hn : evn.Valid arena P A.exceptional B.normal) (hni : evn.Into arena A.exceptional B.normal C.normal)
    (hx : evx.Valid arena P A.exceptional B.exceptional)
    (hxi : evx.Into arena A.exceptional B.exceptional C.exceptional) : C.Sound arena P (R₁.handle R₂) := by
  intro c s hP hr
  cases c with
  | normal =>
    rcases hr with hr | hr
    · exact hw s hP (hA .normal s hP hr)
    · exact Runs.then_sound (k₁ := .exceptional) (k₂ := .normal) hA hB hmid hn hni s hP hr
  | exceptional => exact Runs.then_sound (k₁ := .exceptional) (k₂ := .exceptional) hA hB hmid hx hxi s hP hr

/-! ## Choice -/

/-- The class evidence stating no class: it holds at every heap. -/
theorem classOk_none (ρ : Env) (h : Heap) : ClassOk (fun _ _ => none) ρ h :=
  fun _ _ _ _ hc => by cases hc

/-- **The join of two exit specifications**: the join of the frames, and
the postconditions both state, with `extra`, formulas checked to follow
from each. -/
def ExitSpec.join (q q' : ExitSpec) (extra : List Formula) : ExitSpec :=
  ⟨Footprint.join q.frame q'.frame, q.ensures.filter (fun F => q'.ensures.contains F) ++ extra⟩

/-- **Each specification is within the join** (the design, "Join
alternative executions by an upper bound"): where `extra` follows from
each one's formulas. -/
theorem ExitSpec.weakens_join {arena : AssertionArena} {P : Assertion} {q q' : ExitSpec} {extra : List Formula}
    (h : Consequence arena q.facts extra) (h' : Consequence arena q'.facts extra) :
    q.Weakens arena P (q.join q' extra) ∧ q'.Weakens arena P (q.join q' extra) := by
  have hcl : ∀ η m (st : IndexedHeap), P η m st → ClassOk (fun _ _ => none) η st.h :=
    fun η _ st _ => classOk_none η st.h
  obtain ⟨c₁, c₂⟩ := Footprint.covers_join q.frame q'.frame
  refine ⟨ExitSpec.weakens_of hcl (c₁.le _) ?_, ExitSpec.weakens_of hcl (c₂.le _) ?_⟩
  · intro s hs G hG
    rcases List.mem_append.mp hG with hG | hG
    · exact hs G (List.mem_cons_of_mem _ (List.mem_filter.mp hG).1)
    · exact h s hs G hG
  · intro s hs G hG
    rcases List.mem_append.mp hG with hG | hG
    · have := (List.mem_filter.mp hG).2
      exact hs G (List.mem_cons_of_mem _ (List.contains_iff_mem.mp this))
    · exact h' s hs G hG

/-- **The runs of a choice between two commands**: the runs of either. A
branch on a guard is the choice whose runs are the guarded branches' runs. -/
def Runs.choice (R₁ R₂ : Runs) : Runs := fun c s => R₁ c s ∨ R₂ c s

/-- **The summary of a choice**: within each branch's summary at each exit,
from the entry condition. -/
theorem CommandSummary.choice_sound {arena : AssertionArena} {P : Assertion} {R₁ R₂ : Runs}
    {A B C : CommandSummary} (hA : A.Sound arena P R₁) (hB : B.Sound arena P R₂)
    (wA : ∀ c, (A.get c).Weakens arena P (C.get c)) (wB : ∀ c, (B.get c).Weakens arena P (C.get c)) :
    C.Sound arena P (R₁.choice R₂) := by
  intro c s hP hr
  rcases hr with hr | hr
  · exact wA c s hP (hA c s hP hr)
  · exact wB c s hP (hB c s hP hr)

/-- **The join of two summaries**, exit by exit, with the formulas `extra`
checked to follow from both. -/
def CommandSummary.join (A B : CommandSummary) (extra : Exits (List Formula)) : CommandSummary :=
  ⟨A.normal.join B.normal extra.normal, A.exceptional.join B.exceptional extra.exceptional⟩

/-- **Choice** (the join of the branches' summaries): the frames' entry-wise
maximum and the postconditions both branches establish. -/
theorem CommandSummary.join_sound {arena : AssertionArena} {P : Assertion} {R₁ R₂ : Runs} {A B : CommandSummary}
    {extra : Exits (List Formula)} (hA : A.Sound arena P R₁) (hB : B.Sound arena P R₂)
    (eA : ∀ c, Consequence arena (A.get c).facts (extra.get c))
    (eB : ∀ c, Consequence arena (B.get c).facts (extra.get c)) :
    (A.join B extra).Sound arena P (R₁.choice R₂) := by
  have hw : ∀ c, (A.get c).Weakens arena P ((A.join B extra).get c) ∧
      (B.get c).Weakens arena P ((A.join B extra).get c) := by
    intro c
    cases c with
    | normal => exact ExitSpec.weakens_join (eA .normal) (eB .normal)
    | exceptional => exact ExitSpec.weakens_join (eA .exceptional) (eB .exceptional)
  exact CommandSummary.choice_sound hA hB (fun c => (hw c).1) (fun c => (hw c).2)

/-- **The summary of a sequence from its parts' summaries**: the normal
exit the evidence states, and the join of the first's throw with the first's
return followed by the second's throw. -/
def CommandSummary.seq (A B : CommandSummary) (evn evx : ThenEvidence) (extra : List Formula) : CommandSummary :=
  ⟨evn.spec A.normal B.normal, A.exceptional.join (evx.spec A.normal B.exceptional) extra⟩

/-- **The computed summary of a sequence is sound.** -/
theorem CommandSummary.seq_spec_sound {arena : AssertionArena} {P P₂ : Assertion} {R₁ R₂ : Runs}
    {A B : CommandSummary} {evn evx : ThenEvidence} {extra : List Formula} (hA : A.Sound arena P R₁)
    (hB : B.Sound arena P₂ R₂) (hmid : ∀ s, s.Entry P → A.normal.Holds arena s → P₂ s.afterEnv s.mark s.after)
    (hn : evn.Valid arena P A.normal B.normal) (hx : evx.Valid arena P A.normal B.exceptional)
    (e₁ : Consequence arena A.exceptional.facts extra)
    (e₂ : Consequence arena (evx.spec A.normal B.exceptional).facts extra) :
    (A.seq B evn evx extra).Sound arena P (R₁.seq R₂) := by
  obtain ⟨w₁, w₂⟩ := ExitSpec.weakens_join (P := P) e₁ e₂
  intro c s hP hr
  cases c with
  | normal =>
    exact Runs.then_sound (k₁ := .normal) (k₂ := .normal) hA hB hmid hn (evn.into_spec arena _ _) s hP hr
  | exceptional =>
    rcases hr with hr | hr
    · exact w₁ s hP (hA .exceptional s hP hr)
    · exact w₂ s hP (Runs.then_sound (k₁ := .normal) (k₂ := .exceptional) hA hB hmid hx
        (evx.into_spec arena _ _) s hP hr)

/-! ## Fresh-Eff -/

/-- An entry whose region rebases to none is erased by rebasing. -/
theorem rebaseAll_append_erased (ev : RebaseEvidence) (Ψ : Footprint) {e : Region × Change}
    (he : rebase ev e.1 = []) : rebaseAll ev (Ψ ++ [e]) = rebaseAll ev Ψ := by
  simp [rebaseAll, List.flatMap_append, he]

/-- **A spine the evidence states fresh rebases to none**: the spine of a
position's value, at the empty path, and at a path. -/
theorem rebase_fresh_spine (ev : RebaseEvidence) {x : Nat} {p : List String}
    (hf : ev.freshPath x p arraySpineKey = true) :
    rebase ev (.path x p arraySpineKey) = [] ∧ (p = [] → rebase ev (.field x arraySpineKey) = []) := by
  refine ⟨by simp [rebase, hf], fun hp => ?_⟩
  subst hp
  simp [rebase, hf]

/-- **Fresh-Eff erases the fresh spine alone** (the note, §6, Fresh-Eff: "a
fresh spine may list a cell of the entry heap, and a change of that cell is
part of the effect"; "a write through a fresh typed array keeps its entry
`views: grow`"): rebasing removes the fresh spine's entry and keeps the
entries of its cells, at the value class, and of every class region. -/
theorem rebaseAll_fresh_eff (ev : RebaseEvidence) (Ψ : Footprint) {x : Nat} {δ : Change}
    (hf : ev.freshPath x [] arraySpineKey = true) :
    rebaseAll ev (Ψ ++ [(.field x arraySpineKey, δ)]) = rebaseAll ev Ψ ∧
      rebaseAll ev (Ψ ++ [(.cells x, δ)]) = rebaseAll ev Ψ ++ [(.cls .values, δ)] ∧
      ∀ c, rebaseAll ev (Ψ ++ [(.cls c, δ)]) = rebaseAll ev Ψ ++ [(.cls c, δ)] := by
  refine ⟨rebaseAll_append_erased ev Ψ ((rebase_fresh_spine ev hf).2 rfl), ?_, fun c => ?_⟩
  · simp [rebaseAll, List.flatMap_append, rebase]
  · simp [rebaseAll, List.flatMap_append, rebase]

/-- **Fresh-Eff from the composite's entry** (the note, §6, Fresh-Eff,
`c : Φ ∪ {x.spine : δ}` and `fresh(x)` before `c` give `c : Φ` from the
entry): a later frame with an entry for the spine of position `x`, that
spine fresh relative to the entry heap by the rebasing's evidence, composes
as the frame without that entry. -/
theorem Post.fresh_eff {Φp Ψ Φq : Footprint} {x : Nat} {δ : Change} {cl : ClassEvidence} {ρ₀ σ : Env}
    {h₀ h h' : Heap} {ev : RebaseEvidence} (hf : ev.freshPath x [] arraySpineKey = true)
    (hp : Post Φp ρ₀ h₀ h) (hn : Post (Ψ ++ [(.field x arraySpineKey, δ)]) σ h h') (hk : RebaseOk ev σ ρ₀ h₀ h)
    (hle : Footprint.le cl (Φp ++ rebaseAll ev Ψ) Φq = true) (hc : ClassOk cl ρ₀ h₀) : Post Φq ρ₀ h₀ h' := by
  refine Post.compose_rebases hp hn (rebases_of_rebaseOk hp hk) ?_ hc
  rw [(rebaseAll_fresh_eff ev Ψ hf).1]
  exact hle

/-- **Fresh-Eff at an exit followed by another**: the composite exit's frame
need not cover the later exit's entry for a spine its evidence states fresh. -/
theorem ThenEvidence.into_fresh {arena : AssertionArena} {q₁ q : ExitSpec} {ev : ThenEvidence} {Ψ : Footprint}
    {ens : List Formula} {x : Nat} {δ : Change} (hf : ev.rebase.freshPath x [] arraySpineKey = true)
    (hle : Footprint.le ev.cl (q₁.frame ++ rebaseAll ev.rebase Ψ) q.frame = true)
    (he : Consequence arena (.transition q.frame :: (ev.entry ++ ev.mid)) q.ensures) :
    ev.Into arena q₁ ⟨Ψ ++ [(.field x arraySpineKey, δ)], ens⟩ q := by
  refine ⟨?_, he⟩
  show Footprint.le ev.cl (q₁.frame ++ rebaseAll ev.rebase (Ψ ++ [(.field x arraySpineKey, δ)])) q.frame = true
  rw [(rebaseAll_fresh_eff ev.rebase Ψ hf).1]
  exact hle

/-- **The fresh spine's evidence**: a spine allocated at or beyond the entry
heap's length meets the rebasing's freshness at the empty path. -/
theorem freshIfSpine_of_freshAt {b : Nat} {σ : Env} {x : Nat} {h : Heap} (hf : FreshAt b (σ x)) :
    ∀ v, HeapKnowledge.readPath h (σ x) [] = some v → FreshIfSpine b v := by
  intro v hv
  simp only [HeapKnowledge.readPath, Option.some.injEq] at hv
  subst hv
  exact hf.ifSpine

end Verification.CallEffects
