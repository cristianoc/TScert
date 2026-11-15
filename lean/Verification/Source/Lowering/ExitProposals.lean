import Verification.Semantics.CommandComposition
import Verification.Programs.FrameChecks

/-! # Proposed exit summaries

What the front proposes about a function literal's unwritten effect
(`Synthesis.walkLambda`) is a **command summary at the class level**: per
exit, the closed bound of its frame, `none` where that exit is unreachable
(`ClassSummary`). It is computed from a summary of each operation the walk
meets, composed along control flow by the rules of the note *Tolerant
frames*, §6:

- **an operation's summary** (`ClassSummary.ofEffect`): a call's is its
  instance's per-exit contract (`CallEffects.Effect.summary`), each exit's
  frame read in the closed language below the call's entry mark
  (`Footprint.boundBelow`), the positions the walk knows to hold a fresh store
  discharged (Fresh-Eff); a write's is the grade its typed-write rule
  accepts; a `throw` returns never and leaves the heap it starts in;
- **sequence on both exits** (`ClassSummary.seq`, Seq-Eff at two exits,
  `CommandSummary.seq`): a throw includes the effect of the whole prefix
  before it (`ClassSummary.seq_into`);
- **choice** (`ClassSummary.choice`, `CommandSummary.join`): exit by exit,
  the join of the alternatives;
- **handler** (`ClassSummary.handle`, `CommandSummary.handle_sound`): a caught
  throw continues at the handler, whose exits are the statement's;
- **closure** (`ClassSummary.close`): class entries are rigid, so a frame
  joining every operation's normal frame is closed under another traversal of
  any loop; every throw's prefix is within it.

Class entries rebase to themselves (`rebaseAll_fp`), so composition at the
class level is the join of the closed bounds (`ClassSummary.then_into`).

The proposal is a proposal: the walk of the literal's body at the effect it
is offered at, with the footprint check of each step
(`SinglePass.footprintCheck`) and the records' admission
(`SinglePass.recordsAdmit`), decides whether it holds. Today's effect format
receives it through one projection (`ClassSummary.project`), an upper bound
of the summary at each exit (`ClassSummary.project_covers`). -/
namespace Verification.SourceExtraction
open Verification Footprints CallEffects Parity

abbrev Closed := Footprints.Closed

/-- **A proposed command summary at the class level**: per exit, the closed
bound of its frame (the note, §6, the judgment $c:\Phi\mid\Phi^{e}$, each
frame its three class entries), `none` where no run completes by it. -/
abbrev ClassSummary := Exits (Option Closed)

namespace ClassSummary

/-- One completion followed by another: both reached, their frames joined
(Seq-Eff on class entries). -/
def andThen : Option Closed → Option Closed → Option Closed
  | some a, some b => some (a.join b)
  | _, _ => none

/-- Two alternative completions: the join of those reached. -/
def alt : Option Closed → Option Closed → Option Closed
  | some a, some b => some (a.join b)
  | some a, none => some a
  | none, b => b

/-- The empty command: it returns, changing nothing; it never throws. -/
def skip : ClassSummary := ⟨some .empty, none⟩

/-- **Sequence** (`CommandSummary.seq`; the design's table "Composition
follows the control-flow exits"): it returns where the first returns and then
the second; it throws where the first throws, or the first returns and then
the second throws. -/
def seq (A B : ClassSummary) : ClassSummary :=
  ⟨andThen A.normal B.normal, alt A.exceptional (andThen A.normal B.exceptional)⟩

/-- **Choice** (`CommandSummary.join`): exit by exit, the join. -/
def choice (A B : ClassSummary) : ClassSummary :=
  ⟨alt A.normal B.normal, alt A.exceptional B.exceptional⟩

/-- **Handler** (`CommandSummary.handle_sound`): `try c catch d` returns where
`c` returns or `c` throws and then `d` returns; it throws where `c` throws and
then `d` throws. -/
def handle (A D : ClassSummary) : ClassSummary :=
  ⟨alt A.normal (andThen A.exceptional D.normal), andThen A.exceptional D.exceptional⟩

/-- **The summary walked so far extended by one more operation**: the paths
walked so far, or those followed by the operation (`choice S (seq S op)`). A
walk that visits every operation of a body in an order extending its control
flow, each once or more, accumulates through it an upper bound of the
body's paths. -/
def extend (S op : ClassSummary) : ClassSummary := choice S (seq S op)

/-- **The closure of a walked summary** (the note, §6, "Loops", rigid class
entries): every throw is reached after a prefix of the operations' normal
frames, all within the normal frame walked, so the exceptional frame joins
it. A frame closed in this way is closed under another traversal of every
loop of the body. -/
def close (S : ClassSummary) : ClassSummary :=
  ⟨S.normal, alt S.exceptional (andThen S.exceptional S.normal)⟩

/-- **The summary of an operation of a callable contract**, the positions `P`
holding stores allocated after the call's entry (Fresh-Eff): each exit's
frame of the instance's per-exit contract (`Effect.summary`, whose frames
read no arity), read in the closed language below the entry mark
(`Footprint.boundBelow`); the normal exit unreached where the result is
empty. -/
def ofEffect (e : Effect) (P : List Nat) (returns : Bool := true) : ClassSummary :=
  ⟨if returns then some (Footprint.boundBelow P (e.summary 0).normal.frame) else none,
    some (Footprint.boundBelow P (e.summary 0).exceptional.frame)⟩

/-- An operation that returns within a closed bound and never throws. -/
def ofClosed (c : Closed) : ClassSummary := ⟨some c, none⟩

/-- A `throw`: it never returns, and throws leaving the heap it starts in. -/
def raise : ClassSummary := ⟨none, some .empty⟩

/-- An async body's summary: a throw rejects the promise the call returned,
a normal return of the call; the call never throws, its exceptional exit
unreached. -/
def settle (S : ClassSummary) : ClassSummary := ⟨alt S.normal S.exceptional, none⟩

/-- **The projection into today's effect format**: the effect of a closed
frame and a throw bound (`Effect.ofFootprint`, `onThrow`) whose closed frame
is the normal exit's bound, the least such effect whose per-exit contract
includes the summary (`project_covers`): its throw bounded where `bounded`
asks for it and the exceptional exit's bound is within the normal one's, or
unreached. Where the exceptional bound is within the normal one it is the
least effect of today's format including the summary. A throw bound at
`top` states nothing (the exceptional frame `⊤` either way), so `top` is
projected with none, the form `Effect.summary` elaborates. -/
def project (S : ClassSummary) (bounded : Bool := true) : Effect :=
  let n := S.normal.getD .empty
  { Effect.ofFootprint n with
    onThrow := bounded && n != Closed.top && (match S.exceptional with
      | none => true
      | some x => x.le n) }

/-- **Today's format embedded in a summary**: the per-exit contract of the
effect of closed frame `c` and throw bound `t`, at the class level
(`ofEffect`). -/
def ofFormat (c : Closed) (t : Bool) : ClassSummary := ofEffect { Effect.ofFootprint c with onThrow := t } []

/-! ## Each rule is the class instance of the note's -/

theorem andThen_le {a b : Option Closed} {c : Closed} (h : andThen a b = some c) :
    ∃ x y, a = some x ∧ b = some y ∧ c = x.join y := by
  cases a <;> cases b <;> simp_all [andThen]

/-- **Class entries rebase to themselves** (the note's definition
"Rebasing", class regions). -/
theorem rebaseAll_fp (ev : RebaseEvidence) (c : Closed) : rebaseAll ev c.fp = c.fp := rfl

/-- The join's class entries cover both frames' entries. -/
theorem fp_join_covers (a b : Closed) : Footprint.Covers (a.fp ++ b.fp) (a.join b).fp := by
  intro e he
  rcases a with ⟨v, r, w⟩
  rcases b with ⟨v', r', w'⟩
  simp only [Closed.fp, Closed.join, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at he ⊢
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(.cls .values, v.max v'), by simp, rfl, Change.le_max_left _ _⟩
  · exact ⟨(.cls .arrays, r.max r'), by simp, rfl, Change.le_max_left _ _⟩
  · exact ⟨(.cls .views, w.max w'), by simp, rfl,
      Change.le_max_left _ _⟩
  · exact ⟨(.cls .values, v.max v'), by simp, rfl, Change.le_max_right _ _⟩
  · exact ⟨(.cls .arrays, r.max r'), by simp, rfl, Change.le_max_right _ _⟩
  · exact ⟨(.cls .views, w.max w'), by simp, rfl,
      Change.le_max_right _ _⟩

/-- **One exit followed by another, at the class level, is Seq-Eff**
(`ThenEvidence.Into`): for any rebasing and class evidence, a first exit of
frame `a.fp` followed by a later exit of frame `b.fp` is within the exit of
frame `(a.join b).fp` (no postcondition). -/
theorem then_into (arena : AssertionArena) (ev : ThenEvidence) (a b : Closed) :
    ev.Into arena ⟨a.fp, []⟩ ⟨b.fp, []⟩ ⟨(a.join b).fp, []⟩ :=
  ⟨by simpa [rebaseAll_fp] using (fp_join_covers a b).le ev.cl, Consequence.nil _ _⟩

/-- An alternative is within the join (`ExitSpec.join`, the class entries
covering each). -/
theorem fp_covers_join_left (a b : Closed) : Footprint.Covers a.fp (a.join b).fp :=
  fun e he => fp_join_covers a b e (List.mem_append_left _ he)

theorem fp_covers_join_right (a b : Closed) : Footprint.Covers b.fp (a.join b).fp :=
  fun e he => fp_join_covers a b e (List.mem_append_right _ he)

/-- **The sequence's throw includes its prefix** (Seq-Eff on the exceptional
exit): where the first command returns within `a` and the second then throws
within `x`, the sequence's exceptional bound is at least `a.join x`. -/
theorem seq_into {A B : ClassSummary} {a x : Closed} (ha : A.normal = some a) (hx : B.exceptional = some x) :
    ∃ c, (seq A B).exceptional = some c ∧ Footprint.Covers (a.join x).fp c.fp := by
  cases hA : A.exceptional with
  | none => exact ⟨a.join x, by simp [seq, ha, hx, hA, alt, andThen], fun e he => ⟨e, he, rfl, Change.le_refl _⟩⟩
  | some y =>
    refine ⟨y.join (a.join x), by simp [seq, ha, hx, hA, alt, andThen], fp_covers_join_right _ _⟩

/-! ## The projection is an upper bound -/

private theorem le_join (a b : Closed) : a.le (a.join b) = true ∧ b.le (a.join b) = true := by
  have h := Closed.join_le a b (a.join b)
  rw [Closed.le_refl] at h
  exact Bool.and_eq_true_iff.mp h.symm

private theorem ofFootprint_frame (c : Closed) (t : Bool) :
    ({ Effect.ofFootprint c with onThrow := t } : Effect).frame = c.fp := by
  simp [Effect.frame, Effect.ofFootprint, Effect.receiverEntries]

private theorem ofFootprint_exc (c : Closed) (t : Bool) (n : Nat) :
    (({ Effect.ofFootprint c with onThrow := t } : Effect).summary n).exceptional.frame =
      if t then c.fp else topEffect := by
  cases t <;> simp [Effect.summary, ofFootprint_frame]

/-- **The projection includes the summary** (proved): at each exit the
summary reaches, its bound's frame is within the frame the projection's
per-exit contract states there (`Closed.post_mono`). -/
theorem project_covers (S : ClassSummary) (bounded : Bool) (n : Nat) (c : Completion) {k : Closed}
    (hk : S.get c = some k) {ρ : Env} {h h' : Heap} (hp : Post k.fp ρ h h') :
    Post (((S.project bounded).summary n).get c).frame ρ h h' := by
  rcases S with ⟨N, X⟩
  cases c with
  | normal =>
    simp only [Exits.get] at hk
    subst hk
    simpa [project, Exits.get, Effect.summary, ofFootprint_frame] using hp
  | exceptional =>
    simp only [Exits.get] at hk
    subst hk
    have hframe := ofFootprint_exc (N.getD .empty) (project ⟨N, some k⟩ bounded).onThrow n
    simp only [project] at hframe ⊢
    rw [show ∀ e : Effect, (e.summary n).get .exceptional = (e.summary n).exceptional from fun _ => rfl, hframe]
    by_cases ht : (bounded && N.getD .empty != Closed.top && k.le (N.getD .empty)) = true
    · simp only [ht, if_true]
      simp only [Bool.and_eq_true] at ht
      exact Closed.post_mono ht.2 hp
    · simp only [Bool.not_eq_true] at ht
      simp only [ht]
      exact Closed.post_mono (Closed.le_top k) hp

/-- **The embedding projects back** (proved): today's effect of a closed
frame `c` and throw bound `t` is the projection of its summary, but for a
throw bound at `top`, which states nothing. -/
theorem project_ofFormat (c : Closed) (t : Bool) :
    (ofFormat c t).project = { Effect.ofFootprint c with onThrow := t && c != Closed.top } := by
  have hb : Footprint.boundBelow [] c.fp = c := Footprint.boundBelow_fp [] c
  have ht : Footprint.boundBelow [] topEffect = Closed.top := Footprint.boundBelow_fp [] Closed.top
  cases t <;> simp [ofFormat, ofEffect, project, Effect.summary, ofFootprint_frame, hb, ht, Closed.le_refl]
  · intro h; rw [Closed.top_le]; simpa using h

/-! ## Entailment between summaries -/

/-- One exit's bound within another's: an unreached exit within any, a
reached one within a reached one by `Closed.le`. -/
def exitWithin : Option Closed → Option Closed → Bool
  | none, _ => true
  | some a, some b => a.le b
  | some _, none => false

/-- **A summary entails another** exit by exit (`exitWithin`). -/
def within (A B : ClassSummary) : Bool := exitWithin A.normal B.normal && exitWithin A.exceptional B.exceptional

/-- **Entailment is weakening at each exit** (proved; `ExitSpec.Weakens`): at
each exit the first summary reaches, the second reaches it too, and the
first's exit specification weakens to the second's from any entry. -/
theorem within_weakens {A B : ClassSummary} (h : A.within B = true) (arena : AssertionArena) (P : TolerantFrames.Assertion)
    (c : Completion) {k : Closed} (hk : A.get c = some k) :
    ∃ k', B.get c = some k' ∧ ExitSpec.Weakens arena P ⟨k.fp, []⟩ ⟨k'.fp, []⟩ := by
  have he : exitWithin (A.get c) (B.get c) = true := by
    simp only [within, Bool.and_eq_true] at h
    cases c
    · exact h.1
    · exact h.2
  rw [hk] at he
  cases hb : B.get c with
  | none => rw [hb] at he; cases he
  | some k' =>
    rw [hb] at he
    refine ⟨k', rfl, fun s _ hs => ⟨⟨hs.1.1, Closed.post_mono he hs.1.2⟩, fun _ hF => nomatch hF⟩⟩

theorem exitWithin_alt_left (a b : Option Closed) : exitWithin a (alt a b) = true := by
  cases a <;> cases b <;> simp [exitWithin, alt, (le_join _ _).1, Closed.le_refl]

theorem exitWithin_alt_right (a b : Option Closed) : exitWithin b (alt a b) = true := by
  cases a <;> cases b <;> simp [exitWithin, alt, (le_join _ _).2, Closed.le_refl]

/-- **Each alternative entails the choice** (proved). -/
theorem within_choice (A B : ClassSummary) : A.within (A.choice B) = true ∧ B.within (A.choice B) = true := by
  simp [within, choice, exitWithin_alt_left, exitWithin_alt_right]

end ClassSummary

end Verification.SourceExtraction
