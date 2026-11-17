import Verification.Semantics.FootprintJoin
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
  (`Footprint.boundBelow`), the positions the walk knows to hold a fresh spine
  discharged (Fresh-Eff); a write's is the grade its typed-write rule
  accepts; a `throw` returns never and leaves the heap it starts in;
- **sequence on both exits** (`ClassSummary.seq`, Seq-Eff at two exits): a
  throw includes the effect of the whole prefix before it
  (`ClassSummary.seq_into`);
- **choice** (`ClassSummary.choice`): exit by exit, the join of the
  alternatives;
- **handler** (`ClassSummary.handle`): a caught throw continues at the
  handler, whose exits are the statement's;
- **closure** (`ClassSummary.close`): class entries are rigid, so a frame
  joining every operation's normal frame is closed under another traversal of
  any loop; every throw's prefix is within it.

Class entries rebase to themselves (`rebaseAll_fp`), so composition at the
class level is the join of the closed bounds (`ClassSummary.fp_join_covers`).
The soundness of each rule for a command's runs, and the command summary a
sound summary gives, are stated over the paper's command summaries in
`Paper/TolerantFrames/Bridges/ExitProposals.lean`.

**The walk is an untrusted proposal heuristic.** The walk has no run
semantics of the source: the walk of the literal's body at the effect it is
offered at, with the footprint check of each step
(`SinglePass.footprintCheck`) and the records' admission
(`SinglePass.recordsAdmit`), decides whether the proposal holds. Today's
effect format receives it through one projection (`ClassSummary.project`),
an upper bound of the summary at each exit (`ClassSummary.project_covers`). -/
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
holding spines allocated after the call's entry (Fresh-Eff): each exit's
frame of the instance's specification schema (`Effect.schema`, whose frames
read no arity), read in the closed language below the entry mark
(`Footprint.boundBelow`); the normal exit unreached where the result is
empty. A class summary states frames alone: the schema's postconditions
are not read. -/
def ofEffect (e : Effect) (P : List Nat) (returns : Bool := true) : ClassSummary :=
  ⟨if returns then some (Footprint.boundBelow P e.schema.normal.frame) else none,
    some (Footprint.boundBelow P e.schema.exceptional.frame)⟩

/-- **Whether a frame may change a value location of the entry heap**: the
value component of its closed bound below the entry
(`Footprint.boundBelow`, no position discharged). -/
def changesValues (Φ : Footprint) : Bool := (Footprint.boundBelow [] Φ).value != .keep

/-- An operation that returns within a closed bound and never throws. -/
def ofClosed (c : Closed) : ClassSummary := ⟨some c, none⟩

/-- A `throw`: it never returns, and throws leaving the heap it starts in. -/
def raise : ClassSummary := ⟨none, some .empty⟩

/-- An async body's summary: a throw rejects the promise the call returned,
a normal return of the call; the call never throws, its exceptional exit
unreached. -/
def settle (S : ClassSummary) : ClassSummary := ⟨alt S.normal S.exceptional, none⟩

/-- Whether the projection bounds a throw by the normal frame: where asked
(`bounded`), the normal bound is not `⊤`, and the exceptional bound, where
reached, is within it. -/
def throwBounded (S : ClassSummary) (bounded : Bool := true) : Bool :=
  bounded && S.normal.getD .empty != Closed.top && (match S.exceptional with
    | none => true
    | some x => x.le (S.normal.getD .empty))

/-- **A summary in the claims document's format**: the closed footprint and
the throw flag the claims document writes for a function (`footprint`,
`onThrow`): the normal exit's bound, the throw bounded where `bounded` asks
for it and the exceptional exit's bound is within the normal one's, or
unreached (`throwBounded`). -/
def format (S : ClassSummary) (bounded : Bool := true) : Closed × Bool :=
  (S.normal.getD .empty, S.throwBounded bounded)

/-- **The projection into today's effect format**: the effect of a closed
frame and a throw bound (`Effect.ofClosed`) whose closed frame
is the normal exit's bound, its throw bounded where `bounded` asks for it
and the exceptional exit's bound is within the normal one's, or unreached.
Its schema is an upper bound of the summary's (`project_entails`), at each
exit the summary reaches (`project_covers`).

**What it loses**, each a weakening at one exit:

- an unreached normal exit: the projection returns within the empty frame;
- an unreached exceptional exit: the projection throws within the normal
  frame where its throw is bounded, else within `⊤`;
- an exceptional bound not within the normal one: the projection throws
  within `⊤`;
- every exceptional bound where `bounded` is false or the normal bound is
  `top`: a throw bound at `top` states nothing (the exceptional frame `⊤`
  either way), so `top` is projected with none, the form `Effect.schema`
  elaborates.

Where the exceptional bound is reached and within the normal one, and the
normal bound is not `top`, it is the least effect of today's format whose
schema is above the summary's. -/
def project (S : ClassSummary) (bounded : Bool := true) : Effect :=
  Effect.ofClosed (S.format bounded).1 (S.format bounded).2

/-- **Today's format embedded in a summary**: the per-exit contract of the
effect of closed frame `c` and throw bound `t`, at the class level
(`ofEffect`). -/
def ofFormat (c : Closed) (t : Bool) : ClassSummary := ofEffect (Effect.ofClosed c t) []

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

private theorem covers_refl (c : Closed) : Footprint.Covers c.fp c.fp := fun e he => ⟨e, he, rfl, Change.le_refl _⟩

/-- **An exit reached after the first command returns includes its prefix**
(Seq-Eff at either exit of the second command): where the first command
returns within `a` and the second then completes by `k` within `y`, the
sequence's bound at `k` is at least `a.join y`. -/
theorem seq_after {A B : ClassSummary} {a y : Closed} (k : Completion) (ha : A.normal = some a)
    (hy : B.get k = some y) : ∃ c, (seq A B).get k = some c ∧ Footprint.Covers (a.join y).fp c.fp := by
  cases k with
  | normal => exact ⟨a.join y, by simp_all [seq, Exits.get, andThen], covers_refl _⟩
  | exceptional => exact seq_into ha hy

/-- **An exit reached after a caught throw includes the throw's prefix**
(`handle`): where the protected command throws within `x` and the handler
then completes by `k` within `d`, the statement's bound at `k` is at least
`x.join d`. -/
theorem handle_after {A D : ClassSummary} {x d : Closed} (k : Completion) (hx : A.exceptional = some x)
    (hd : D.get k = some d) : ∃ c, (handle A D).get k = some c ∧ Footprint.Covers (x.join d).fp c.fp := by
  cases k with
  | normal =>
    cases hA : A.normal with
    | none => exact ⟨x.join d, by simp_all [handle, Exits.get, alt, andThen], covers_refl _⟩
    | some y => exact ⟨y.join (x.join d), by simp_all [handle, Exits.get, alt, andThen], fp_covers_join_right _ _⟩
  | exceptional => exact ⟨x.join d, by simp_all [handle, Exits.get, andThen], covers_refl _⟩

/-! ## The projection is an upper bound -/

theorem le_join (a b : Closed) : a.le (a.join b) = true ∧ b.le (a.join b) = true := by
  have h := Closed.join_le a b (a.join b)
  rw [Closed.le_refl] at h
  exact Bool.and_eq_true_iff.mp h.symm

private theorem ofFootprint_exc (c : Closed) (t : Bool) (n : Nat) :
    ((Effect.ofClosed c t).summary n).exceptional.frame =
      if t then c.fp else topEffect := by
  cases t <;> rfl

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
    simpa [project, format, Exits.get, Effect.summary, Exits.atArity, Exits.map, ExitSchema.instantiate,
      Effect.ofClosed, Exits.ofClosed] using hp
  | exceptional =>
    simp only [Exits.get] at hk
    subst hk
    have hframe := ofFootprint_exc (N.getD .empty) (throwBounded ⟨N, some k⟩ bounded) n
    simp only [project, format, throwBounded] at hframe ⊢
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
    (ofFormat c t).project = Effect.ofClosed c (t && c != Closed.top) := by
  have hb : Footprint.boundBelow [] c.fp = c := Footprint.boundBelow_fp [] c
  have ht : Footprint.boundBelow [] topEffect = Closed.top := Footprint.boundBelow_fp [] Closed.top
  cases t <;> simp [ofFormat, ofEffect, project, format, throwBounded, Effect.ofClosed_schema, Exits.ofClosed, hb, ht,
    Closed.le_refl]
  rw [Closed.top_le]
  cases h : c == Closed.top <;> simp_all

/-! ## The summary's schema, and the projection above it -/

/-- **The schema of a summary**: at each exit its bound's class entries and
no postcondition; the empty frame at an exit no run reaches, which holds of
all of its runs (`sound_spec`). -/
def schema (S : ClassSummary) : Exits ExitSchema :=
  ⟨⟨(S.normal.getD .empty).fp, []⟩, ⟨(S.exceptional.getD .empty).fp, []⟩⟩

/-- **A schema entails one stating no postcondition** where each exit's
frame includes the first's (`Exits.Entails`). -/
theorem entails_of_frames {x y : Exits ExitSchema} (hy : ∀ c, (y.get c).ensures = [])
    (hf : ∀ c ρ h h', Post (x.get c).frame ρ h h' → Post (y.get c).frame ρ h h') : x.Entails y := by
  intro c r args s s' v hp
  refine ⟨⟨hp.1.1, ?_⟩, ?_⟩
  · rw [Exits.atArity_frame]
    exact hf c _ _ _ (Exits.exitPost_frame hp)
  · intro F hF
    have he : ((y.atArity args.length).get c).ensures =
        (y.get c).ensures.map (instantiateFormula (y.callInstantiation args.length)) := by
      cases c <;> rfl
    rw [he, hy c] at hF
    nomatch hF

/-- **The projection is an upper bound of the summary in the effect order**
(proved; `Exits.Entails`, the order `Effect.Covers` reads schemas in): at
both exits, at every call, the summary's schema entails the projection's.
What it weakens is listed at `project`. -/
theorem project_entails (S : ClassSummary) (bounded : Bool) : S.schema.Entails (S.project bounded).schema := by
  rcases S with ⟨N, X⟩
  have hs : (project ⟨N, X⟩ bounded).schema = ⟨⟨(N.getD .empty).fp, []⟩,
      if throwBounded ⟨N, X⟩ bounded then ⟨(N.getD .empty).fp, []⟩ else ⟨topEffect, []⟩⟩ :=
    Effect.ofClosed_schema _ _
  rw [hs]
  refine entails_of_frames (fun c => ?_) (fun c ρ h h' hp => ?_)
  · cases c
    · rfl
    · show (if _ then _ else _ : ExitSchema).ensures = []
      split <;> rfl
  · cases c with
    | normal => exact hp
    | exceptional =>
      show Post (if _ then _ else _ : ExitSchema).frame ρ h h'
      split
      · next ht =>
        simp only [throwBounded, Bool.and_eq_true] at ht
        have hle : (X.getD .empty).le (N.getD .empty) = true := by
          cases X with
          | none => exact Closed.empty_le _
          | some k => simpa using ht.2
        exact Closed.post_mono hle hp
      · exact Closed.post_mono (Closed.le_top _) hp

/-! ## Entailment between summaries -/

/-- One exit's bound within another's: an unreached exit within any, a
reached one within a reached one by `Closed.le`. -/
def exitWithin : Option Closed → Option Closed → Bool
  | none, _ => true
  | some a, some b => a.le b
  | some _, none => false

/-- **A summary entails another** exit by exit (`exitWithin`). -/
def within (A B : ClassSummary) : Bool := exitWithin A.normal B.normal && exitWithin A.exceptional B.exceptional


theorem exitWithin_alt_left (a b : Option Closed) : exitWithin a (alt a b) = true := by
  cases a <;> cases b <;> simp [exitWithin, alt, (le_join _ _).1, Closed.le_refl]

theorem exitWithin_alt_right (a b : Option Closed) : exitWithin b (alt a b) = true := by
  cases a <;> cases b <;> simp [exitWithin, alt, (le_join _ _).2, Closed.le_refl]

/-- **Each alternative entails the choice** (proved). -/
theorem within_choice (A B : ClassSummary) : A.within (A.choice B) = true ∧ B.within (A.choice B) = true := by
  simp [within, choice, exitWithin_alt_left, exitWithin_alt_right]

/-- **The walk's closure keeps a summary sound**: it only widens the
exceptional exit (`within S S.close`). -/
theorem exitWithin_refl (a : Option Closed) : exitWithin a a = true := by
  cases a <;> simp [exitWithin, Closed.le_refl]

theorem within_close (S : ClassSummary) : S.within S.close = true := by
  simp only [within, close, Bool.and_eq_true]
  exact ⟨exitWithin_refl _, exitWithin_alt_left _ _⟩

/-! ## Loops -/

/-- **The prefix summary of a loop**: zero iterations, or iterations each
within the body's normal bound; class entries are rigid, so one join bounds
any number. -/
def iterated (B : ClassSummary) : Option Closed := alt (some .empty) B.normal

theorem iterated_step (B : ClassSummary) : exitWithin (andThen (iterated B) B.normal) (iterated B) = true := by
  rcases hb : B.normal with _ | b
  · simp [iterated, hb, andThen]
    rfl
  · simp only [iterated, hb, alt, andThen, exitWithin]
    rw [Closed.join_le, Closed.join_le]
    simp [(le_join Closed.empty b).1, (le_join Closed.empty b).2]

end ClassSummary

end Verification.SourceExtraction