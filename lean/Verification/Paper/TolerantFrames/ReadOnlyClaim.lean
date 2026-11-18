import Verification.Paper.TolerantFrames.ReadOnlyProvenance
import Verification.Semantics.SafeUnder

/-! # Read-only handles: the client obligation a framed unit is accepted under

The note "Read-only frames" (`docs/drafts/readonly-frames-note/note.tex`,
Assumption "Clients") and the draft "Read-only handles"
(`docs/drafts/readonly-handles.md`, "Trust", "The framed claim"). A unit
verified through the read-only frame rule is accepted for the executions
in which code outside its component `C` keeps the client obligation `Θ`
(`Row`) at each of its steps. This module states that obligation over the
calculus's steps, with the history it reads:

- **A client frame** (`ClientFrame`): the family of components, its sites
  numbered; the component `C`; the type view of crossings; the client
  obligation `Θ`; what the checks give at each step (`chk`: the sites and
  keys of what it allocates, its crossings); and the histories an entry may
  start from (`start`), at least one at every state (`start_total`).
- **The obligation at a step** (`ClientFrame.Keeps`): a step whose active
  frame runs no code of `C` with as many calls of `C` active after it as
  before (`stepKind … = .outside`) changes the storage the row protects at
  the history `g` within `Θ` at its part (`RowAt`, `Row` read at the heaps,
  the world and the history, `row_iff`). A step of `C`'s code is not
  constrained.
- **The history along an execution** (`ClientFrame.next`): the history of
  the paper's executions (`Ghost.stepAt`, `Ghost.next` at the
  configurations' heaps and terms, `next_conf`).
- **The calls the claim is about** (`ClientFrame.Call`): the frame's
  well-formed entries (`enters`, read at the call alone), and four named
  premises (`ClientFrame.Entry`) beside the obligation: code provenance (`Provenance`: every code
  the term and the heap hold that carries a tag of `C` is one of `C`'s own
  codes, `codes`; Assumption "Clients", outside code enters `C` only
  through its interface), the call discipline (`Discipline`: the term
  well formed, the heap free of runs, the configurations of `XStep.of_wf`),
  and two of well-formed entries: outside code is lowered source
  (`Source`, `LoweredSrc`) and the values are closed (`ClosedAt`).
  Every step keeps them (`Entry.step`, by `step_prov`, `step_wf` and
  `step_scoped`), so every state of an execution from an entry meets them
  (`Entry.steps`).

The entry of a unit is a call from outside code: the top segment runs no
component (`none`). -/
namespace Verification.TolerantFrames.ReadOnly
open Verification Footprints

/-- **A family whose sites are numbered**: `Family` at `Site := Nat`. -/
structure NumberedFamily where
  nested : Nat → Nat → Prop
  refl : ∀ c, nested c c
  trans : ∀ a b c, nested a b → nested b c → nested a c
  laminar : ∀ a b, nested a b ∨ nested b a ∨ ∀ c, ¬ (nested c a ∧ nested c b)
  siteOf : Nat → ComponentTag
  mark : Nat → Nat → Mark

/-- The family a numbered family is. -/
def NumberedFamily.family (N : NumberedFamily) : Family :=
  ⟨Nat, N.nested, N.refl, N.trans, N.laminar, N.siteOf, N.mark⟩

/-- **A type view over the types `τ`**: `TypeView` at `Ty := τ`. -/
structure ViewOver (τ : Type) where
  child : τ → Label → τ
  RO : τ → Prop
  ro_child : ∀ t a, RO t → RO (child t a)

/-- The type view a view over `τ` is. -/
def ViewOver.view {τ : Type} (V : ViewOver τ) : TypeView := ⟨τ, V.child, V.RO, V.ro_child⟩

/-- **The client obligation at a step, read at its data**: every location
the row protects at the history `g`, holding `v` at the heap `h`, holds
`v'` at `h'` with the change from `v` to `v'` within `Θ` at its part, its
kind read at the world `W`. -/
def RowAt {P : Package} (Θ : Protocol P) {k : Nat} (W : WorldT k) (g : Ghost P) (h h' : Heap) : Prop :=
  ∀ l v, RowProtects g l → h[l]? = some v →
    ∃ v', h'[l]? = some v' ∧ (Θ ⟨g.site l, kindAt W l, g.key l⟩).Holds h.length v v'

/-- `Row` is `RowAt` at the states' heaps, the first world and history. -/
theorem row_iff {P : Package} {Θ : Protocol P} {st st' : St P} :
    Row Θ st st' ↔ RowAt Θ st.s.W st.g st.s.h st'.s.h := Iff.rfl

/-- **The call discipline at an entry** (named premise of the framed
claim): the term is well formed and the heap free of runs (`Conf.WF`), so
every step obeys `Disc` (`disc_of_wf`). -/
def Discipline (h : Heap) (t : Tm) : Prop := wf t = true ∧ HeapFree h

/-- **A client frame** (the draft, "The framed claim"): the component `C` of
a family, the types crossings are read at, the client obligation `Θ`, what
the checks give at each step, and the histories an entry starts from. -/
structure ClientFrame (τ : Type) where
  fam : NumberedFamily
  C : Nat
  /-- `C`'s own lowered code: the unit's program, the closures it creates,
  the component's members. -/
  codes : Code → Prop
  view : ViewOver τ
  Θ : Protocol (fam.family.at C)
  chk : Heap → Tm → Heap → Tm → CheckData (fam.family.at C) view.view
  start : (k : Nat) → WorldT k → Heap → Tm → Ghost (fam.family.at C) → Prop
  /-- Every state has a history an entry may start from: the claim reads no
  entry as one without a history. -/
  start_total : ∀ k (W : WorldT k) h t, ∃ g, start k W h t g
  /-- **The calls the claim is about** (named premise, well-formed
  entries): the states at which a call of the unit's code may start, such
  as those whose slots of the module's functions hold the module's
  closures. No step need keep it: it is read at the call alone. -/
  enters : Heap → Tm → Prop

namespace ClientFrame
variable {τ : Type} (fr : ClientFrame τ)

/-- The family of the frame. -/
abbrev F : Family := fr.fam.family

/-- **The obligation at a step** (Assumption "Clients"): a step of code
outside `C`, keeping the calls of `C` active, changes the storage the row
protects within `Θ`. -/
def Keeps (g : Ghost (fr.F.at fr.C)) (k : Nat) (W : WorldT k) (h : Heap) (t : Tm) (h' : Heap) (t' : Tm) :
    Prop :=
  stepKind fr.F fr.C none t t' = .outside → RowAt fr.Θ W g h h'

/-- **The history after a step**: the paper's (`Ghost.stepAt`), at what the
checks give of the step. -/
noncomputable def next (g : Ghost (fr.F.at fr.C)) (h : Heap) (t : Tm) (h' : Heap) (t' : Tm) :
    Ghost (fr.F.at fr.C) :=
  Ghost.stepAt fr.F fr.C none (fr.chk h t h' t') h t h' t' g

open Classical in
/-- **A code at a tag meets the frame**: a code carrying a tag of `C` is one
of `C`'s own codes. -/
noncomputable def ok : Code → ComponentTag → Bool := fun code c => decide (fr.F.Runs c fr.C → fr.codes code)

/-- **Code provenance at an entry** (named premise, Assumption "Clients"):
every code of the term and of the heap carrying a tag of `C` is `C`'s own. -/
def Provenance (h : Heap) (t : Tm) : Prop := prov fr.ok t = true ∧ HeapProv fr.ok h

/-- **Outside code is lowered source at an entry** (named premise,
well-formed entries): every code of outside code the term and the heap
hold, of its closures and runs, is lowered source (`LoweredSrc`). -/
def Source (h : Heap) (t : Tm) : Prop :=
  prov (srcOk (fr.F.ofC fr.C)) t = true ∧ HeapProv (srcOk (fr.F.ofC fr.C)) h

/-- **The values at an entry are closed** (named premise, well-formed
entries): the term and every value the heap holds have no free
variable. -/
def ClosedAt (h : Heap) (t : Tm) : Prop := Scoped 0 t ∧ ∀ v ∈ h, Scoped 0 v

/-- **An entry the framed claim is about**: code provenance, the call
discipline, outside code lowered source and closed values. -/
def Entry (h : Heap) (t : Tm) : Prop := fr.Provenance h t ∧ Discipline h t ∧ fr.Source h t ∧ ClosedAt h t

/-- **A call the claim is about**: the premises every step keeps
(`Entry`) and the frame's well-formed entries (`enters`). -/
def Call (h : Heap) (t : Tm) : Prop := fr.Entry h t ∧ fr.enters h t

/-- **Every step keeps an entry's premises** (proved): code provenance and
outside code lowered source by `step_prov`, the call discipline by
`step_wf`, closed values by `step_scoped`. -/
theorem Entry.step {h h' : Heap} {t t' : Tm} (he : fr.Entry h t) (hs : Step h t h' t') : fr.Entry h' t' :=
  let hp := step_prov hs he.1.1 he.1.2
  let hw := step_wf hs he.2.1.1 he.2.1.2
  let hl := step_prov hs he.2.2.1.1 he.2.2.1.2
  let hc := step_scoped hs he.2.2.2.1 he.2.2.2.2
  ⟨⟨hp.1, hp.2⟩, ⟨hw.1, hw.2.1⟩, ⟨hl.1, hl.2⟩, ⟨hc.1, hc.2⟩⟩

/-- **Every state of an execution from an entry meets its premises** (proved). -/
theorem Entry.steps {j : Nat} {h h' : Heap} {t t' : Tm} (he : fr.Entry h t)
    (hs : HeapObservations.Steps j h t h' t') : fr.Entry h' t' := by
  induction hs with
  | refl => exact he
  | next st _ ih => exact ih (Entry.step fr he st)

/-- **A configuration at an entry's premises is well formed** (proved). -/
theorem Entry.wf {x : Conf} (he : fr.Entry x.s.h x.t) : x.WF := he.2.1

/-- **Provenance excludes a closure tagged with `C` whose code is not `C`'s**
(proved): a term holding such a closure meets no provenance. -/
theorem Entry.foreign {fs : List (PropKey × Nat)} {ar : Nat} {E : List Tm}
    {K : List (ControlFlow.Continuation × Option ControlFlow.Target)} {st : Nat} {caps : List Tm} {kd : Invoke}
    {rest : Bool} {c : Nat} {i : Nat} (hc : fr.F.nested c fr.C) (hn : ¬ fr.codes (E, K)) :
    prov fr.ok (.objAt fs (.graph ar E K st caps kd rest (some c)) i) = false := by
  have : fr.ok (E, K) (some c) = false := by
    simp only [ok, decide_eq_false_iff_not]
    exact fun h => hn (h ⟨c, rfl, hc⟩)
  simp [prov, this]

/-- The checks at configurations. -/
def chkConf : Conf → Conf → CheckData (fr.F.at fr.C) fr.view.view := fun x y => fr.chk x.s.h x.t y.s.h y.t

/-- **The history is the paper's** (proved, by definition): at
configurations, `next` is `Ghost.next` at the checks the frame gives. -/
theorem next_conf (g : Ghost (fr.F.at fr.C)) (x y : Conf) :
    fr.next g x.s.h x.t y.s.h y.t = Ghost.next fr.F fr.C none fr.chkConf x y g := rfl

/-- **The obligation is the paper's** (proved, by definition): at
configurations, `Keeps` is `Row` at an outside step, the hypothesis
`StepHyp` makes of a step of outside code. -/
theorem keeps_conf (g g' : Ghost (fr.F.at fr.C)) (x y : Conf) :
    fr.Keeps g x.s.n x.s.W x.s.h x.t y.s.h y.t ↔
      (kind fr.F fr.C none x y = .outside → Row fr.Θ (lift fr.F fr.C none x g) (lift fr.F fr.C none y g')) :=
  Iff.rfl

/-- **The obligation is met** from every history the frame starts from: an
invariant of the history and the term holds there, and every step from a
state meeting it keeps the obligation and the invariant. -/
def Met : Prop :=
  ∃ I, HeapObservations.KeepsOn fr.Keeps fr.next I ∧ ∀ k W h t g, fr.start k W h t g → I g h t

/-- **Outside code certified to keep `Θ`** (proved): where an invariant `I`
of the history and the term is kept by every step and every outside step
from it keeps the row, at every world, every step from it keeps the
obligation. -/
theorem keepsOn_of {I : Ghost (fr.F.at fr.C) → Heap → Tm → Prop}
    (hI : ∀ g h t h' t', I g h t → Step h t h' t' → I (fr.next g h t h' t') h' t')
    (hrow : ∀ g h t h' t', I g h t → Step h t h' t' → stepKind fr.F fr.C none t t' = .outside →
      ∀ (k : Nat) (W : WorldT k), RowAt fr.Θ W g h h') :
    HeapObservations.KeepsOn fr.Keeps fr.next I :=
  fun g h t h' t' hi st => ⟨fun k W hk => hrow g h t h' t' hi st hk k W, hI g h t h' t' hi st⟩

/-- **No outside code** (proved): where an invariant `I` is kept by every
step and the active frame of every term meeting it runs `C`'s code, no step
from it is a step of outside code, and every step keeps the obligation. -/
theorem keepsOn_inside {I : Ghost (fr.F.at fr.C) → Heap → Tm → Prop}
    (hI : ∀ g h t h' t', I g h t → Step h t h' t' → I (fr.next g h t h' t') h' t')
    (hin : ∀ g h t, I g h t → ¬ OutsideAt fr.F fr.C none t) :
    HeapObservations.KeepsOn fr.Keeps fr.next I :=
  fr.keepsOn_of hI fun g h t _ t' hi _ hk => by
    have : OutsideAt fr.F fr.C none t ∧ depthC fr.F fr.C none t' = depthC fr.F fr.C none t := by
      unfold stepKind at hk
      by_cases h₁ : OutsideAt fr.F fr.C none t ∧ depthC fr.F fr.C none t' = depthC fr.F fr.C none t
      · exact h₁
      · rw [if_neg h₁] at hk
        split at hk <;> (try split at hk) <;> cases hk
    exact absurd this.1 (hin g h t hi)

end ClientFrame
end Verification.TolerantFrames.ReadOnly
