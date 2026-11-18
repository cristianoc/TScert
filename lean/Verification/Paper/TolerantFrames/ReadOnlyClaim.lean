import Verification.Paper.TolerantFrames.ReadOnlyExec
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

/-- **A client frame** (the draft, "The framed claim"): the component `C` of
a family, the types crossings are read at, the client obligation `Θ`, what
the checks give at each step, and the histories an entry starts from. -/
structure ClientFrame (τ : Type) where
  fam : NumberedFamily
  C : Nat
  view : ViewOver τ
  Θ : Protocol (fam.family.at C)
  chk : Heap → Tm → Heap → Tm → CheckData (fam.family.at C) view.view
  start : (k : Nat) → WorldT k → Heap → Tm → Ghost (fam.family.at C) → Prop
  /-- Every state has a history an entry may start from: the claim reads no
  entry as one without a history. -/
  start_total : ∀ k (W : WorldT k) h t, ∃ g, start k W h t g

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
