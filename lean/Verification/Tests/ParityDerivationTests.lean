import Verification.Semantics.ParityDerivations

/-! Research tests of the parity derivations, kept while the derivations
are built and replaced by pipeline cases once the pass produces them: each
encodes a derivation of the note "Tolerant frames"
(`docs/drafts/tolerant-frames-note/note.tex`) as a `RawDerivation` and checks
it with `checkScoped`, which checks the arena and the scopes first: what it
accepts holds by `checkScoped_sound`.

- The regional certificates: classes, spine separation, rigid spines.
- The atom axioms (Sep), (Init), (View), (Every), (Rigid), each refused off
  its shape.
- A rigid path image under a box (Frame⁺ with a certified transport).
- The note's Example "A write through a typed array": four facts framed
  across `{views: grow}`, and the fifth, about another typed array's
  element, refused.
- P4's straight-line bound and P18's two-field guard, their framing derived
  by (Rigid) and the tolerant frame theorem; the fields' stable contracts
  (the guards' and the paths' rigidity) are premises, since no rule of the
  checker introduces them.
- Write-In, Write-End and Push from their exact posts.
- The arithmetic of `index[c >> 8]`, with `0 ≤ c < 1114112` and
  `index.length = 4352`, and of `table[x & 255]` with `table.length = 256`
  (the note, §6, Shr and Mask).
- The modal plumbing of law (d), Frame and guard elimination on P18's
  guard, with the framed `L` case as a premise (`P18Plumbing`), and unit
  checks of substitution, literal witnesses and ∃ elimination. -/
namespace Verification.Parity.Tests
open Verification Footprints HeapKnowledge

private def isOk {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

private def errorOf {α : Type} : Except String α → String
  | .ok _ => ""
  | .error e => e

/-- The empty arena: the arithmetic derivations name no assertion. -/
private def empty : AssertionArena := ⟨#[]⟩

/-- A linear certificate found by the search, to be checked. -/
private def proveOr (Fs : List (Linear.Fact StepVar)) (f : Linear.Form StepVar) (d : Int) :
    List (Linear.Step StepVar) :=
  (Linear.prove Fs f d).getD []

/-- A linear consequence of the facts `Fs` by the certificate the search
finds, each concluded term named by a fact. -/
private def linRaw (Fs : List (Linear.Fact StepVar)) (f : Linear.Form StepVar) (d : Int) (raw : RawDerivation) :
    RawDerivation :=
  .linear Fs [] (proveOr Fs f d) raw .truth

/-- The conjunction of a list of linear premises, each a premise. -/
private def premisesRaw : Nat → RawDerivation
  | 0 => .truth
  | n + 1 => .andIntro .assumption (premisesRaw n)

/-! ## The validated boundary

An arena whose node 0 is `1 ∧ 1` refers forward, so node 0 denotes `false`.
The unvalidated check builds a derivation of it from two `true`s; the
validated one refuses the arena. -/

namespace Invalid
private def bad : AssertionArena := ⟨#[.and ⟨1⟩ ⟨1⟩, .truth]⟩
private def raw : RawDerivation := .atAndIntro ⟨1⟩ ⟨1⟩ .atTruth .atTruth

#guard isOk (checkDerivation bad [] (.at .after ⟨0⟩) raw)
#guard errorOf (checkScoped bad ⟨0, 0⟩ [] (.at .after ⟨0⟩) raw) = "the arena is not valid"
end Invalid

/-! ## Regional certificates -/

namespace Regional
private def r (n : Nat) : AssertionRef := ⟨n⟩
private def arena : AssertionArena := ⟨#[
  .atom (.dense (.var 0) (Term.value 1)),       -- 0 dense(xs, n): xs an ordinary array
  .separated (.var 0) (.var 2),                 -- 1 xs # ys
  .and (r 0) (r 1),                             -- 2 K
  .atom (.equal ⟨1, ["items"]⟩ (.path (.var 0))), -- 3
  .box topEffect (r 3),                         -- 4
  .existsValue (r 4)]⟩                          -- 5 rigid(p.items), p at slot 0

#guard arena.check
-- `xs.spine` is an array spine, disjoint from the view spines.
#guard (DisjointEvidence.classes (.arrayAt (r 0)) .intrinsic).check arena (r 2) (.spine 0 []) (.cls .views)
-- Without a conjunct naming `ys` as an array, `ys.spine` has no class.
#guard !(DisjointEvidence.classes (.arrayAt (r 0)) .intrinsic).check arena (r 2) (.spine 2 []) (.cls .views)
#guard (DisjointEvidence.classes (.arrayAt (r 1)) .intrinsic).check arena (r 2) (.spine 2 []) (.cls .views)
-- The two spines a separation names, in either order.
#guard (DisjointEvidence.spines (r 1)).check arena (r 2) (.spine 0 []) (.spine 2 [])
#guard (DisjointEvidence.swap (.spines (r 1))).check arena (r 2) (.spine 2 []) (.spine 0 [])
-- A spine's cells are values, disjoint from every spine.
#guard (DisjointEvidence.classes .intrinsic .intrinsic).check arena (r 2) (.pathCells 0 []) (.cls .spines)
-- `{p.items.spine: any}` is rigid where `p.items` is; `{p.items[cells]: any}` is not.
#guard (RigidityEvidence.stable [r 5]).check arena (r 5) [(.spine 0 ["items"], .any), (.cls .values, .any)]
#guard !(RigidityEvidence.stable [r 5]).check arena (r 5) [(.pathCells 0 ["items"], .any)]
-- Inclusion by class: the cells of `xs` at `any` are within `{values: any}`.
#guard (InclusionEvidence.byClass [.intrinsic]).check arena (r 2) [(.pathCells 0 [], .any)] [(.cls .values, .any)]
end Regional

/-! ## The atom axioms

(Sep), (Init), (View), (Every) and (Rigid) of the note's Proposition
"Axioms of the atoms", each at its displayed shape. -/

namespace Axioms
private def r (n : Nat) : AssertionRef := ⟨n⟩
private def grow : Footprint := TolerantFrames.growEffect.fp
private def arena : AssertionArena := ⟨#[
  .atom (.linear (.le [(Term.value 1, 1), (Term.length 0, -1)] 0)),      -- 0 n ≤ |x|
  .separated (.var 0) (.var 2),                                         -- 1 x # y
  .box [(.cls .values, .any), (.spine 2 [], .any)] (r 0),               -- 2 (Sep)
  .box [(.cls .values, .init)] (r 0),                                   -- 3 (Init)
  .atom (.linear (.le [(Term.value 1, 1), (Term.now .view 3 [], -1)] 0)), -- 4 n ≤ view(w)
  .box topEffect (r 4),                                                 -- 5 (View)
  .apart (.var 2) (.var 0),                                             -- 6 apart(y, x)
  .atom (.every (.var 0) (Term.value 1) [.atom (.le [(.elem, -1)] (-1))]), -- 7 every(x, n, v > 0)
  .box [(.spine 2 [], .any), (.pathCells 2 [], .any)] (r 7),            -- 8 (Every)
  .atom (.equal ⟨5, ["f"]⟩ (.path (.var 0))),                           -- 9
  .box topEffect (r 9),                                                 -- 10
  .existsValue (r 10),                                                  -- 11 rigid(p.f), p at slot 4
  .atom (.linear (lowerFact 2 0)),                                      -- 12 n ≤ |y|, y fresh at slot 0
  .box grow (r 12),                                                     -- 13
  .atom (.linear (.le [(Term.value 1, 1), (Term.now .length 4 ["f"], -1)] 0)), -- 14 n ≤ |p.f|
  .box grow (r 14),                                                     -- 15 (Rigid) with (Grow)
  .atom (.linear (.le [(Term.value 1, 1), (Term.length 2, -1)] 0)),      -- 16 n ≤ |y|
  .box [(.cls .values, .any), (.spine 2 [], .any)] (r 16)]⟩             -- 17

#guard arena.check
private def sc : Scope := ⟨5, 5⟩

#guard isOk (checkScoped arena sc [.at .before (r 1), .at .before (r 0)] (.at .before (r 2))
  (.sep 0 2 (r 1) .assumption .assumption))
-- (Sep) frames a fact about `|x|`, not one about the changed `|y|`.
#guard errorOf (checkScoped arena sc [.at .before (r 1), .at .before (r 16)] (.at .before (r 17))
  (.sep 0 2 (r 1) .assumption .assumption)) = "sep: the atom reads more than |x| and variables"
#guard isOk (checkScoped arena sc [.at .before (r 0)] (.at .before (r 3)) (.init .assumption))
#guard isOk (checkScoped arena sc [.at .before (r 4)] (.at .before (r 5)) (.view .assumption))
-- A length is no view: (View) does not frame `n ≤ |x|` under `⊤`.
#guard errorOf (checkScoped arena sc [.at .before (r 0)] (.at .before (r 3)) (.view .assumption)) =
  "view: the atom reads more than variables and typed-array lengths"
#guard isOk (checkScoped arena sc [.at .before (r 6), .at .before (r 7)] (.at .before (r 8))
  (.everyFrame 2 (r 6) .assumption .assumption))
-- (Every) needs `apart`; a spine separation leaves the cells shared.
#guard errorOf (checkScoped arena sc [.at .before (r 1), .at .before (r 7)] (.at .before (r 8))
  (.everyFrame 2 (r 1) .assumption .assumption)) = "everyFrame: goal is no box or the separation is no apartness"
#guard isOk (checkScoped arena sc [.at .before (r 11), .at .before (r 14)] (.at .before (r 15))
  (.rigidSubst ⟨4, ["f"]⟩ 5 (r 11) (r 12) (r 14) (r 13) (.grow 2 0 (r 12) .assumption) .assumption .assumption))
-- Without the path's rigidity the substitution is refused.
#guard errorOf (checkScoped arena sc [.at .before (r 13), .at .before (r 14)] (.at .before (r 15))
  (.rigidSubst ⟨4, ["f"]⟩ 5 (r 13) (r 12) (r 14) (r 13) (.grow 2 0 (r 12) .assumption) .assumption .assumption)) =
  "rigidSubst: no rigidity of the path"
end Axioms

/-! ## A path image under a box

Frame⁺ carries `□_{grow}(n ≤ |y|)` across a step whose exit reads `y` as the
field `p.f`: the path image is read inside the box, so the transport
certifies it rigid at the exit. -/

namespace RigidImage
private def r (n : Nat) : AssertionRef := ⟨n⟩
private def grow : Footprint := TolerantFrames.growEffect.fp
private def arena : AssertionArena := ⟨#[
  .atom (.linear (lowerFact 1 2)),                                         -- 0 n ≤ |y|
  .box grow (r 0),                                                         -- 1
  .atom (.linear (.le [(Term.value 1, 1), (Term.now .length 0 ["f"], -1)] 0)), -- 2 n ≤ |p.f|
  .box grow (r 2),                                                         -- 3
  .atom (.equal ⟨1, ["f"]⟩ (.path (.var 0))),                              -- 4
  .box topEffect (r 4),                                                    -- 5
  .existsValue (r 5),                                                      -- 6 rigid(p.f)
  .truth]⟩                                                                 -- 7

#guard arena.check
private def images : Array Witness := #[.path (.var 0), .path (.var 1), .path ⟨0, ["f"]⟩]
private def θ : Substitution := { images := images, stable := [2] }
private def Γ : List Formula :=
  [.at .before (r 1), .transition grow, .transport { images := images }, .at .after (r 6)]

#guard isOk (checkScoped arena ⟨3, 3⟩ Γ (.at .after (r 3))
  (.framePlus (.closed TolerantFrames.growEffect) grow (r 1) (r 0) (r 7) θ .atTruth .assumption .assumption
    (.transportRigid [(2, r 6)] .assumption (.andIntro .assumption .truth))))
-- Without the certificate the field image is refused inside the box.
#guard errorOf (checkScoped arena ⟨3, 3⟩ Γ (.at .after (r 3))
  (.framePlus (.closed TolerantFrames.growEffect) grow (r 1) (r 0) (r 7) { images := images } .atTruth .assumption
    .assumption .assumption)) = "framePlus: not the transported box"
end RigidImage

/-! ## The note's Example "A write through a typed array"

Before `b[0] = 7`, of effect `{views: grow}`: `3 ≤ |xs|`,
`every(xs, t, v > 0)`, `o.n ≐ 1`, `2 ≤ view(c)` and `c[j] ≐ 5` (`t` and `j`
variables standing for `3` and `1`). The first four hold after the write by
Frame, each from the tolerant frame theorem at its support or (View); the
last has no derivation: its support keeps `c`'s view spine, which the
effect lets grow. -/

namespace ViewWrite
private def r (n : Nat) : AssertionRef := ⟨n⟩
private def Φ : Footprint := [(.cls .views, .grow)]
private def arena : AssertionArena := ⟨#[
  .atom (.linear (.le [(Term.length 0, -1)] (-3))),                         -- 0 3 ≤ |xs|
  .atom (.every (.var 0) (Term.value 4) [.atom (.le [(.elem, -1)] (-1))]),  -- 1 every(xs, t, v > 0)
  .atom (.equal ⟨1, ["n"]⟩ (.literal (.num (bitsOfNat 1)))),                -- 2 o.n ≐ 1
  .atom (.linear (.le [(Term.now .view 3 [], -1)] (-2))),                   -- 3 2 ≤ view(c)
  .atom (.element (.var 3) (Term.value 5) (.literal (.num (bitsOfNat 5)))), -- 4 c[j] ≐ 5
  .box Φ (r 0), .box Φ (r 1), .box Φ (r 2), .box Φ (r 3), .box Φ (r 4)]⟩    -- 5–9

#guard arena.check
private def θ : Substitution := Substitution.ident 6
private def Γ : List Formula :=
  [.at .before (r 0), .at .before (r 1), .at .before (r 2), .at .before (r 3), .at .before (r 4),
    .transition Φ, .transport θ]

/-- Frame of the box `b` of the atom `a`, the box derived by `box`. -/
private def frameOf (a b : Nat) (box : RawDerivation) : RawDerivation :=
  .frame Φ (r b) (r a) θ box .assumption .assumption

private def box0 : RawDerivation :=
  .tolerantFrame [(.spine 0 [], .keep)] .lengths ⟨[(0, 0, .classes (.arrayAt (r 0)) .intrinsic)]⟩ .truth (r 0) (r 0)
    .assumption .assumption .assumption
private def box1 : RawDerivation :=
  .tolerantFrame [(.spine 0 [], .keep), (.pathCells 0 [], .keep)] .everyCells
    ⟨[(0, 0, .classes (.arrayAt (r 1)) .intrinsic), (1, 0, .classes .intrinsic .intrinsic)]⟩ .truth (r 1) (r 1)
    .assumption .assumption .assumption
private def box2 : RawDerivation :=
  .tolerantFrame [(.path 1 [] (.str "n"), .keep)] .field ⟨[(0, 0, .classes (.fieldAt (r 2)) .intrinsic)]⟩ .truth
    (r 2) (r 2) .assumption .assumption .assumption

private def goal : Formula := conj [.at .after (r 0), .at .after (r 1), .at .after (r 2), .at .after (r 3)]

#guard isOk (checkScoped arena ⟨6, 6⟩ Γ goal
  (.andIntro (frameOf 0 5 box0) (.andIntro (frameOf 1 6 box1) (.andIntro (frameOf 2 7 box2)
    (.andIntro (frameOf 3 8 (.view .assumption)) .truth)))))

-- `c[j] ≐ 5` has its support at `c`'s view spine and cells at `keep`; the
-- effect lets the view spine grow, and no certificate separates it.
#guard errorOf (checkScoped arena ⟨6, 6⟩ Γ (.at .after (r 4)) (frameOf 4 9
  (.tolerantFrame [(.spine 3 [], .keep), (.pathCells 3 [], .keep)] .viewElement ⟨[]⟩ .truth (r 4) (r 4)
    .assumption .assumption .assumption))) = "tolerantFrame: the effect does not respect the support"
end ViewWrite

/-! ## P4, the straight-line bound

`|a.flags| = |a.starts|` survives a call of effect
`{values: any, o.spine: any}` where `a.flags # o` and `a.starts # o`, the
two paths rigid (`astra/parity-plan-out.md`, P4): (Rigid) twice opens the
paths as fresh variables `y1`, `y2`, the tolerant frame theorem frames each
length fact at the support `{y1.spine: keep, y2.spine: keep}` (values and
`o.spine` disjoint from both spines), and the separations of variables are
invariant. After the call, `i + 1 < |a.flags|` gives `i + 1 < |a.starts|`.
The rigidity of the two fields comes from their stable contracts, which no
rule of this checker introduces: they are premises. -/

namespace P4
private def r (n : Nat) : AssertionRef := ⟨n⟩
private def fl : Path := ⟨0, ["flags"]⟩
private def st : Path := ⟨0, ["starts"]⟩
private def Φ : Footprint := [(.cls .values, .any), (.spine 1 [], .any)]
private def Φ1 : Footprint := Footprint.rename (· + 1) Φ
private def Φ2 : Footprint := Footprint.rename (· + 1) Φ1
private def len (p : Path) : Term := p.term .length
private def le (a b : Term) : Linear.Fact Term := .le [(a, 1), (b, -1)] 0
private def below : Linear.Fact Term := .le [(Term.value 2, 1), (len fl, -1)] (-2)

private def arena : AssertionArena := ⟨#[
  -- a2: y2 at 0, y1 at 1, a at 2, o at 3
  .atom (.linear (le (Term.length 1) (Term.length 0))),   -- 0 |y1| ≤ |y2|
  .atom (.linear (le (Term.length 0) (Term.length 1))),   -- 1 |y2| ≤ |y1|
  .separated (.var 1) (.var 3),                           -- 2 y1 # o
  .separated (.var 0) (.var 3),                           -- 3 y2 # o
  .and (r 0) (r 1), .and (r 2) (r 3), .and (r 4) (r 5),   -- 4 5 6 (a2)
  .box Φ2 (r 0), .box Φ2 (r 1), .box Φ2 (r 4), .box Φ2 (r 5), .box Φ2 (r 6),  -- 7–11
  -- a1: y1 at 0, a at 1, o at 2
  .atom (.linear (le (Term.length 0) (Term.now .length 1 ["starts"]))),  -- 12
  .atom (.linear (le (Term.now .length 1 ["starts"]) (Term.length 0))),  -- 13
  .separated (.var 0) (.var 2),                           -- 14
  .separated ⟨1, ["starts"]⟩ (.var 2),                    -- 15
  .and (r 12) (r 13), .and (r 14) (r 15), .and (r 16) (r 17),  -- 16 17 18 (core1)
  .atom (.equal ⟨2, ["starts"]⟩ (.path (.var 0))), .box topEffect (r 19), .existsValue (r 20),  -- 19 20 21 rigid(a.starts)
  .and (r 18) (r 21),                                     -- 22 a1
  .box Φ1 (r 18), .box Φ1 (r 21), .box Φ1 (r 22),          -- 23 24 25
  -- c: a at 0, o at 1, i at 2
  .atom (.linear (le (len fl) (len st))), .atom (.linear (le (len st) (len fl))),  -- 26 27
  .separated fl (.var 1), .separated st (.var 1),          -- 28 29
  .and (r 26) (r 27), .and (r 28) (r 29), .and (r 30) (r 31),  -- 30 31 32
  .atom (.equal ⟨1, ["starts"]⟩ (.path (.var 0))), .box topEffect (r 33), .existsValue (r 34),  -- 33 34 35
  .and (r 32) (r 35),                                     -- 36 c
  .box Φ (r 36),                                          -- 37
  .atom (.equal ⟨1, ["flags"]⟩ (.path (.var 0))), .box topEffect (r 38), .existsValue (r 39),  -- 38 39 40 rigid(a.flags)
  .atom (.linear below),                                  -- 41 i + 1 < |a.flags|
  .and (r 4) (r 2)]⟩                                      -- 42 the lengths and y1 # o only

#guard arena.check

/-- The support of a length fact over `y1`, `y2`, respected by `Φ2`. -/
private def frameLength (K : Nat) (seps : Bool) (dA : RawDerivation) : RawDerivation :=
  .tolerantFrame [(.spine 1 [], .keep), (.spine 0 [], .keep)] .lengths
    ⟨[(0, 0, .classes (.arrayAt (r 0)) .intrinsic), (0, 1, .spines (r 2)),
      (1, 0, .classes (.arrayAt (r 0)) .intrinsic), (1, 1, .spines (r (if seps then 3 else 2)))]⟩
    .truth (r K) (r K) .assumption .assumption dA

/-- `a2 ⊢ □_Φ2 a2`. -/
private def e2 : RawDerivation :=
  .boxAndIntro Φ2 (r 6) (r 4) (r 5) (r 9) (r 10)
    (.boxAndIntro Φ2 (r 4) (r 0) (r 1) (r 7) (r 8)
      (frameLength 6 true (.atAndLeft (r 4) (r 1) (.atAndLeft (r 6) (r 5) .assumption)))
      (frameLength 6 true (.atAndRight (r 4) (r 0) (.atAndLeft (r 6) (r 5) .assumption))))
    (.tolerantFrame [] .invariant ⟨[]⟩ .truth (r 6) (r 6) .assumption .assumption (.atAndRight (r 6) (r 4) .assumption))

/-- `a1 ⊢ □_Φ1 a1`: (Rigid) at `a.starts` for `y2`. -/
private def e1 : RawDerivation :=
  .boxAndIntro Φ1 (r 22) (r 18) (r 21) (r 23) (r 24)
    (.rigidSubst ⟨1, ["starts"]⟩ 3 (r 21) (r 6) (r 18) (r 11) e2 (.atAndRight (r 22) (r 18) .assumption)
      (.atAndLeft (r 22) (r 21) .assumption))
    (.tolerantFrame [] .invariant ⟨[]⟩ .truth (r 22) (r 22) .assumption .assumption
      (.atAndRight (r 22) (r 18) .assumption))

private def Γ : List Formula :=
  [.at .before (r 26), .at .before (r 27), .at .before (r 28), .at .before (r 29), .at .before (r 35),
    .at .before (r 40), .transition Φ, .transport (Substitution.ident 3), .at .after (r 41)]

/-- `c` before the call. -/
private def cBefore : RawDerivation :=
  .atAndIntro (r 32) (r 35)
    (.atAndIntro (r 30) (r 31) (.atAndIntro (r 26) (r 27) .assumption .assumption)
      (.atAndIntro (r 28) (r 29) .assumption .assumption))
    .assumption

private def goal : Formula := .linear (.le [(.after (Term.value 2), 1), (.after (len st), -1)] (-2))
private def lenFacts : List (Linear.Fact StepVar) := [tagFact .after below, tagFact .after (le (len fl) (len st))]

private def raw : RawDerivation :=
  .cut (.at .after (r 36))
    (.frame Φ (r 37) (r 36) (Substitution.ident 3)
      (.rigidSubst fl 2 (r 40) (r 22) (r 36) (r 25) e1 .assumption cBefore) .assumption .assumption)
    (linRaw lenFacts [(.after (Term.value 2), 1), (.after (len st), -1)] (-2)
      (.andIntro (.atomToLinear .after (r 41) below .assumption)
        (.andIntro (.atomToLinear .after (r 26) (le (len fl) (len st))
          (.atAndLeft (r 30) (r 27) (.atAndLeft (r 32) (r 31) (.atAndLeft (r 36) (r 35) .assumption)))) .truth)))

#guard isOk (checkScoped arena ⟨3, 3⟩ Γ goal raw)

-- Without `y2 # o` the call's write of `o`'s spine may be `y2`'s:
-- the length fact's support is not respected.
#guard errorOf (checkScoped arena ⟨4, 4⟩ [.at .after (r 42)] (.at .after (r 7))
  (frameLength 42 true (.atAndLeft (r 4) (r 1) (.atAndLeft (r 42) (r 2) .assumption)))) =
  "tolerantFrame: the effect does not respect the support"
end P4

/-! ## P18, the two-field guard, its framing derived

`F = g₁ ∨ g₂ ∨ (L ∧ rigid(p.items.insideExtras) ∧ rigid(p.widths))` with
`g₁ = □_⊤(p.items ≐ null)`, `g₂ = □_⊤(p.items.insideExtras ≐ null)` and
`L = |p.items.insideExtras| = |p.widths|`, across a call of effect
`{values: any}` (spines kept): law (d) twice, and in the third case (Rigid)
twice and the tolerant frame theorem at the two spines' `keep`
(`astra/parity-plan-out.md`, P18). The guards and the two rigidities are
the stable contracts' facts, which no rule of this checker introduces: the
premise `F` states them. -/

namespace P18
private def r (n : Nat) : AssertionRef := ⟨n⟩
private def ex : Path := ⟨0, ["items", "insideExtras"]⟩
private def wd : Path := ⟨0, ["widths"]⟩
private def items : Path := ⟨0, ["items"]⟩
private def Φ : Footprint := (⟨.any, .keep, .keep⟩ : Footprints.Closed).fp
private def len (p : Path) : Term := p.term .length
private def le (a b : Term) : Linear.Fact Term := .le [(a, 1), (b, -1)] 0
private def below : Linear.Fact Term := .le [(Term.value 1, 1), (len wd, -1)] (-1)
private def object : CallEffects.ElemPred := { obj := true }

private def arena : AssertionArena := ⟨#[
  -- a2: y2 (widths) at 0, y1 (extras) at 1, p at 2, i at 3
  .atom (.linear (le (Term.length 1) (Term.length 0))), .atom (.linear (le (Term.length 0) (Term.length 1))),  -- 0 1
  .and (r 0) (r 1),                                                    -- 2
  .box Φ (r 0), .box Φ (r 1), .box Φ (r 2),                            -- 3 4 5
  -- a1: y1 at 0, p at 1, i at 2
  .atom (.linear (le (Term.length 0) (Term.now .length 1 ["widths"]))),  -- 6
  .atom (.linear (le (Term.now .length 1 ["widths"]) (Term.length 0))),  -- 7
  .and (r 6) (r 7),                                                    -- 8
  .atom (.equal ⟨2, ["widths"]⟩ (.path (.var 0))), .box topEffect (r 9), .existsValue (r 10),  -- 9 10 11
  .and (r 8) (r 11),                                                   -- 12
  .box Φ (r 8), .box Φ (r 11), .box Φ (r 12),                          -- 13 14 15
  -- c: p at 0, i at 1
  .atom (.linear (le (len ex) (len wd))), .atom (.linear (le (len wd) (len ex))),  -- 16 17
  .and (r 16) (r 17),                                                  -- 18 L
  .atom (.equal ⟨1, ["widths"]⟩ (.path (.var 0))), .box topEffect (r 19), .existsValue (r 20),  -- 19 20 21
  .and (r 18) (r 21),                                                  -- 22
  .atom (.equal ⟨1, ["items", "insideExtras"]⟩ (.path (.var 0))), .box topEffect (r 23), .existsValue (r 24),  -- 23 24 25
  .and (r 22) (r 25),                                                  -- 26 the third case
  .box Φ (r 22),                                                       -- 27
  .atom (.equal items (.literal .nul)), .box topEffect (r 28),         -- 28 29 g₁
  .atom (.equal ex (.literal .nul)), .box topEffect (r 30),            -- 30 31 g₂
  .guarded (r 31) (r 26), .guarded (r 29) (r 32),                      -- 32 33 F
  .box Φ (r 26), .guarded (r 31) (r 34), .box Φ (r 32), .guarded (r 29) (r 36), .box Φ (r 33),  -- 34–38
  .box Φ (r 25),                                                       -- 39
  .atom (.contents items object), .atom (.contents ex object),         -- 40 41
  .atom (.linear below)]⟩                                              -- 42 i < |p.widths|

#guard arena.check

private def frameLength (dA : RawDerivation) : RawDerivation :=
  .tolerantFrame [(.spine 1 [], .keep), (.spine 0 [], .keep)] .lengths
    ⟨[(0, 0, .classes (.arrayAt (r 0)) .intrinsic), (1, 0, .classes (.arrayAt (r 0)) .intrinsic)]⟩
    .truth (r 2) (r 2) .assumption .assumption dA

private def e2 : RawDerivation :=
  .boxAndIntro Φ (r 2) (r 0) (r 1) (r 3) (r 4) (frameLength (.atAndLeft (r 2) (r 1) .assumption))
    (frameLength (.atAndRight (r 2) (r 0) .assumption))

private def e1 : RawDerivation :=
  .boxAndIntro Φ (r 12) (r 8) (r 11) (r 13) (r 14)
    (.rigidSubst ⟨1, ["widths"]⟩ 3 (r 11) (r 2) (r 8) (r 5) e2 (.atAndRight (r 12) (r 8) .assumption)
      (.atAndLeft (r 12) (r 11) .assumption))
    (.tolerantFrame [] .invariant ⟨[]⟩ .truth (r 12) (r 12) .assumption .assumption
      (.atAndRight (r 12) (r 8) .assumption))

/-- `□_Φ` of the third case, in its branch; `rex` the rigidity it opens `ex` by. -/
private def boxThird (rex : Nat) : RawDerivation :=
  .boxAndIntro Φ (r 26) (r 22) (r 25) (r 27) (r 39)
    (.rigidSubst ex 2 (r rex) (r 12) (r 22) (r 15) e1 (.atAndRight (r 26) (r 22) .assumption)
      (.atAndLeft (r 26) (r 25) .assumption))
    (.tolerantFrame [] .invariant ⟨[]⟩ .truth (r 26) (r 26) .assumption .assumption
      (.atAndRight (r 26) (r 22) .assumption))

/-- `□_Φ F` before the call, by cases and law (d) twice. -/
private def boxF (rex : Nat) : RawDerivation :=
  .guardCases .before (r 33) (r 29) (r 32) .assumption
    (.boxGuard Φ (r 37) (r 29) (r 36) (r 32) (r 33) (.guardLeft (r 29) (r 36) .assumption))
    (.boxGuard Φ (r 37) (r 29) (r 36) (r 32) (r 33)
      (.guardRight (r 29) (r 36)
        (.guardCases .before (r 32) (r 31) (r 26) .assumption
          (.boxGuard Φ (r 35) (r 31) (r 34) (r 26) (r 32) (.guardLeft (r 31) (r 34) .assumption))
          (.boxGuard Φ (r 35) (r 31) (r 34) (r 26) (r 32) (.guardRight (r 31) (r 34) (boxThird rex))))))

private def Γ : List Formula :=
  [.at .before (r 33), .transition Φ, .transport (Substitution.ident 2),
    .at .after (r 40), .at .after (r 41), .at .after (r 42)]

private def goal : Formula := .linear (.le [(.after (Term.value 1), 1), (.after (len ex), -1)] (-1))
private def lenFacts : List (Linear.Fact StepVar) := [tagFact .after below, tagFact .after (le (len wd) (len ex))]

private def afterF : RawDerivation :=
  .guardCases .after (r 33) (r 29) (r 32) .assumption
    (.atomClash .after items .nul object (r 28) (r 40) (.boxElim topEffect (r 29) .assumption) .assumption)
    (.guardCases .after (r 32) (r 31) (r 26) .assumption
      (.atomClash .after ex .nul object (r 30) (r 41) (.boxElim topEffect (r 31) .assumption) .assumption)
      (linRaw lenFacts [(.after (Term.value 1), 1), (.after (len ex), -1)] (-1)
        (.andIntro (.atomToLinear .after (r 42) below .assumption)
          (.andIntro (.atomToLinear .after (r 17) (le (len wd) (len ex))
            (.atAndRight (r 18) (r 16) (.atAndLeft (r 22) (r 21) (.atAndLeft (r 26) (r 25) .assumption)))) .truth))))

private def raw (rex : Nat) : RawDerivation :=
  .cut (.at .after (r 33)) (.frame Φ (r 38) (r 33) (Substitution.ident 2) (boxF rex) .assumption .assumption) afterF

#guard isOk (checkScoped arena ⟨2, 2⟩ Γ goal (raw 25))
-- The fact through `p.items.insideExtras` needs that path's rigidity: the
-- rigidity of `p.widths` does not open it.
#guard errorOf (checkScoped arena ⟨2, 2⟩ Γ goal (raw 21)) = "rigidSubst: no rigidity of the path"
end P18

/-! ## Exact postconditions of writes -/

namespace Writes
#guard isOk (checkScoped empty ⟨2, 2⟩ [.operation (.lengthsKept 0 1), .defined (lenB 0)] (lengthStep 0 1 0)
  (.writeIn 0 1 .assumption .assumption))
#guard isOk (checkScoped empty ⟨2, 2⟩ [.operation (.boundedWrite 0 1 1), atEndFacts 0 1] (lengthStep 0 1 1)
  (.writeEnd 0 1 1 .assumption .assumption))
-- Write-End's growth needs the index at the length.
#guard errorOf (checkScoped empty ⟨2, 2⟩ [.operation (.boundedWrite 0 1 1)] (lengthStep 0 1 1)
  (.writeEnd 0 1 1 .assumption .assumption)) = "assumption: not a premise"
#guard isOk (checkScoped empty ⟨2, 2⟩ [.operation (.push 0 1 [.literal (.num (bitsOfNat 7))]), .defined (lenB 0),
    .linear (.le [(lenB 0, 1)] (maxArrayLength - 1))] (lengthStep 0 1 1)
  (.pushPost 0 1 [.literal (.num (bitsOfNat 7))] .assumption .assumption .assumption))
-- A post reading an entry slot past the entry's scope is refused.
#guard errorOf (checkScoped empty ⟨1, 2⟩ [.operation (.boundedWrite 0 1 1)] (lengthStep 0 1 1)
  (.writeEnd 0 1 1 .assumption .assumption)) = "a formula reads a slot outside its scope"
#guard errorOf (checkScoped empty ⟨1, 2⟩ [.operation (.push 0 1 [.path (.var 3)]), .defined (lenB 0),
    .linear (.le [(lenB 0, 1)] (maxArrayLength - 1))] (lengthStep 0 1 1)
  (.pushPost 0 1 [.path (.var 3)] .assumption .assumption .assumption)) = "a formula reads a slot outside its scope"
end Writes

/-! ## `index[c >> 8]` -/

/-- The derivation of the `i`-th conjunct of `conj l` from one of `conj l`. -/
private def proj : List Formula → Nat → RawDerivation → RawDerivation
  | _ :: t, 0, d => .andLeft (conj t) d
  | F :: t, i + 1, d => proj t i (.andRight F d)
  | [], _, d => d

namespace Shift
private def c : Path := .var 1
private def j : Path := .var 0
private def k : Path := .var 3
private def index : StepVar := .after (Term.length 2)
private def eight : UInt64 := bitsOfNat 8

/-- After `j = c >> 8`: the operation, `0 ≤ c`, `c ≤ 1114111`, `|index| = 4352`. -/
private def Γ : List Formula :=
  [.operation (.arith .shr (.path c) (.literal (.num eight)) j),
    .linear (.le [(av c, -1)] 0), .linear (.le [(av c, 1)] 1114111),
    .linear (.le [(index, 1)] 4352), .linear (.le [(index, -1)] (-4352))]

/-- `0 ≤ j < |index|`. -/
private def goal : Formula :=
  conj [.linear (.le [(av j, -1)] 0), .linear (.le [(av j, 1), (index, -1)] (-1))]

private def F : Linear.Form Term := [(vt c, 1)]
private def shr : List Formula :=
  [safeFact j, lin (.le [(vt j, -1)] 0), lin (.le ((vt j, 2 ^ 8) :: F.scale (-1)) 0),
    lin (.le ((vt j, -(2 ^ 8)) :: F) (2 ^ 8 - 1 - 0))]

private def boundFacts : List (Linear.Fact StepVar) :=
  [tagFact .after (.le ((vt j, 2 ^ 8) :: F.scale (-1)) 0), .le [(av c, 1)] 1114111, .le [(index, -1)] (-4352)]

/-- `0 ≤ c ≤ 2^31 − 1` from the premises. -/
private def small : RawDerivation :=
  .andIntro .assumption (.andIntro (linRaw [.le [(av c, 1)] 1114111] [(av c, 1)] (2 ^ 31 - 1 - 0) (premisesRaw 1)) .truth)

/-- The shift by `amount`, then the bound. -/
private def rawWith (amount : Operand) (dk : RawDerivation) (bound : Int) : RawDerivation :=
  .cut (smallFacts F 0) small
    (.cut (conj shr) (.shiftRight (.var c) amount j .assumption (.definedOfLinear (.le [(av c, 1)] 1114111) .assumption)
        dk .assumption)
      (.andIntro (proj shr 1 .assumption)
        (.andIntro
          (linRaw boundFacts [(av j, 1), (index, -1)] bound
            (.andIntro (proj shr 2 .assumption) (.andIntro .assumption (.andIntro .assumption .truth))))
          .truth)))

private def raw : RawDerivation := rawWith (.literal eight) .truth (-1)

#guard isOk (checkScoped empty ⟨0, 4⟩ Γ goal raw)

-- A bound one tighter than the facts give, `j ≤ |index| − 2`, is refused:
-- no certificate concludes it.
private def goalTight : Formula :=
  conj [.linear (.le [(av j, -1)] 0), .linear (.le [(av j, 1), (index, -1)] (-2))]

#guard errorOf (checkScoped empty ⟨0, 4⟩ Γ goalTight (rawWith (.literal eight) .truth (-2))) =
  "linear: the certificate does not conclude the goal"

-- The shift amount a slot proved equal to 8, as the pass's `knownConstant`
-- gives it.
private def Γk : List Formula :=
  [.operation (.arith .shr (.path c) (.path k) j),
    .linear (.le [(av c, -1)] 0), .linear (.le [(av c, 1)] 1114111),
    .linear (.le [(index, 1)] 4352), .linear (.le [(index, -1)] (-4352)),
    lin (.le [(vt k, 1)] 8), lin (.le [(vt k, -1)] (-8))]

#guard isOk (checkScoped empty ⟨0, 4⟩ Γk goal (rawWith (.const k 8) (premisesRaw 2) (-1)))
-- Without the evidence the amount is no constant.
#guard errorOf (checkScoped empty ⟨0, 4⟩ Γk goal (rawWith (.var k) (.definedOfLinear (.le [(av k, 1)] 8) .assumption) (-1))) =
  "shiftRight: the shift is no constant safe integer"

end Shift

/-! ## `table[x & 255]` -/

namespace Mask
private def x : Path := .var 1
private def y : Path := .var 0
private def table : StepVar := .after (Term.length 2)
private def mask255 : UInt64 := bitsOfNat 255

private def Γ : List Formula :=
  [.operation (.arith .bitAnd (.path x) (.literal (.num mask255)) y),
    .linear (.le [(av x, -1)] 0), .linear (.le [(av x, 1)] (2 ^ 31 - 1)),
    .linear (.le [(table, -1)] (-256))]

private def goal : Formula :=
  conj [.linear (.le [(av y, -1)] 0), .linear (.le [(av y, 1), (table, -1)] (-1))]

private def F : Linear.Form Term := [(vt x, 1)]
private def msk : List Formula :=
  [safeFact y, lin (.le [(vt y, -1)] 0), lin (.le [(vt y, 1)] 255), lin (.le ((vt y, 1) :: F.scale (-1)) 0)]

private def boundFacts : List (Linear.Fact StepVar) := [.le [(av y, 1)] 255, .le [(table, -1)] (-256)]

private def raw : RawDerivation :=
  .cut (conj msk)
    (.mask (.var x) (.literal mask255) y .assumption (.definedOfLinear (.le [(av x, -1)] 0) .assumption) .truth
      (premisesRaw 2))
    (.andIntro (proj msk 1 .assumption)
      (.andIntro
        (linRaw boundFacts [(av y, 1), (table, -1)] (-1)
          (.andIntro (proj msk 2 .assumption) (.andIntro .assumption .truth)))
        .truth))

#guard isOk (checkScoped empty ⟨0, 3⟩ Γ goal raw)

-- Without the operand's upper bound the range premise is missing.
private def Γnarrow : List Formula := Γ.take 2 ++ Γ.drop 3

#guard errorOf (checkScoped empty ⟨0, 3⟩ Γnarrow goal raw) = "assumption: not a premise"

end Mask

/-! ## P18: the two-field guard -/

namespace P18Plumbing
private def items : Path := ⟨0, ["items"]⟩
private def extras : Path := ⟨0, ["items", "insideExtras"]⟩
private def widths : Path := ⟨0, ["widths"]⟩
private def i : Term := Term.value 1

/-- `step`'s effect `{values: any}`, spines kept. -/
private def Φ : Footprint := (⟨.any, .keep, .keep⟩ : Footprints.Closed).fp

private def lenEq₁ : Linear.Fact Term := .le [(extras.term .length, 1), (widths.term .length, -1)] 0
private def lenEq₂ : Linear.Fact Term := .le [(extras.term .length, -1), (widths.term .length, 1)] 0
private def below : Linear.Fact Term := .le [(i, 1), (widths.term .length, -1)] (-1)
private def object : CallEffects.ElemPred := { obj := true }

private def ref (n : Nat) : AssertionRef := ⟨n⟩

/-- The arena: `g₁ = □_⊤ (p.items ≐ null)`, `g₂ = □_⊤ (p.items.insideExtras ≐ null)`,
`L = |p.items.insideExtras| = |p.widths|`, `F = g₁ ∨ (g₂ ∨ L)`. -/
private def arena : AssertionArena := ⟨#[
  .atom (.equal items (.literal .nul)),        -- 0
  .box topEffect (ref 0),                      -- 1  g₁
  .atom (.equal extras (.literal .nul)),       -- 2
  .box topEffect (ref 2),                      -- 3  g₂
  .atom (.linear lenEq₁),                      -- 4
  .atom (.linear lenEq₂),                      -- 5
  .and (ref 4) (ref 5),                        -- 6  L
  .guarded (ref 3) (ref 6),                    -- 7  g₂ ∨ L
  .guarded (ref 1) (ref 7),                    -- 8  F
  .box Φ (ref 6),                              -- 9  □_Φ L
  .guarded (ref 3) (ref 9),                    -- 10 g₂ ∨ □_Φ L
  .box Φ (ref 7),                              -- 11 □_Φ (g₂ ∨ L)
  .guarded (ref 1) (ref 11),                   -- 12 g₁ ∨ □_Φ (g₂ ∨ L)
  .box Φ (ref 8),                              -- 13 □_Φ F
  .atom (.contents items object),              -- 14 p.items is an object
  .atom (.contents extras object),             -- 15 p.items.insideExtras is an object
  .atom (.linear below),                       -- 16 i < |p.widths|
  .atom (.equal ⟨1, ["items"]⟩ (.path (.var 0))), -- 17 p.items ≐ v, under the binder
  .box topEffect (ref 17),                     -- 18
  .existsValue (ref 18),                       -- 19 rigid(p.items)
  .box Φ (ref 1),                              -- 20 □_Φ g₁
  .box [(.cells 0, .any)] (ref 0),             -- 21 □_{p[elements]: any} (p.items ≐ null)
  .guarded (ref 1) (ref 10)]⟩                  -- 22 g₁ ∨ g₂ ∨ □_Φ L

#guard arena.check

/-- The identity transport: the call binds no name. -/
private def θ : Substitution := { images := #[.path (.var 0), .path (.var 1)] }

/-- Before the call `g₁ ∨ g₂ ∨ □_Φ L`: the guard with its `L` case framed;
the call's transition; after it, both null tests failed and
`i < |p.widths|`. -/
private def Γ : List Formula :=
  [.at .before (ref 22), .transition Φ, .transport θ,
    .at .after (ref 14), .at .after (ref 15), .at .after (ref 16)]

/-- `i < |p.items.insideExtras|` after the call. -/
private def goal : Formula := .linear (.le [(.after i, 1), (.after (extras.term .length), -1)] (-1))

/-- `□_Φ F` before the call, by law (d) twice. -/
private def boxF : RawDerivation :=
  .guardCases .before (ref 22) (ref 1) (ref 10) .assumption
    (.boxGuard Φ (ref 12) (ref 1) (ref 11) (ref 7) (ref 8) (.guardLeft (ref 1) (ref 11) .assumption))
    (.boxGuard Φ (ref 12) (ref 1) (ref 11) (ref 7) (ref 8)
      (.guardRight (ref 1) (ref 11) (.boxGuard Φ (ref 10) (ref 3) (ref 9) (ref 6) (ref 7) .assumption)))

private def lenFacts : List (Linear.Fact StepVar) :=
  [tagFact .after lenEq₂, tagFact .after below]

/-- After the call: the guards are eliminated by the failed null tests. -/
private def afterF : RawDerivation :=
  .guardCases .after (ref 8) (ref 1) (ref 7) .assumption
    (.atomClash .after items .nul object (ref 0) (ref 14) (.boxElim topEffect (ref 1) .assumption) .assumption)
    (.guardCases .after (ref 7) (ref 3) (ref 6) .assumption
      (.atomClash .after extras .nul object (ref 2) (ref 15) (.boxElim topEffect (ref 3) .assumption) .assumption)
      (linRaw lenFacts [(.after i, 1), (.after (extras.term .length), -1)] (-1)
        (.andIntro (.atomToLinear .after (ref 5) lenEq₂ (.atAndRight (ref 6) (ref 4) .assumption))
          (.andIntro (.atomToLinear .after (ref 16) below .assumption) .truth))))

private def raw : RawDerivation :=
  .cut (.at .after (ref 8)) (.frame Φ (ref 13) (ref 8) θ boxF .assumption .assumption) afterF

#guard isOk (checkScoped arena ⟨2, 2⟩ Γ goal raw)

-- Without the transition the frame's premise is missing.
#guard errorOf (checkScoped arena ⟨2, 2⟩ (Γ.filter (· != .transition Φ)) goal raw) = "assumption: not a premise"
-- From `F` alone, without the framed `L` case, the cases of `F` have no box
-- in the `L` branch: the premise `g₁ ∨ g₂ ∨ □_Φ L` is missing.
#guard errorOf (checkScoped arena ⟨2, 2⟩ (.at .before (ref 8) :: Γ.drop 1) goal raw) = "assumption: not a premise"

-- `F` read one binder further builds and checks; a field path for slot `0`
-- under the boxes of `F` is refused.
#guard isOk (substAssertion arena (Substitution.shift 2) (ref 8))
#guard errorOf (substAssertion arena { images := #[.path ⟨1, ["next"]⟩, .path (.var 1)] } (ref 8)) =
  "substAssertion: a slot is outside the substitution"
-- A field path for slot `1`, which the boxes of `g₁` do not read, is accepted.
#guard isOk (substAssertion arena { images := #[.path (.var 0), .path ⟨0, ["next"]⟩] } (ref 1))
-- A box of a regional effect `{x[elements]: any}` under the identity and
-- under a renaming of its root.
#guard isOk (substAssertion arena (Substitution.ident 2) (ref 21))
#guard isOk (substAssertion arena { images := #[.path (.var 1), .path (.var 0)] } (ref 21))

-- The tolerant frame rule with an invariant's support: `g₁ ⊢ □_Φ g₁`.
#guard isOk (checkScoped arena ⟨2, 2⟩ [.at .before (ref 1)] (.at .before (ref 20))
  (.tolerantFrame [] .invariant ⟨[]⟩ .truth (ref 1) (ref 1) .assumption .assumption .assumption))
-- A support the effect does not respect is refused: `{values: keep}`
-- against `Φ = {values: any}`.
#guard errorOf (checkScoped arena ⟨2, 2⟩ [.at .before (ref 1)] (.at .before (ref 20))
  (.tolerantFrame [(.cls .values, .keep)] .invariant ⟨[]⟩ .truth (ref 1) (ref 1) .assumption .assumption
    .assumption)) = "tolerantFrame: the effect does not respect the support"
-- With a disjointness certificate the spines' support is respected.
#guard isOk (checkScoped arena ⟨2, 2⟩ [.at .before (ref 1)] (.at .before (ref 20))
  (.tolerantFrame [(.cls .spines, .keep)] .invariant ⟨[(0, 0, .classes .intrinsic .intrinsic)]⟩ .truth (ref 1) (ref 1) .assumption
    .assumption .assumption))

-- Region inclusion by selectors: `{arrays: keep} ⊑ {spines: grow}`, not
-- the converse.
#guard InclusionEvidence.regions.check arena (ref 1) [(.cls .arrays, .keep)] [(.cls .spines, .grow)]
#guard !InclusionEvidence.regions.check arena (ref 1) [(.cls .spines, .grow)] [(.cls .arrays, .keep)]
-- The views analogue: `{views: keep} ⊑ {spines: grow}`, not the converse,
-- and array spines and view spines are disjoint classes.
#guard InclusionEvidence.regions.check arena (ref 1) [(.cls .views, .keep)] [(.cls .spines, .grow)]
#guard !InclusionEvidence.regions.check arena (ref 1) [(.cls .spines, .grow)] [(.cls .views, .keep)]
#guard !InclusionEvidence.regions.check arena (ref 1) [(.cls .views, .keep)] [(.cls .arrays, .grow)]
#guard Selector.arrays.disjoint Selector.views

-- A literal witness: `□_⊤(p.items ≐ null) ⊢ rigid(p.items)`.
#guard isOk (checkScoped arena ⟨2, 2⟩ [.at .before (ref 1)] (.at .before (ref 19))
  (.existsIntroLiteral (ref 18) .nul 2 (ref 1) .assumption))

-- Opening `rigid(p.items)` keeps the ambient premise `i < |p.widths|`, read
-- one slot further, and concludes it.
private def belowBefore : Formula := .linear (tagFact .before below)
private def belowShifted : Formula := .linear (renameFact (shiftVar .before) (tagFact .before below))

#guard isOk (checkScoped arena ⟨2, 2⟩ [.at .before (ref 19), belowBefore] belowBefore
  (.existsElim .before (ref 19) (ref 18) 2 [belowShifted] belowShifted .assumption .assumption))
-- The conclusion read at the eigenvariable's own slot is refused.
#guard errorOf (checkScoped arena ⟨2, 2⟩ [.at .before (ref 19), belowBefore] belowBefore
  (.existsElim .before (ref 19) (ref 18) 2 [belowBefore] belowBefore .assumption .assumption)) =
  "existsElim: a premise is not read one slot further"

end P18Plumbing

end Verification.Parity.Tests
