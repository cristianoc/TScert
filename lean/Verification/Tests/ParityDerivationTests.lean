import Verification.Semantics.ParityDerivations

/-! Research tests of the parity derivations, kept while the derivations
are built and replaced by pipeline cases once the pass produces them: each
encodes a derivation of the note "Tolerant frames"
(`docs/drafts/tolerant-frames-note/note.tex`) as a `RawDerivation` and checks
it with `checkScoped`, which checks the arena and the scopes first: what it
accepts holds by `checkScoped_sound`.

- The arithmetic of `index[c >> 8]`, with `0 ≤ c < 1114112` and
  `index.length = 4352`, and of `table[x & 255]` with `table.length = 256`
  (I4, "Arithmetic indices and range conditions").
- The modal plumbing of P18's two-field guard (not yet P18's parity
  derivation): the guard `g₁ ∨ g₂ ∨ L` across a call of effect
  `{values: any}`, by law (d), Frame and guard elimination
  (`astra/parity-plan-out.md`, P18). Two premises stand for evidence the
  rules do not produce yet: the guards are `□_⊤(π ≐ null)`, which P18
  obtains from the null tests and the fields' stable contracts (stable
  paths have no introduction rule yet); and the `L` case is framed
  inside its branch, `g₁ ∨ g₂ ∨ □_Φ L`, which P18 obtains by the
  tolerant frame rule at the stores' keep support, whose regional
  support certificate the shared foundation supplies. -/
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
-- `xs.store` is an array store, disjoint from the view stores.
#guard (DisjointEvidence.classes (.arrayAt (r 0)) .intrinsic).check arena (r 2) (.store 0 []) (.cls .views)
-- Without a conjunct naming `ys` as an array, `ys.store` has no class.
#guard !(DisjointEvidence.classes (.arrayAt (r 0)) .intrinsic).check arena (r 2) (.store 2 []) (.cls .views)
#guard (DisjointEvidence.classes (.arrayAt (r 1)) .intrinsic).check arena (r 2) (.store 2 []) (.cls .views)
-- The two stores a separation names, in either order.
#guard (DisjointEvidence.stores (r 1)).check arena (r 2) (.store 0 []) (.store 2 [])
#guard (DisjointEvidence.swap (.stores (r 1))).check arena (r 2) (.store 2 []) (.store 0 [])
-- A store's cells are values, disjoint from every store.
#guard (DisjointEvidence.classes .intrinsic .intrinsic).check arena (r 2) (.pathElems 0 []) (.cls .stores)
-- `{p.items.store: any}` is rigid where `p.items` is; `{p.items[cells]: any}` is not.
#guard (RigidityEvidence.stable [r 5]).check arena (r 5) [(.store 0 ["items"], .any), (.cls .values, .any)]
#guard !(RigidityEvidence.stable [r 5]).check arena (r 5) [(.pathElems 0 ["items"], .any)]
-- Inclusion by class: the cells of `xs` at `any` are within `{values: any}`.
#guard (InclusionEvidence.byClass [.intrinsic]).check arena (r 2) [(.pathElems 0 [], .any)] [(.cls .values, .any)]
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
  .box [(.cls .values, .any), (.store 2 [], .any)] (r 0),               -- 2 (Sep)
  .box [(.cls .values, .init)] (r 0),                                   -- 3 (Init)
  .atom (.linear (.le [(Term.value 1, 1), (Term.now .view 3 [], -1)] 0)), -- 4 n ≤ view(w)
  .box topEffect (r 4),                                                 -- 5 (View)
  .apart (.var 2) (.var 0),                                             -- 6 apart(y, x)
  .atom (.every (.var 0) (Term.value 1) [.atom (.le [(.elem, -1)] (-1))]), -- 7 every(x, n, v > 0)
  .box [(.store 2 [], .any), (.pathElems 2 [], .any)] (r 7),            -- 8 (Every)
  .atom (.equal ⟨5, ["f"]⟩ (.path (.var 0))),                           -- 9
  .box topEffect (r 9),                                                 -- 10
  .existsValue (r 10),                                                  -- 11 rigid(p.f), p at slot 4
  .atom (.linear (lowerFact 2 0)),                                      -- 12 n ≤ |y|, y fresh at slot 0
  .box grow (r 12),                                                     -- 13
  .atom (.linear (.le [(Term.value 1, 1), (Term.now .length 4 ["f"], -1)] 0)), -- 14 n ≤ |p.f|
  .box grow (r 14),                                                     -- 15 (Rigid) with (Grow)
  .atom (.linear (.le [(Term.value 1, 1), (Term.length 2, -1)] 0)),      -- 16 n ≤ |y|
  .box [(.cls .values, .any), (.store 2 [], .any)] (r 16)]⟩             -- 17

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
-- (Every) needs `apart`; a store separation leaves the cells shared.
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

/-- `step`'s effect `{values: any}`, stores kept. -/
private def Φ : Footprint := (⟨.any, .keep⟩ : Footprints.Closed).fp

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
  .box [(.elems 0, .any)] (ref 0),             -- 21 □_{p[elements]: any} (p.items ≐ null)
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
-- With a disjointness certificate the stores' support is respected.
#guard isOk (checkScoped arena ⟨2, 2⟩ [.at .before (ref 1)] (.at .before (ref 20))
  (.tolerantFrame [(.cls .stores, .keep)] .invariant ⟨[(0, 0, .classes .intrinsic .intrinsic)]⟩ .truth (ref 1) (ref 1) .assumption
    .assumption .assumption))

-- Region inclusion by selectors: `{arrays: keep} ⊑ {stores: grow}`, not
-- the converse.
#guard InclusionEvidence.regions.check arena (ref 1) [(.cls .arrays, .keep)] [(.cls .stores, .grow)]
#guard !InclusionEvidence.regions.check arena (ref 1) [(.cls .stores, .grow)] [(.cls .arrays, .keep)]
-- The views analogue: `{views: keep} ⊑ {stores: grow}`, not the converse,
-- and array stores and view stores are disjoint classes.
#guard InclusionEvidence.regions.check arena (ref 1) [(.cls .views, .keep)] [(.cls .stores, .grow)]
#guard !InclusionEvidence.regions.check arena (ref 1) [(.cls .stores, .grow)] [(.cls .views, .keep)]
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
