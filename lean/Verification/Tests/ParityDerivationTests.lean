import Verification.Semantics.ParityDerivations

/-! Research tests of the parity derivations, kept while the derivations
are built and replaced by pipeline cases once the pass produces them: each
encodes a derivation of the note "Tolerant frames"
(`docs/drafts/tolerant-frames-note/note.tex`) as a `RawDerivation` and checks
it with `checkDerivation`. A derivation the checker accepts is valid by
`Derivation.sound`.

- The arithmetic of `index[c >> 8]`, with `0 ≤ c < 1114112` and
  `index.length = 4352`, and of `table[x & 255]` with `table.length = 256`
  (I4, "Arithmetic indices and range conditions").
- P18: the two-field guard `p.items = null ∨ p.items.insideExtras = null ∨
  |p.items.insideExtras| = |p.widths|` across a call of effect
  `{values: any}`, by law (d), Frame and guard elimination
  (`astra/parity-plan-out.md`, P18). The preservation of the length
  equality itself, `K ∧ L ⊢ □_Φ L`, is the tolerant frame theorem at a
  support the call's effect respects; its checked respect reads region
  membership and is a premise here. -/
namespace Verification.Parity.Tests
open Verification Footprints HeapKnowledge

private def isOk {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

/-- The empty arena: the arithmetic derivations name no assertion. -/
private def empty : AssertionArena := ⟨#[]⟩

/-- A linear certificate found by the search, to be checked. -/
private def proveOr (Fs : List (Linear.Fact StepVar)) (f : Linear.Form StepVar) (d : Int) :
    List (Linear.Step StepVar) :=
  (Linear.prove Fs f d).getD []

/-- The conjunction of a list of linear premises, each a premise. -/
private def premisesRaw : Nat → RawDerivation
  | 0 => .truth
  | n + 1 => .andIntro .assumption (premisesRaw n)

/-! ## `index[c >> 8]` -/

namespace Shift
private def c : Path := .var 1
private def j : Path := .var 0
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

private def shrA : Formula := .linear (.le [(av j, -1)] 0)
private def shrB : Formula := .linear (.le [(av j, 2 ^ 8), (av c, -1)] 0)
private def shrC : Formula := .linear (.le [(av c, 1), (av j, -(2 ^ 8))] (2 ^ 8 - 1))

private def boundFacts : List (Linear.Fact StepVar) :=
  [.le [(av j, 2 ^ 8), (av c, -1)] 0, .le [(av c, 1)] 1114111, .le [(index, -1)] (-4352)]

private def raw : RawDerivation :=
  .cut (smallFacts c)
    (.andIntro .assumption
      (.andIntro (.linear [.le [(av c, 1)] 1114111] (proveOr [.le [(av c, 1)] 1114111] [(av c, 1)] (2 ^ 31 - 1))
        (premisesRaw 1)) .truth))
    (.cut (shrFacts c j 8) (.shiftRight c j eight .assumption .assumption)
      (.andIntro (.andLeft (.and shrB (.and shrC .truth)) .assumption)
        (.andIntro
          (.linear boundFacts (proveOr boundFacts [(av j, 1), (index, -1)] (-1))
            (.andIntro (.andLeft (.and shrC .truth) (.andRight shrA .assumption))
              (.andIntro .assumption (.andIntro .assumption .truth))))
          .truth)))

#guard isOk (checkDerivation empty Γ goal raw)

-- The checker refuses the bound one past the table.
private def goalPast : Formula :=
  conj [.linear (.le [(av j, -1)] 0), .linear (.le [(av j, 1), (index, -1)] (-2))]

#guard !isOk (checkDerivation empty Γ goalPast raw)

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

private def maskA : Formula := .linear (.le [(av y, -1)] 0)
private def maskB : Formula := .linear (.le [(av y, 1)] 255)
private def maskC : Formula := .linear (.le [(av y, 1), (av x, -1)] 0)

private def boundFacts : List (Linear.Fact StepVar) := [.le [(av y, 1)] 255, .le [(table, -1)] (-256)]

private def raw : RawDerivation :=
  .cut (maskFacts x y 255) (.mask x y mask255 .assumption (premisesRaw 2))
    (.andIntro (.andLeft (.and maskB (.and maskC .truth)) .assumption)
      (.andIntro
        (.linear boundFacts (proveOr boundFacts [(av y, 1), (table, -1)] (-1))
          (.andIntro (.andLeft (.and maskC .truth) (.andRight maskA .assumption))
            (.andIntro .assumption .truth)))
        .truth))

#guard isOk (checkDerivation empty Γ goal raw)

/-- Without the operand's range the mask rule does not apply. -/
private def Γnarrow : List Formula := Γ.take 2 ++ Γ.drop 3

#guard !isOk (checkDerivation empty Γnarrow goal raw)

end Mask

/-! ## P18: the two-field guard -/

namespace P18
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
  .atom (.linear below)]⟩                      -- 16 i < |p.widths|

#guard arena.check

/-- The identity transport: the call binds no name. -/
private def θ : Substitution := ⟨#[.var 0, .var 1]⟩

/-- Before the call `F` and, by the tolerant frame theorem, `□_Φ L` (in the
case `L`); the call's transition; after it, both null tests failed and
`i < |p.widths|`. -/
private def Γ : List Formula :=
  [.at .before (ref 8), .at .before (ref 9), .transition Φ, .transport θ,
    .at .after (ref 14), .at .after (ref 15), .at .after (ref 16)]

/-- `i < |p.items.insideExtras|` after the call. -/
private def goal : Formula := .linear (.le [(.after i, 1), (.after (extras.term .length), -1)] (-1))

/-- `□_Φ F` before the call, by law (d) twice. -/
private def boxF : RawDerivation :=
  .guardCases .before (ref 8) (ref 1) (ref 7) .assumption
    (.boxGuard Φ (ref 12) (ref 1) (ref 11) (ref 7) (ref 8) (.guardLeft (ref 1) (ref 11) .assumption))
    (.boxGuard Φ (ref 12) (ref 1) (ref 11) (ref 7) (ref 8)
      (.guardRight (ref 1) (ref 11)
        (.boxGuard Φ (ref 10) (ref 3) (ref 9) (ref 6) (ref 7) (.guardRight (ref 3) (ref 9) .assumption))))

private def lenFacts : List (Linear.Fact StepVar) :=
  [tagFact .after lenEq₂, tagFact .after below]

/-- After the call: the guards are eliminated by the failed null tests. -/
private def afterF : RawDerivation :=
  .guardCases .after (ref 8) (ref 1) (ref 7) .assumption
    (.atomClash .after items .nul object (ref 0) (ref 14) (.boxElim topEffect (ref 1) .assumption) .assumption)
    (.guardCases .after (ref 7) (ref 3) (ref 6) .assumption
      (.atomClash .after extras .nul object (ref 2) (ref 15) (.boxElim topEffect (ref 3) .assumption) .assumption)
      (.linear lenFacts (proveOr lenFacts [(.after i, 1), (.after (extras.term .length), -1)] (-1))
        (.andIntro (.atomToLinear .after (ref 5) lenEq₂ (.atAndRight (ref 6) (ref 4) .assumption))
          (.andIntro (.atomToLinear .after (ref 16) below .assumption) .truth))))

private def raw : RawDerivation :=
  .cut (.at .after (ref 8)) (.frame Φ (ref 13) (ref 8) θ boxF .assumption .assumption) afterF

#guard isOk (checkDerivation arena Γ goal raw)

-- Without the transition the frame does not apply.
#guard !isOk (checkDerivation arena (Γ.filter (· != .transition Φ)) goal raw)

end P18

end Verification.Parity.Tests
