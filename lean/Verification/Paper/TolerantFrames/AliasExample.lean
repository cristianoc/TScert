import Verification.Paper.TolerantFrames.Admission
import Verification.Paper.TolerantFrames.Loops

/-! # The actual aliasing loop

This extends the command language, not the older six-node example. The source
is `for (let j=from; j<to; j++) { if(j>out.length) throw new RangeError();
out[j]=xs[j]; }`. A private cell represents the mutable loop variable. The
command contains the output-length test, constructor and throw. Its head and
all displayed integer obligations are stated below. The connection from these
obligations to primitive execution and a closed annotated-graph proof is a
separate obligation; these arithmetic lemmas are not such a proof.
-/
namespace Verification.Paper.TolerantFrames.AliasExample
open Verification Footprints HeapKnowledge HeapObservations
open Verification.TolerantFrames

/-- Slots: from=0, to=1, xs=2, out=3, RangeError=4, j's private cell=5;
iteration temporaries j=6, test=7, k=8, out-test=9, error=10, v=11, j'=12. -/
def body : Command :=
  let increment : Command := .seq
    (.step (.bind 12 (.binary .add (.variable 6) (.literal (.number (bitsOfNat 1))))))
    (.step (.perform (.fieldWrite 5 "value" (.variable 12))))
  let copy : Command := .seq
    (.step (.bind 11 (.elementRead 2 (.variable 6))))
    (.seq (.step (.perform (.elementWrite 3 (.variable 6) (.variable 11)))) increment)
  let raiseError : Command := .seq (.step (.bind 10 (.construct 4 []))) (.throw_ (.variable 10))
  let checkOutput : Command := .seq (.step (.bind 8 (.arrayLength 3)))
    (.seq (.step (.bind 9 (.binary .gt (.variable 6) (.variable 8))))
      (.choice (.variable 9) raiseError copy))
  .seq (.step (.bind 6 (.fieldRead 5 "value")))
    (.seq (.step (.bind 7 (.binary .lt (.variable 6) (.variable 1))))
      (.choice (.variable 7) checkOutput .break_))

/-- The entire loop includes its initialisation from `from`. -/
def program : Command :=
  .seq (.step (.bind 5 (.objectLiteral [("value", .variable 0)]))) (.loop body)

/-- Freshness and scope of every named intermediate result, including both
tests and the caught-free exception construction. Iteration-local names do
not escape the loop. -/
theorem program_scoped : Command.WellScoped (fun x => x < 5) program (fun x => x = 5 ∨ x < 5) := by
  unfold program body
  apply Command.WellScoped.seq
  · apply Command.WellScoped.bind <;> simp [Operation.Scoped, Argument.Scoped, Operation.Binds]
  · apply Command.WellScoped.loop
    repeat first
      | apply Command.WellScoped.seq
      | apply Command.WellScoped.choice_input
      | apply Command.WellScoped.bind
      | apply Command.WellScoped.perform
      | apply Command.WellScoped.throw_
      | apply Command.WellScoped.break_
      | simp [Operation.Scoped, Argument.Scoped, Operation.Binds]

/-- The displayed head assertion, read after the iteration's j binding.
Density is a type-system assumption about xs, separate from this knowledge. -/
def Head : Assertion := fun ρ _ s =>
  ∃ j stop len, intValue (ρ 6) = some j ∧ intValue (ρ 1) = some stop ∧
    lengthOf s.h (ρ 2) = some len ∧ 0 ≤ j ∧ j ≤ stop ∧ stop ≤ len

/-- Row 1: the entry obligations supply precisely the three head bounds. -/
theorem entry {start stop len : Int} (h : 0 ≤ start ∧ start ≤ stop ∧ stop ≤ len) :
    0 ≤ start ∧ start ≤ stop ∧ stop ≤ len := h

/-- Rows 2 and 4: the true head branch establishes the source-read bound. -/
theorem read_bound {j stop len : Int} (h : 0 ≤ j ∧ j ≤ stop ∧ stop ≤ len) (hg : j < stop) :
    0 ≤ j ∧ j < len := by omega

/-- Row 3: the false output-length branch is exactly the needed upper bound.
The true branch throws and has postcondition true. -/
theorem output_test {j outLen : Int} (hn : ¬ outLen < j) : j ≤ outLen := by omega

/-- Row 5: the two tests give both conditions for an in-or-at-end write.
No premise compares the references xs and out. -/
theorem write_bound {j stop len outLen : Int}
    (h : 0 ≤ j ∧ j ≤ stop ∧ stop ≤ len) (hg : j < stop)
    (hout : j ≤ outLen) (hmax : len ≤ 4294967295) :
    0 ≤ j ∧ j ≤ outLen ∧ j < 4294967295 := by omega

/-- Row 5's Grow consequence. Neither equality nor inequality of references
is needed to retain the lower bound when the source spine grows. -/
theorem lower_bound_after_growth {stop len len' : Int} (h : stop ≤ len) (hg : len ≤ len') : stop ≤ len' := by omega

/-- Row 6: the increment is within the safe-integer range under the source
array bound. Its actual floating-point exactness is the shared Add rule. -/
theorem increment_range {j stop len : Int}
    (h : 0 ≤ j ∧ j ≤ stop ∧ stop ≤ len) (hg : j < stop) (hmax : len ≤ 4294967295) :
    -9007199254740991 ≤ j + 1 ∧ j + 1 ≤ 9007199254740991 := by omega

/-- Row 7: after j'=j+1 and growth, the complete head, including j'≤to,
is established by the edge renaming j↦j'. -/
theorem back_edge {j stop len len' : Int}
    (h : 0 ≤ j ∧ j ≤ stop ∧ stop ≤ len) (hg : j < stop) (hgrow : len ≤ len') :
    0 ≤ j + 1 ∧ j + 1 ≤ stop ∧ stop ≤ len' := by omega

/-- Row 8: the false head branch retains the head and exits at j=to. -/
theorem exit {j stop len : Int} (h : 0 ≤ j ∧ j ≤ stop ∧ stop ≤ len) (hg : ¬ j < stop) :
    j = stop ∧ 0 ≤ j ∧ j ≤ stop ∧ stop ≤ len := by omega

end Verification.Paper.TolerantFrames.AliasExample
