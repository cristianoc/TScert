import Std.Data.HashMap

/-! The work table of a profiled process (`TSCERT_PROFILE`,
docs/drafts/on-demand-processing.md, "Accounting"): a measurement, which no
result reads. -/
namespace Verification.SinglePass

/-- Whether `timedKind` and `work` measure (`TSCERT_PROFILE`): off, they run
`f` alone. -/
initialize profiling : IO.Ref Bool ← IO.mkRef false

/-- The work of the process by kind and item: for each `kind` and `item` (a
function or file of a source, `<sha256 prefix>#<unit>`), how many times it
was done, its nanoseconds, and its nanoseconds outside the work nested in it:
a measurement. -/
initialize workTable : IO.Ref (Std.HashMap (String × String) (Nat × Nat × Nat)) ← IO.mkRef {}

/-- Each open work's item and the nanoseconds of the work nested in it,
innermost first. -/
initialize workNested : IO.Ref (List (String × Nat)) ← IO.mkRef []

private unsafe def workImpl {α : Type} (kind item : String) (f : Unit → α) : α :=
  if !(unsafeBaseIO profiling.get) then f () else
  match unsafeIO (do
      workNested.modify ((item, 0) :: ·)
      let t0 ← IO.monoNanosNow
      let a ← IO.lazyPure f
      let t1 ← IO.monoNanosNow
      let inner ← workNested.modifyGet fun | (_, n) :: rest => (n, rest) | [] => (0, [])
      let d := t1 - t0
      workNested.modify fun | (i, n) :: rest => (i, n + d) :: rest | [] => []
      workTable.modify fun m =>
        let (c, t, s) := m.getD (kind, item) (0, 0, 0)
        m.insert (kind, item) (c + 1, t + d, s + (d - inner))
      pure a) with
  | .ok a => a
  | .error _ => f ()

/-- `f ()`, recorded as one `kind` of work on `item` where profiling. -/
@[implemented_by workImpl] def work {α : Type} (_kind _item : String) (f : Unit → α) : α := f ()

private unsafe def workWithinImpl {α : Type} (kind : String) (f : Unit → α) : α :=
  if !(unsafeBaseIO profiling.get) then f () else
  match unsafeBaseIO workNested.get with
  | (item, _) :: _ => workImpl kind item f
  | [] => f ()

/-- `f ()`, recorded as one `kind` of work on the item of the innermost
work open around it, where profiling: work nested in a function's walk, such
as the walk's rounds over its body, counted on that function. -/
@[implemented_by workWithinImpl] def workWithin {α : Type} (_kind : String) (f : Unit → α) : α := f ()

end Verification.SinglePass
