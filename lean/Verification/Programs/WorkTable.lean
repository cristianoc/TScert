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

/-- The kinds of the works open, innermost first, each with the sequence
number of its opening in the process: the context a graph run is recorded
in (`runRecorded`). -/
initialize workStack : IO.Ref (List String) ← IO.mkRef []

/-- The works opened in the process so far. -/
initialize workSeq : IO.Ref Nat ← IO.mkRef 0

/-- `f ()` timed as work on `item`, its row's kind computed from its result
(`kindOf`): the row is counted, its nanoseconds and those outside the work
nested in it added. -/
private unsafe def workKindImpl {α : Type} (name : String) (kindOf : α → String) (item : String) (f : Unit → α) :
    IO α := do
  let seq ← workSeq.modifyGet fun n => (n, n + 1)
  workNested.modify ((item, 0) :: ·)
  workStack.modify ((s!"{name}@{seq}") :: ·)
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  let inner ← workNested.modifyGet fun | (_, n) :: rest => (n, rest) | [] => (0, [])
  workStack.modify fun | _ :: rest => rest | [] => []
  let d := t1 - t0
  workNested.modify fun | (i, n) :: rest => (i, n + d) :: rest | [] => []
  let kind := kindOf a
  workTable.modify fun m =>
    let (c, t, s) := m.getD (kind, item) (0, 0, 0)
    m.insert (kind, item) (c + 1, t + d, s + (d - inner))
  pure a

private unsafe def workImpl {α : Type} (kind item : String) (f : Unit → α) : α :=
  if !(unsafeBaseIO profiling.get) then f () else
  match unsafeIO (do
      let seq ← workSeq.modifyGet fun n => (n, n + 1)
      workNested.modify ((item, 0) :: ·)
      workStack.modify ((s!"{kind}@{seq}") :: ·)
      let t0 ← IO.monoNanosNow
      let a ← IO.lazyPure f
      let t1 ← IO.monoNanosNow
      let inner ← workNested.modifyGet fun | (_, n) :: rest => (n, rest) | [] => (0, [])
      workStack.modify fun | _ :: rest => rest | [] => []
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

/-- A string's digest: a 64-bit hash, in hexadecimal. -/
def digestOf (s : String) : String :=
  let h := hash s
  let hex := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - hex.length) ++ hex

private unsafe def runRecordedImpl {α : Type} (purpose route : String) (digests : Unit → String × String)
    (visits : α → Nat) (f : Unit → α) : α :=
  if !(unsafeBaseIO profiling.get) then f () else
  match unsafeIO (do
      let item := match ← workNested.get with
        | (i, _) :: _ => i
        | [] => ""
      let (body, whole) ← workKindImpl "account: run digest" (fun _ => "account: run digest") item fun _ => digests ()
      let stack ← workStack.get
      let seq ← workSeq.modifyGet fun n => (n, n + 1)
      let context := String.intercalate "<" stack
      -- (timed apart from the work around it, which keeps its time: the
      -- row adds no time outside its work)
      let t0 ← IO.monoNanosNow
      let a ← IO.lazyPure f
      let t1 ← IO.monoNanosNow
      let kind := "run: " ++ String.intercalate "\t"
        [toString seq, purpose, route, body, whole, toString (visits a), context]
      workTable.modify fun m =>
        let (c, t, s) := m.getD (kind, item) (0, 0, 0)
        m.insert (kind, item) (c + 1, t + (t1 - t0), s)
      pure a) with
  | .ok a => a
  | .error _ => f ()

/-- **A graph run, recorded** where profiling: `f ()`, its row in the work
table of kind `run: <seq>\t<purpose>\t<route>\t<body>\t<whole>\t<visits>\t<context>`
on the item of the innermost work open around it, where `body` digests the
run's inputs but its bound and `whole` all of them (`digests`, computed
only where profiling, its time a work of its own), `visits` the transfers
it made and `context` the works open around it, innermost first: each run
has an identity, a measurement. -/
@[implemented_by runRecordedImpl] def runRecorded {α : Type} (_purpose _route : String)
    (_digests : Unit → String × String) (_visits : α → Nat) (f : Unit → α) : α := f ()

end Verification.SinglePass
