import Lean.Data.Json
import Verification.Types.GraphRows
import Verification.Types.PositiveCertificates
import Verification.Programs.CertificateProducer

/-! What the source path asks of the labels it types a program with, and of
the store that gives them meaning. The checked requests are written against
these two interfaces, which two stores provide: the store extraction grows
over the lowering's heads (`EquationStore.State`, labels `Tree`), and the
equations those heads present, frozen (`EquationStore.Checked`, labels
`CheckedLabel`). Neither interface carries a proof obligation: a store's graph
is what the checked requests are proved safe over, whatever store built it. -/
namespace Verification.LabelStore
open Lean PositiveGraphs PositiveNormalization CallEffects

/-- A label, apart from any store: decidable equality and hashing (search
caches are keyed by types), a total order for the canonical order of unions,
its JSON spelling, and the four primitive values' labels, which every store
holds as they are. -/
class Labels (ι : Type) extends Hashable ι, Ord ι, ToJson ι, FromJson ι, Repr ι,
    CertificateProducer.Instantiates ι where
  decEq : DecidableEq ι
  nul : ι
  tru : ι
  fls : ι
  undef : ι

instance (priority := low) {ι : Type} [Labels ι] : DecidableEq ι := Labels.decEq

namespace Labels
variable {ι : Type} [Labels ι]

/-- The order of a canonical union: sorted by `compare`, each label once. -/
@[nospecialize] def le (a b : ι) : Bool := compare a b != .gt

@[nospecialize] def lt (a b : ι) : Bool := compare a b == .lt

/-- Lexicographic order on unions, for the canonical order of their lists. -/
@[nospecialize] def before : List ι → List ι → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => lt a b || (a == b && before as bs)

end Labels

/-- What a diagnostic shows of a store: a finite table of rows over its own
positions, the position each label the diagnostic mentions is shown at, and a
source-like spelling of the positions that stand for applications
(`Promise<number | R>`). The table holds the mentioned labels and what their
rows name, to a depth bound; past it, an application is an opaque named
reference: a `names` entry whose row has no clauses. A diagnostic is display
data: nothing checks or trusts a projection. -/
structure Projection (ι : Type) where
  /-- The table under `types`, rows naming positions in it. -/
  rows : List (GraphRow Nat)
  /-- Where a mentioned label is shown: its position in `rows`. -/
  position : ι → Nat
  /-- An application's spelling by position, in position order, each once;
  `names`, left out when empty. -/
  names : List (Nat × String) := []

namespace Projection

/-- How many row references below a mentioned label a projection expands. -/
def depth : Nat := 3

/-- A union as a diagnostic shows it. -/
@[nospecialize] def shown {ι : Type} (p : Projection ι) (A : List ι) : List Nat := A.map p.position

end Projection

/-- What checking reads of a store: labels with rows, their graph and the
image check its instances use. `σ` is the store's state, `ι` its labels.
Rows are read through `row` and interpreted through `graph`, which must
agree with them; `valid` says which labels the store holds, `wellFormed`
that its rows name only those. `labels` lists labels with rows of their own,
and `bound` bounds any closure over rows (the vocabulary a search is offered
is such a closure). A checked request reads its store through this view
only, so a store that no longer grows (`EquationStore.Checked`) is one. -/
class StoreView (σ : Type) (ι : outParam Type) [Labels ι] extends ToJson σ, FromJson σ where
  /-- The graph the store denotes. Built once per state: its rows are read
  at every step of search and checking. -/
  graph : σ → NormalGraph ι
  /-- A label's row; an empty clause row for a label the store lacks. -/
  row : σ → ι → GraphRow ι
  /-- Whether the store holds a label. -/
  valid : σ → ι → Bool
  /-- Whether every row names only labels the store holds, and binds only
  parameters. -/
  wellFormed : σ → Bool
  /-- The labels with rows of their own. -/
  labels : σ → List ι
  /-- A bound on the rounds of a fixpoint over rows. -/
  bound : σ → Nat
  /-- The built-in array prototype, `ArrayProto`: the prototype every array
  type names. -/
  arrayProto : σ → ι
  /-- The label of a union of clauses, when the store has one. -/
  lookup : σ → List (Clause (List ι)) → Option ι
  /-- What a diagnostic mentioning these labels shows of the store, rows
  expanded `depth` references deep (`Projection`). -/
  project : σ → List ι → Nat → Projection ι
  /-- How an instance's images are checked in this store's graph: proved
  sound, supplied by verified code, never by a certificate. -/
  images : (T : σ) → PositiveCertificates.InstanceImageCheck (graph T)

/-- What a diagnostic mentioning `mentioned` shows of the store, to the
projection's depth. -/
@[nospecialize] def StoreView.projection {σ ι : Type} [Labels ι] [StoreView σ ι] (T : σ) (mentioned : List ι) : Projection ι :=
  StoreView.project T mentioned Projection.depth

end Verification.LabelStore
