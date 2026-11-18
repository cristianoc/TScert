import Verification.Source.ComponentWire
import Std.Data.HashSet

/-! # The read-only frame's checks of a component family

The checks (S), (K) and (O) of Paper I's rule Read-only frame
(`docs/drafts/tolerant-frames-note/note.tex`, "Calls of code outside a
component"; the draft `docs/drafts/readonly-handles.md`, "The checks the rule
requires"), over every body of every component of the family a fragment
describes (`ComponentWire.Components`), each failure located at the module
and span of the code it is of. The front's description is a proposal: the
flow of possible sites, the marks and the crossings are each checked here
against the events of the code (allocations, stores, calls, throws,
catches, the bindings a module or a closure holds, the bindings a module
exports), which the front reads from the source.

- **The flow** (`flowDiags`): every value includes what the code's
  statements make it include; every store puts its value in the contents of
  each site its receiver may be, at a key the site has; every call passes
  its arguments, receiver and result between the call and each code it may
  run, enters its result from outside where its callee may be outside code,
  and, of a native, gives its result its site, what it is given and what
  that holds, and what its callbacks return; every member of a component
  (an entry, or a code of it whose site is exposed or released for it)
  enters its parameters and receiver from outside.
- **(S), no suspension** (`suspensionDiags`): no `await`, `yield`, async
  function or generator in a component's code, nested and unused bodies
  included; an async function of the checked file the lowering reads is one
  whatever the description states.
- **(K), the marks** (`marksDiags`): each site's marks are one per
  enclosing component, innermost first, each at most the mark of the
  component nested in it; every crossing the events make (`crossings`) is
  stated with the type of its position; a value crossing out of a component
  reaches no local or internal site of it, and an exposed one only at a
  read-only position; storage that is not local holds no local storage; a
  binding a module or a closure of the component holds reaches no local
  storage.
- **(O), the stores** (`ownershipDiags`): a store into storage that may be
  protected (a local or exposed site's, a released site's but its initial
  values, a value entering from outside) stores a value all of whose
  reachable storage is of the component's local or exposed sites.

Nothing in acceptance reads the outcome (`familyOutcome`): the verifier
prints it beside the units' verdicts (`WorkerWire.componentOutcome`). -/
namespace Verification.ComponentChecks
open ComponentWire

/-- A value's tokens: its possible sites and the components it may enter
from outside. -/
structure Tokens where
  sites : List Nat
  incoming : List Nat
  deriving Inhabited

def Tokens.empty : Tokens := ⟨[], []⟩

def Tokens.union (a b : Tokens) : Tokens := ⟨a.sites ++ b.sites, a.incoming ++ b.incoming⟩

/-- A failure of a check: the component whose certificate it refuses, the
check, and the place of the code it is of. -/
structure Diag where
  component : Nat
  check : String
  module : String
  place : Span
  message : String
  deriving Repr, BEq

def Diag.render (d : Diag) : String := s!"({d.check}) {d.module} {d.place.1}-{d.place.2}: {d.message}"

/-- **The family with its values' sets**, for membership tests. -/
structure Ctx where
  F : Components
  sitesOf : Array (Std.HashSet Nat)
  incomingOf : Array (Std.HashSet Nat)
  /-- The code each closure site is, by site. -/
  codeAtSite : Std.HashMap Nat Nat

def Ctx.of (F : Components) : Ctx :=
  { F, sitesOf := (F.values.map fun v => Std.HashSet.ofList v.sites).toArray,
    incomingOf := (F.values.map fun v => Std.HashSet.ofList v.incoming).toArray,
    codeAtSite := F.codes.zipIdx.foldl (fun m (c, i) => match c.site with
      | some s => m.insert s i
      | none => m) {} }

namespace Ctx
variable (cx : Ctx)

def value (v : Nat) : Tokens := match cx.F.values[v]? with
  | some x => ⟨x.sites, x.incoming⟩
  | none => .empty

def contents (t : Nat) : Tokens := match cx.F.sites[t]? with
  | some s => cx.value s.contents
  | none => .empty

/-- What a value's storage holds: its sites' contents, and of a value
entering from outside, a value entering from outside. -/
def read (v : Nat) : Tokens :=
  let x := cx.value v
  ⟨x.sites.flatMap (cx.contents · |>.sites), x.incoming ++ x.sites.flatMap (cx.contents · |>.incoming)⟩

def eval : Source → Tokens
  | .site s => ⟨[s], []⟩
  | .value v => cx.value v
  | .read v => cx.read v
  | .incoming c => ⟨[], [c]⟩

/-- Whether value `v` includes the tokens `t`. -/
def has (v : Nat) (t : Tokens) : Bool :=
  match cx.sitesOf[v]?, cx.incomingOf[v]? with
  | some s, some i => t.sites.all s.contains && t.incoming.all i.contains
  | _, _ => t.sites.isEmpty && t.incoming.isEmpty

/-- **The storage reachable from tokens**: their sites and every site the
contents of a reachable site hold, with the components a value of them may
enter from outside. -/
def closure (start : Tokens) : Tokens := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array Nat := #[]
  let mut incoming : Std.HashSet Nat := Std.HashSet.ofList start.incoming
  let mut work := start.sites
  for _ in [0:cx.F.sites.length + 1] do
    let mut next : List Nat := []
    for t in work do
      if !seen.contains t then
        seen := seen.insert t
        out := out.push t
        let c := cx.contents t
        next := c.sites ++ next
        for i in c.incoming do incoming := incoming.insert i
    work := next
  return ⟨out.toList, incoming.toList⟩

/-- A component's chain: itself and the components it is nested in,
innermost first. -/
def chain (c : Nat) : List Nat := go cx.F.components.length c
where
  go : Nat → Nat → List Nat
    | 0, c => [c]
    | n + 1, c => c :: match (cx.F.components[c]?).bind (·.parent) with
      | some p => go n p
      | none => []

/-- A site's mark for a component, where the site is of its code. -/
def mark (t C : Nat) : Option Mark := (cx.F.sites[t]?).bind fun s => s.marks.lookup C

def siteName (t : Nat) : String := match cx.F.sites[t]? with
  | some s => s!"{s.module} {s.pos.1}-{s.pos.2}"
  | none => s!"site {t}"

end Ctx

def markName : Mark → String
  | .local => "local"
  | .internal => "internal"
  | .exposed => "exposed"
  | .released => "released"

namespace Ctx
variable (cx : Ctx)

/-- The codes a component's interface names: each entry's code, and of an
entry naming a class, the class component's constructor. -/
def entryCodes (C : Nat) : List Nat :=
  match (cx.F.components[C]?).map Component.interface with
  | some (Interface.known es) => es.flatMap fun e =>
    match cx.F.codes.zipIdx.find? (fun (c, _) => c.module == e.module && c.pos == e.pos) with
    | some (_, i) => [i]
    | none =>
      -- A class: its own component's constructor entry.
      match cx.F.components.find? (fun k => k.kind == ComponentWire.Kind.klass && k.location == e.module && k.pos == some e.pos) with
      | some k => match k.interface with
        | .known ks => ks.filter (·.name == "constructor") |>.flatMap fun k' =>
          (cx.F.codes.zipIdx.find? fun (c, _) => c.module == k'.module && c.pos == k'.pos).map (·.2) |>.toList
        | .unknown _ => []
      | none => []
  | _ => []

/-- **A component's members**: the codes its interface names, and each
code of it whose closure is exposed or released for it, given to code that
is not its. -/
def members (C : Nat) : List Nat :=
  let escaped := cx.F.codes.zipIdx.filterMap fun (c, i) => do
    let s ← c.site
    match cx.mark s C with
    | some .exposed | some .released => some i
    | _ => none
  (cx.entryCodes C ++ escaped).eraseDups

end Ctx

/-! ## The flow -/

/-- Whether a store's key is one the site's records have: an array's
element, a numeric key of an array, its spine key `[]` at a computed key; a
record's key, `anyKey` at a computed one or an element. -/
def keyHeld (s : Site) (key : Option String) (element : Bool) : Bool :=
  let numeric := match key with
    | some k => !k.isEmpty && k.all Char.isDigit
    | none => false
  match s.kind with
  | .array => element || numeric || (match key with
    | some k => s.keys.contains k
    | none => s.keys.contains "[]")
  | _ => if element then s.anyKey else match key with
    | some k => s.keys.contains k || s.anyKey
    | none => s.anyKey

/-- **The flow's failures**, each attributed to the component of the code
it is of, or of every component (`none`) where it is a value's. -/
def flowDiags (cx : Ctx) : List (Option Nat × String × Span × String) := Id.run do
  let F := cx.F
  let mut out : List (Option Nat × String × Span × String) := []
  -- Values include what the statements make them include.
  for (v, i) in F.values.zipIdx do
    for x in v.sources do
      if !cx.has i (cx.eval x) then
        out := (none, v.module, v.pos, s!"the value at {v.pos.1}-{v.pos.2} omits what it includes") :: out
  -- Stores.
  let storeOk (receiver : Nat) (key : Option String) (element : Bool) (stored : Tokens) : Bool :=
    (cx.value receiver).sites.all fun t => match F.sites[t]? with
      | some s => cx.has s.contents stored && keyHeld s key element
      | none => false
  for s in F.stores do
    let stored := match s.stored with
      | some v => cx.value v
      | none => .empty
    if !storeOk s.receiver s.key s.element stored then
      out := (some s.component, s.module, s.place, "a store's receiver's sites omit what it stores, or the key it writes") :: out
    -- A key written to a value entering from outside is a key of every
    -- site exposed for that component.
    for c in (cx.value s.receiver).incoming do
      for (site, t) in F.sites.zipIdx do
        if cx.mark t c == some .exposed && !keyHeld { site with kind := .object } s.key false then
          out := (some s.component, s.module, s.place,
            s!"a key written to a value entering from outside is not a key of the exposed site {cx.siteName t}") :: out
  -- Calls.
  for c in F.calls do
    let callee := cx.value c.callee
    let direct := callee.sites.filterMap cx.codeAtSite.get?
    if !direct.all c.targets.contains then
      out := (some c.component, c.module, c.place, "a call omits a code its callee may be") :: out
    for ti in c.targets do
      match F.codes[ti]? with
      | none => pure ()
      | some code =>
        for (a, i) in c.args.zipIdx do
          let ok := if a.spread then code.params.all fun (p, _) => cx.has p (cx.read a.value)
            else match code.params[i]? with
              | some (p, _) => cx.has p (cx.value a.value)
              | none => true
          if !ok then out := (some c.component, c.module, a.place, "a parameter omits the argument a call passes it") :: out
        for r in c.receiver do
          if !cx.has code.receiver (cx.value r) then
            out := (some c.component, c.module, c.place, "a code's receiver omits a call's") :: out
        match c.inst with
        | some i => if !cx.has code.receiver ⟨[i], []⟩ then
            out := (some c.component, c.module, c.place, "a constructor's receiver omits the instance") :: out
        | none => if !cx.has c.result (cx.value code.result) then
            out := (some c.component, c.module, c.place, "a call's result omits its code's result") :: out
    for i in c.inst do
      if !cx.has c.result ⟨[i], []⟩ then out := (some c.component, c.module, c.place, "a `new` omits its instance") :: out
    if !cx.has c.result ⟨[], callee.incoming⟩ then
      out := (some c.component, c.module, c.place, "a call of outside code omits its result entering from outside") :: out
    let closures := callee.sites.any fun t => (F.sites[t]?).any (·.kind == .closure)
    let needsNative := c.targets.isEmpty && !closures && callee.incoming.isEmpty
    match c.native with
    | none => if needsNative then out := (some c.component, c.module, c.place, "a native's call states no native") :: out
    | some n =>
      let passed := c.args.foldl (fun acc a => acc.union (if a.spread then cx.read a.value else cx.value a.value)) .empty
      let given := ((c.receiver.map cx.value).getD .empty).union (cx.value n.passed)
      let callbacks := c.args.filter (!·.spread) |>.flatMap fun a =>
        (cx.value a.value).sites.filterMap fun t => cx.codeAtSite.get? t >>= (F.codes[·]?)
      let allOk := cx.has n.passed passed && cx.has n.given given && cx.has n.all ⟨[n.site], []⟩ && cx.has n.all (cx.value n.given) &&
        cx.has n.all (cx.read n.given) && callbacks.all (fun k => cx.has n.all (cx.value k.result) &&
          k.params.all fun (p, _) => cx.has p (cx.value n.all)) && cx.has c.result (cx.value n.all) &&
        (c.receiver.all fun r => (cx.value r).sites.all fun t => match F.sites[t]? with
          | some s => cx.has s.contents (cx.value n.passed) && keyHeld s none true
          | none => false)
      if !allOk then out := (some c.component, c.module, c.place, "a native's call omits what it may give or return") :: out
  -- Throws and catches.
  for t in F.throws do
    if !(F.thrown.any fun v => cx.has v (cx.value t.value)) then
      out := (some t.component, t.module, t.place, "the thrown values omit a throw's") :: out
  for k in F.catches do
    let ok := (F.thrown.all fun v => cx.has k.value (cx.value v)) && cx.has k.value ⟨[], cx.chain k.component⟩
    if !ok then out := (some k.component, k.module, k.place, "a caught value omits the thrown values or those entering from outside") :: out
  -- Members enter from outside.
  for C in List.range F.components.length do
    for m in cx.members C do
      match F.codes[m]? with
      | none => pure ()
      | some code =>
        for (p, place) in code.params do
          if !cx.has p ⟨[], [C]⟩ then
            out := (some C, code.module, place, "a member's parameter omits a value entering from outside") :: out
        if !code.arrow && !cx.has code.receiver ⟨[], [C]⟩ then
          out := (some C, code.module, code.pos, "a member's receiver omits a value entering from outside") :: out
  return out

/-! ## The crossings the events make -/

/-- A crossing the events make: its component, direction, position and
place, its value's tokens, and whether its position's type is the
crossing's to state (a parameter's, a result's, an argument's, an exported
binding's) or writable (a thrown value, a field of outside storage, a
binding outside code holds). -/
structure Made where
  component : Nat
  direction : Direction
  position : Position
  module : String
  place : Span
  tokens : Tokens
  typed : Bool

def crossings (cx : Ctx) : List Made := Id.run do
  let F := cx.F
  let mut out : List Made := []
  for C in List.range F.components.length do
    for m in cx.members C do
      for code in F.codes[m]?.toList do
        for ((p, place), i) in code.params.zipIdx do
          out := ⟨C, .into, .parameter code.pos i, code.module, place, cx.value p, true⟩ :: out
        out := ⟨C, .out, .result code.pos, code.module, code.pos, cx.value code.result, true⟩ :: out
  for c in F.calls do
    for C in (cx.value c.callee).incoming.eraseDups do
      for (a, i) in c.args.zipIdx do
        out := ⟨C, .out, .argument c.place i, c.module, a.place, if a.spread then cx.read a.value else cx.value a.value, true⟩ :: out
      out := ⟨C, .into, .callResult c.place, c.module, c.place, ⟨[], [C]⟩, true⟩ :: out
  for t in F.throws do
    for C in cx.chain t.component do
      out := ⟨C, .out, .thrown, t.module, t.place, cx.value t.value, false⟩ :: out
  for k in F.catches do
    for C in cx.chain k.component do
      out := ⟨C, .into, .caught, k.module, k.place, cx.value k.value, false⟩ :: out
  for s in F.stores do
    for C in (cx.value s.receiver).incoming.eraseDups do
      out := ⟨C, .out, .field s.key, s.module, s.place, (s.stored.map cx.value).getD .empty, false⟩ :: out
  for e in F.exports do
    for C in e.components do
      out := ⟨C, .out, .binding e.name, e.module, e.place, cx.value e.value, true⟩ :: out
  for h in F.holds do
    for t in (cx.value h.value).sites do
      for C in (F.sites[t]?).toList.flatMap (·.marks.map (·.1)) do
        if !(cx.chain h.component).contains C then
          out := ⟨C, .out, .binding h.name, h.module, h.place, cx.value h.value, false⟩ :: out
  return out

/-- The stated crossing of a made one: the same component, direction,
position, module and place. -/
def stated (F : Components) (x : Made) : Option Crossing :=
  F.crossings.find? fun y => y.component == x.component && y.direction == x.direction && y.position == x.position &&
    y.module == x.module && y.place == x.place

/-! ## (K), the marks -/

/-- **The sites a crossing out of `C` may not reach** (K): of the storage
reachable from its value, a local or internal site of `C`, and an exposed
one where its position is writable (`ro` false). -/
def crossBad (cx : Ctx) (C : Nat) (T : Tokens) (ro : Bool) : List Nat :=
  (cx.closure T).sites.filter fun t => match cx.mark t C with
    | some .local | some .internal => true
    | some .exposed => !ro
    | _ => false

/-- **The local sites storage of a site may not hold** (K): storage that is
not local holds no local storage. -/
def contentsBad (cx : Ctx) (t C : Nat) : List Nat :=
  match cx.mark t C with
  | some .local | none => []
  | some _ => (cx.contents t).sites.filter fun u => cx.mark u C == some .local

/-- **The marks' failures** (K). -/
def marksDiags (cx : Ctx) : List Diag := Id.run do
  let F := cx.F
  let mut out : List Diag := []
  -- One mark per enclosing component, innermost first, each at most the
  -- nested one's.
  for (s, t) in F.sites.zipIdx do
    match s.marks with
    | [] => out := ⟨0, "K", s.module, s.pos, "a site has no mark"⟩ :: out
    | (c, _) :: _ =>
      if s.marks.map (·.1) != cx.chain c then
        out := ⟨c, "K", s.module, s.pos, "a site's marks are not one per component enclosing its code"⟩ :: out
      for ((C, m), (D, n)) in (s.marks.drop 1).zip s.marks do
        if m.rank > n.rank then
          out := ⟨C, "K", s.module, s.pos,
            s!"the site's mark for component {C}, {markName m}, exceeds its mark {markName n} for component {D} nested in it"⟩ :: out
      -- Storage that is not local holds no local storage.
      for (C, m) in s.marks do
        for u in contentsBad cx t C do
          out := ⟨C, "K", s.module, s.pos, s!"{markName m} storage holds the local site {cx.siteName u}"⟩ :: out
  -- Every crossing stated; a crossing out reaches no local or internal site,
  -- an exposed one only at a read-only position.
  for x in crossings cx do
    match stated F x with
    | none =>
      out := ⟨x.component, "K", x.module, x.place, "a crossing of the component's code is not stated"⟩ :: out
    | some y =>
      if x.direction == .out then
        for t in crossBad cx x.component x.tokens (x.typed && y.readOnly) do
          match cx.mark t x.component with
          | some .exposed =>
            out := ⟨x.component, "K", x.module, x.place,
              s!"a value crossing out at a writable position reaches the exposed site {cx.siteName t}"⟩ :: out
          | m =>
            out := ⟨x.component, "K", x.module, x.place,
              s!"a value crossing out reaches the {(m.map markName).getD ""} site {cx.siteName t}"⟩ :: out
  -- A binding a module or a closure holds reaches no local storage of the
  -- components it is held in.
  for h in F.holds do
    for t in (cx.closure (cx.value h.value)).sites do
      for C in cx.chain h.component do
        if cx.mark t C == some .local then
          out := ⟨C, "K", h.module, h.place, s!"the binding {h.name} holds the local site {cx.siteName t}"⟩ :: out
  return out

/-! ## (O), the stores -/

/-- **The sites an install into `C`'s protected storage may not reach**
(O): of the storage reachable from the stored value, a site of `C` neither
local nor exposed, and storage of code outside `C`. -/
def installBad (cx : Ctx) (C : Nat) (stored : Tokens) : List Nat :=
  (cx.closure stored).sites.filter fun t => match cx.mark t C with
    | some .local | some .exposed => false
    | _ => true

/-- **A store into storage of `C` that may be protected**: a local or an
exposed site's, a released site's but a field's initial value in the record
it allocates, or a value entering `C` from outside. -/
def protectedInto (cx : Ctx) (C : Nat) (r : Tokens) (initial : Bool) : Bool :=
  r.incoming.contains C && !initial || r.sites.any fun t => match cx.mark t C with
    | some .local | some .exposed => true
    | some .released => !initial
    | _ => false

/-- The stores of the family's code with their values' tokens: each store,
and each native's write of what its arguments pass into its receiver. -/
def stores (cx : Ctx) : List (Nat × String × Span × Nat × Tokens × Bool) :=
  cx.F.stores.map (fun s => (s.component, s.module, s.place, s.receiver, (s.stored.map cx.value).getD .empty, s.initial)) ++
  cx.F.calls.filterMap fun c => do
    let n ← c.native
    let r ← c.receiver
    return (c.component, c.module, c.place, r, cx.value n.passed, false)

/-- **The ownership failures** (O): a store into storage that may be
protected, of a value whose reachable storage is not all of the
component's local or exposed sites. -/
def ownershipDiags (cx : Ctx) : List Diag := Id.run do
  let mut out : List Diag := []
  for (k, module, place, receiver, stored, initial) in stores cx do
    let r := cx.value receiver
    for C in cx.chain k do
      if protectedInto cx C r initial then
        let reach := cx.closure stored
        for t in installBad cx C stored do
          match cx.mark t C with
          | some m => out := ⟨C, "O", module, place,
              s!"a store into storage that may be protected installs the {markName m} site {cx.siteName t}"⟩ :: out
          | none => out := ⟨C, "O", module, place,
              s!"a store into storage that may be protected installs storage of code outside the component, {cx.siteName t}"⟩ :: out
        if !reach.incoming.isEmpty then
          out := ⟨C, "O", module, place, "a store into storage that may be protected installs a value entering from outside"⟩ :: out
  return out

/-! ## (S), no suspension -/

/-- **The suspensions' failures** (S): each suspension the description
states, at every component enclosing it, and each async function of the
checked file (`fns`, by name and the span of its name) no stated async
suspension contains. -/
def suspensionDiags (cx : Ctx) (file : String) (fns : List (String × Span × Bool)) : List Diag := Id.run do
  let F := cx.F
  let mut out : List Diag := []
  for x in F.suspensions do
    let what := match x.kind with
      | .await => "an `await`"
      | .yield => "a `yield`"
      | .async => "an async function"
      | .generator => "a generator"
    for C in cx.chain x.component do
      out := ⟨C, "S", x.module, x.place, s!"{what} in the component's code"⟩ :: out
  for (name, pos, async) in fns do
    if async && !(F.suspensions.any fun x => x.kind == .async && x.module == file && x.place.1 ≤ pos.1 && pos.2 ≤ x.place.2) then
      -- The code it is: the innermost described code containing it, else
      -- the checked file's module.
      let owner := F.codes.filter (fun c => c.module == file && c.pos.1 ≤ pos.1 && pos.2 ≤ c.pos.2)
        |>.foldl (fun (b : Option Code) c => match b with
          | some b => if c.pos.2 - c.pos.1 < b.pos.2 - b.pos.1 then some c else some b
          | none => some c) none
      let comp := match owner with
        | some c => some c.component
        | none => (F.components.zipIdx.find? fun (k : Component × Nat) => k.1.kind == ComponentWire.Kind.module && k.1.location == file).map
            (fun (k : Component × Nat) => k.2)
      for c in comp.toList do
        for C in cx.chain c do
          out := ⟨C, "S", file, pos, s!"the async function {name} states no suspension"⟩ :: out
  return out

/-! ## The outcome -/

/-- **Each component's outcome**: its kind, its location and the failures
refusing its certificate, each once. -/
def familyOutcome (F : Components) (file : String) (fns : List (String × Span × Bool)) :
    List (Nat × Component × List String) :=
  let cx := Ctx.of F
  let flow := flowDiags cx
  let diags := suspensionDiags cx file fns ++ marksDiags cx ++ ownershipDiags cx
  F.components.zipIdx.map fun (k, C) =>
    let own := flow.filterMap fun (c, module, place, message) =>
      if c.all (cx.chain · |>.contains C) then some s!"(flow) {module} {place.1}-{place.2}: {message}" else none
    (C, k, (own ++ (diags.filter (·.component == C)).map Diag.render).eraseDups)

def kindName : ComponentWire.Kind → String
  | .package => "package"
  | .module => "module"
  | .klass => "class"

end Verification.ComponentChecks
