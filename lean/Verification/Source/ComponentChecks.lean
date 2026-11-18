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
  protected (an exposed site's, a local site's where a guarantee candidate's
  possible support may read it, a released site's but its initial values
  and storage no crossing can have reached, a value entering from outside)
  stores a value all of whose reachable storage is of the component's local
  or exposed sites.
- **Ψ, the protocol** (`protocolDiags`): the front's proposed protocol of
  each component covers the charges of every write of its code (the parts
  it may change in the component's region, by what), a write into storage
  fresh in its frame charging nothing.
- **G, the guarantee** (`Ctx.guarantee`): each type invariant of the family
  with the writes of the component's code that change its support beyond
  the client obligation, construction aside; kept where there is none.

Nothing in acceptance reads the outcome (`familyOutcome`): the verifier
prints it beside the units' verdicts (`WorkerWire.componentOutcome`). -/
namespace Verification.ComponentChecks
open ComponentWire

/-- A value's tokens: its possible sites and the components it may enter
from outside. -/
structure Tokens where
  sites : List Nat
  incoming : List Nat
  /-- The components it may enter from outside reached read-only from a
  crossing in at a read-only type. -/
  ro : List Nat
  deriving Inhabited

def Tokens.empty : Tokens := ⟨[], [], []⟩

def Tokens.union (a b : Tokens) : Tokens := ⟨a.sites ++ b.sites, a.incoming ++ b.incoming, a.ro ++ b.ro⟩

def Tokens.ofSites (s : List Nat) : Tokens := ⟨s, [], []⟩

def Tokens.writable (cs : List Nat) : Tokens := ⟨[], cs, []⟩

/-- The components a value may enter from outside, at either position. -/
def Tokens.components (t : Tokens) : List Nat := (t.incoming ++ t.ro).eraseDups

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
  readOnlyOf : Array (Std.HashSet Nat)
  /-- The code each closure site is, by site. -/
  codeAtSite : Std.HashMap Nat Nat
  /-- The sites that may escape their frames (`Ctx.escaping`), once
  computed. -/
  escaped : Std.HashSet Nat := {}

def Ctx.of (F : Components) : Ctx :=
  { F, sitesOf := (F.values.map fun v => Std.HashSet.ofList v.sites).toArray,
    incomingOf := (F.values.map fun v => Std.HashSet.ofList v.incoming).toArray,
    readOnlyOf := (F.values.map fun v => Std.HashSet.ofList v.incomingReadOnly).toArray,
    codeAtSite := F.codes.zipIdx.foldl (fun m (c, i) => match c.site with
      | some s => m.insert s i
      | none => m) {} }

namespace Ctx
variable (cx : Ctx)

def value (v : Nat) : Tokens := match cx.F.values[v]? with
  | some x => ⟨x.sites, x.incoming, x.incomingReadOnly⟩
  | none => .empty

def contents (t : Nat) : Tokens := match cx.F.sites[t]? with
  | some s => cx.value s.contents
  | none => .empty

/-- What a value's storage holds: its sites' contents, and of a value
entering from outside, a value entering from outside, read-only where it is
reached read-only. -/
def read (v : Nat) : Tokens :=
  let x := cx.value v
  ⟨x.sites.flatMap (cx.contents · |>.sites), x.incoming ++ x.sites.flatMap (cx.contents · |>.incoming),
    x.ro ++ x.sites.flatMap (cx.contents · |>.ro)⟩

def eval : Source → Tokens
  | .site s => .ofSites [s]
  | .value v => cx.value v
  | .read v => cx.read v
  | .incoming c => .writable [c]
  | .incomingReadOnly c => ⟨[], [], [c]⟩

/-- Whether value `v` includes the tokens `t`. -/
def has (v : Nat) (t : Tokens) : Bool :=
  match cx.sitesOf[v]?, cx.incomingOf[v]?, cx.readOnlyOf[v]? with
  | some s, some i, some r => t.sites.all s.contains && t.incoming.all i.contains && t.ro.all r.contains
  | _, _, _ => t.sites.isEmpty && t.incoming.isEmpty && t.ro.isEmpty

/-- **The storage reachable from tokens**: their sites and every site the
contents of a reachable site hold, with the components a value of them may
enter from outside. -/
def closure (start : Tokens) : Tokens := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut out : Array Nat := #[]
  let mut incoming : Std.HashSet Nat := Std.HashSet.ofList start.incoming
  let mut ro : Std.HashSet Nat := Std.HashSet.ofList start.ro
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
        for i in c.ro do ro := ro.insert i
    work := next
  return ⟨out.toList, incoming.toList, ro.toList⟩

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

/-- **A shape read-only throughout** (the draft, "Read-only types and
crossings"; `shapeReadOnly` in `tools/components.mts` states the same): a
primitive, `unknown` or a sealed handle; a read-only array or tuple of such
shapes; a record whose every member is a `readonly` field of such a shape; a
union or an intersection of such shapes; a named type whose definition is
one, a recursive reference read as writable. `fuel` bounds the nesting and
the named types expanded, exhausted read as writable. -/
def readOnlyShape (types : List TypeRow) : Nat → List Nat → ComponentWire.Shape → Bool
  | 0, _, _ => false
  | n + 1, vis, s => match s with
    | .primitive | .unknown | .sealed => true
    | .function | .other | .array _ => false
    | .readonlyArray e => readOnlyShape types n vis e
    | .tuple ro es => ro && es.attach.all fun ⟨e, _⟩ => readOnlyShape types n vis e
    | .record ms => ms.attach.all fun ⟨(r, f, t), _⟩ => r && f && readOnlyShape types n vis t
    | .union ps | .inter ps => ps.attach.all fun ⟨e, _⟩ => readOnlyShape types n vis e
    | .named i => !vis.contains i && match types[i]? with
      | some r => readOnlyShape types n (i :: vis) r.definition
      | none => false

/-- Whether a position of the declared shape `t` is read-only throughout; a
position with no declared type is writable. -/
def Ctx.readOnly (cx : Ctx) : Option ComponentWire.Shape → Bool
  | some t => readOnlyShape cx.F.types (ComponentWire.shapeLimit * (cx.F.types.length + 1)) [] t
  | none => false

/-- **A call of a method of the standard library**, as TypeScript resolves
it: that native's, of its arrays whatever its receiver's value (the array
invariant, `DESIGN.md`, "Trust surface"), of another interface where its
receiver is the family's own storage with no key of its name (checked in
`flowDiags`); no code of the family and no outside code runs. -/
def _root_.Verification.ComponentWire.Call.member (c : Call) : Bool := c.native.any (·.member)

/-- The callee's components it may enter from, of a call that may run
outside code. -/
def Ctx.outsideOf (cx : Ctx) (c : Call) : List Nat := if c.member then [] else (cx.value c.callee).components

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
    for c in (cx.value s.receiver).components do
      for (site, t) in F.sites.zipIdx do
        if cx.mark t c == some .exposed && !keyHeld { site with kind := .object } s.key false then
          out := (some s.component, s.module, s.place,
            s!"a key written to a value entering from outside is not a key of the exposed site {cx.siteName t}") :: out
  -- Calls.
  for c in F.calls do
    let callee := cx.value c.callee
    let direct := callee.sites.filterMap cx.codeAtSite.get?
    if !c.member && !direct.all c.targets.contains then
      out := (some c.component, c.module, c.place, "a call omits a code its callee may be") :: out
    for ti in c.targets do
      match F.codes[ti]? with
      | none => pure ()
      | some code =>
        for (a, i) in c.args.zipIdx do
          let ok := if a.spread then code.params.all fun (p, _, _) => cx.has p (cx.read a.value)
            else match code.params[i]? with
              | some (p, _, _) => cx.has p (cx.value a.value)
              | none => true
          if !ok then out := (some c.component, c.module, a.place, "a parameter omits the argument a call passes it") :: out
        for r in c.receiver do
          if !cx.has code.receiver (cx.value r) then
            out := (some c.component, c.module, c.place, "a code's receiver omits a call's") :: out
        match c.inst with
        | some i => if !cx.has code.receiver (.ofSites [i]) then
            out := (some c.component, c.module, c.place, "a constructor's receiver omits the instance") :: out
        | none => if !cx.has c.result (cx.value code.result) then
            out := (some c.component, c.module, c.place, "a call's result omits its code's result") :: out
    for i in c.inst do
      if !cx.has c.result (.ofSites [i]) then out := (some c.component, c.module, c.place, "a `new` omits its instance") :: out
    if !cx.has c.result (.writable (cx.outsideOf c)) then
      out := (some c.component, c.module, c.place, "a call of outside code omits its result entering from outside") :: out
    let closures := callee.sites.any fun t => (F.sites[t]?).any (·.kind == .closure)
    let needsNative := c.member || c.targets.isEmpty && !closures && callee.components.isEmpty
    match c.native with
    | none => if needsNative then out := (some c.component, c.module, c.place, "a native's call states no native") :: out
    | some n =>
      let passed := c.args.foldl (fun acc a => acc.union (if a.spread then cx.read a.value else cx.value a.value)) .empty
      let given := ((c.receiver.map cx.value).getD .empty).union (cx.value n.passed)
      let callbacks := c.args.filter (!·.spread) |>.flatMap fun a =>
        (cx.value a.value).sites.filterMap fun t => cx.codeAtSite.get? t >>= (F.codes[·]?)
      -- A fresh result is the array it allocates, holding what the arguments
      -- pass and what is reachable from the elements of what it is given and
      -- from its callbacks' results; any other result may be any of what it
      -- may return, its own storage holding them.
      let resultOk := match F.sites[n.site]? with
        | none => false
        | some site =>
          if n.member && n.array && n.fresh then cx.has c.result (.ofSites [n.site]) && (n.primitiveElements || cx.has site.contents passed &&
            cx.has site.contents (cx.closure (cx.read n.given)) &&
            callbacks.all (fun k => cx.has site.contents (cx.closure (cx.value k.result))))
          else cx.has c.result (cx.value n.all) && cx.has site.contents (cx.value n.all)
      let allOk := cx.has n.passed passed && cx.has n.given given && cx.has n.all (.ofSites [n.site]) && cx.has n.all (cx.value n.given) &&
        cx.has n.all (cx.read n.given) && callbacks.all (fun k => cx.has n.all (cx.value k.result) &&
          k.params.all fun (p, _, _) => cx.has p (cx.value n.all)) && resultOk &&
        (c.receiver.all fun r => (cx.value r).sites.all fun t => match F.sites[t]? with
          | some s => cx.has s.contents (cx.value n.passed) && (n.member || keyHeld s none true)
          | none => false)
      if !allOk then out := (some c.component, c.module, c.place, "a native's call omits what it may give or return") :: out
      -- A method of another library interface is that native's only of the
      -- family's own storage, no record of which may own its name.
      if n.member && !n.array then
        let r := (c.receiver.map cx.value).getD .empty
        let owns := r.sites.any fun t => match F.sites[t]? with
          | some s => s.anyKey || n.name.any s.keys.contains
          | none => true
        if c.receiver.isNone || !r.components.isEmpty || owns then
          out := (some c.component, c.module, c.place,
            "a call read as a library method's whose receiver may come from outside or own the method") :: out
  -- Throws and catches.
  for t in F.throws do
    if !(F.thrown.any fun v => cx.has v (cx.value t.value)) then
      out := (some t.component, t.module, t.place, "the thrown values omit a throw's") :: out
  for k in F.catches do
    let ok := (F.thrown.all fun v => cx.has k.value (cx.value v)) && cx.has k.value (.writable (cx.chain k.component))
    if !ok then out := (some k.component, k.module, k.place, "a caught value omits the thrown values or those entering from outside") :: out
  -- Members enter from outside.
  for C in List.range F.components.length do
    for m in cx.members C do
      match F.codes[m]? with
      | none => pure ()
      | some code =>
        for (p, place, ty) in code.params do
          -- A parameter of a read-only type is reached read-only throughout.
          if !cx.has p (if cx.readOnly ty then ⟨[], [], [C]⟩ else .writable [C]) then
            out := (some C, code.module, place, "a member's parameter omits a value entering from outside") :: out
        if !code.arrow && !cx.has code.receiver (.writable [C]) then
          out := (some C, code.module, code.pos, "a member's receiver omits a value entering from outside") :: out
  return out

/-! ## The crossings the events make -/

/-- A crossing the events make: its component, direction, position and
place, its value's tokens, and whether its position is read-only, derived
from its declared type (a parameter's, a result's, an argument's of a
callee of declared parameter types, an exported binding's), a thrown value,
a caught one, a field of outside storage and a binding outside code holds
being writable. -/
structure Made where
  component : Nat
  direction : Direction
  position : Position
  module : String
  place : Span
  tokens : Tokens
  ro : Bool

def crossings (cx : Ctx) : List Made := Id.run do
  let F := cx.F
  let mut out : List Made := []
  for C in List.range F.components.length do
    for m in cx.members C do
      for code in F.codes[m]?.toList do
        for ((p, place, ty), i) in code.params.zipIdx do
          out := ⟨C, .into, .parameter code.pos i, code.module, place, cx.value p, cx.readOnly ty⟩ :: out
        out := ⟨C, .out, .result code.pos, code.module, code.pos, cx.value code.result, cx.readOnly code.resultType⟩ :: out
  for c in F.calls do
    for C in cx.outsideOf c do
      for (a, i) in c.args.zipIdx do
        out := ⟨C, .out, .argument c.place i, c.module, a.place, if a.spread then cx.read a.value else cx.value a.value,
          cx.readOnly a.type⟩ :: out
      out := ⟨C, .into, .callResult c.place, c.module, c.place, .writable [C], false⟩ :: out
  for t in F.throws do
    for C in cx.chain t.component do
      out := ⟨C, .out, .thrown, t.module, t.place, cx.value t.value, false⟩ :: out
  for k in F.catches do
    for C in cx.chain k.component do
      out := ⟨C, .into, .caught, k.module, k.place, cx.value k.value, false⟩ :: out
  for s in F.stores do
    let r := cx.value s.receiver
    for C in r.components do
      -- A field of a value reached read-only from a crossing in at a
      -- read-only type is a read-only position.
      out := ⟨C, .out, .field s.key, s.module, s.place, (s.stored.map cx.value).getD .empty,
        r.ro.contains C && !r.incoming.contains C⟩ :: out
  for e in F.exports do
    for C in e.components do
      out := ⟨C, .out, .binding e.name, e.module, e.place, cx.value e.value, cx.readOnly e.type⟩ :: out
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
      if y.readOnly != x.ro then
        out := ⟨x.component, "K", x.module, x.place,
          s!"the crossing states its position {if y.readOnly then "read-only" else "writable"}, its declared type is {if x.ro then "read-only" else "writable"}"⟩ :: out
      if x.direction == .out then
        for t in crossBad cx x.component x.tokens x.ro do
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

/-! ## Frames: fresh storage and outside code -/

/-- **The innermost code containing a place** of a module. -/
def Ctx.codeAt (cx : Ctx) (module : String) (place : Span) : Option Nat :=
  cx.F.codes.zipIdx.foldl (fun (b : Option (Nat × Nat)) (c, i) =>
    if c.module == module && c.pos.1 ≤ place.1 && place.2 ≤ c.pos.2 then
      match b with
      | some (_, w) => if c.pos.2 - c.pos.1 < w then some (i, c.pos.2 - c.pos.1) else b
      | none => some (i, c.pos.2 - c.pos.1)
    else b) none |>.map (·.1)

/-- The values whose contents a frame receives from another code: each
code's parameters, receiver and result, and each caught value. -/
def Ctx.boundaryValues (cx : Ctx) : Std.HashSet Nat :=
  let codes := cx.F.codes.flatMap fun c => c.receiver :: c.result :: c.params.map (·.1)
  Std.HashSet.ofList (codes ++ cx.F.catches.map (·.value))

/-- A call's code, whether it runs outside code itself (a callee that may
enter from outside, a native given a value from outside where it may call
it), and the codes it may run. -/
def Ctx.callSteps (cx : Ctx) : List (Option Nat × Call × Bool × List Nat) :=
  cx.F.calls.map fun c =>
    let given := (c.receiver.toList ++ c.args.map (·.value)).map cx.value
    let callbacks := given.flatMap fun t => t.sites.filterMap cx.codeAtSite.get?
    let calls := if c.member then
        (c.args.zipIdx.filter fun (a, j) => a.spread || ((c.native.bind (·.calls[j]?)).getD true)).map
          fun (a, _) => cx.value a.value
      else given
    (cx.codeAt c.module c.place, c, !(cx.outsideOf c).isEmpty ||
      c.native.isSome && calls.any (fun t => !(cx.closure t).components.isEmpty), c.targets ++ callbacks)

/-- **The codes that may run code outside the family** (a fixed point over
the calls): a code making a call whose callee may enter from outside, a
call of a native given a value that may enter from outside where it may
call it (a standard library method at each argument its declaration does
not type by a type parameter or a primitive, and at each spread argument,
which it iterates; any other native at every position), or a call that may
run such a code, a closure a native is given among them. -/
def Ctx.runsOutside (cx : Ctx) : Std.HashSet Nat := Id.run do
  let located := cx.callSteps
  let mut out : Std.HashSet Nat := {}
  for _ in [0:cx.F.codes.length + 1] do
    for (k, _, runs, next) in located do
      for i in k do
        if !out.contains i && (runs || next.any out.contains) then out := out.insert i
  return out

/-- **The parameter of the code `i` a call calls**: its callee the value of
that parameter, which no statement assigns (its sources none). -/
def Ctx.paramCallee (cx : Ctx) (i : Nat) (c : Call) : Option Nat := do
  let code ← cx.F.codes[i]?
  let callee ← cx.F.values[c.callee]?
  match callee.sources with
  | [.value p] =>
    let j ← code.params.findIdx? (·.1 == p)
    if (cx.F.values[p]?).any (·.sources.isEmpty) then some j else none
  | _ => none

/-- The parameters of the code `t` some call of its calls. -/
def Ctx.calls (cx : Ctx) (t : Nat) : List Nat :=
  (cx.F.calls.filterMap fun c => match cx.codeAt c.module c.place with
    | some i => if i == t then cx.paramCallee t c else none
    | none => none).eraseDups

/-- **The codes that may run outside code other than by calling their own
parameters** (a fixed point): `runsOutside` with each call of an unassigned
parameter of the calling code left out, its argument being the caller's. -/
def Ctx.runsOutsideBut (cx : Ctx) (outside : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  let mut out : Std.HashSet Nat := {}
  for (k, c, runs, next) in cx.callSteps do
    for i in k do
      if (cx.paramCallee i c).isNone && (runs || next.any outside.contains) then out := out.insert i
  return out

/-- **The quiet codes**: a code each of whose calls runs no outside code
itself and may run only codes that run none, or that run outside code
only by calling their parameters and are given at each parameter they call
a value that enters from no outside code and is codes running none. A frame
of a quiet code, and every frame its calls create, runs no outside code. -/
def Ctx.quiet (cx : Ctx) (outside : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  let but := cx.runsOutsideBut outside
  let steps := cx.callSteps
  let quietValue (v : Nat) : Bool :=
    let t := cx.value v
    t.components.isEmpty && t.sites.all fun s => match cx.codeAtSite.get? s with
      | some k => !outside.contains k
      | none => false
  let callOk (c : Call) (runs : Bool) (next : List Nat) : Bool :=
    !runs && next.all fun t => !outside.contains t || (!but.contains t &&
      (cx.calls t).all fun j => (c.args[j]?).all fun a => !a.spread && quietValue a.value)
  let mut bad : Std.HashSet Nat := {}
  for (k, c, runs, next) in steps do
    for i in k do
      if !callOk c runs next then bad := bad.insert i
  return Std.HashSet.ofList ((List.range cx.F.codes.length).filter (!bad.contains ·))

/-- **The code immediately enclosing a code**: the innermost other code of
its module whose span contains its own. -/
def Ctx.parentCode (cx : Ctx) (k : Nat) : Option Nat := do
  let c ← cx.F.codes[k]?
  let (i, _) ← cx.F.codes.zipIdx.foldl (fun (b : Option (Nat × Nat)) (d, i) =>
    if i != k && d.module == c.module && d.pos.1 ≤ c.pos.1 && c.pos.2 ≤ d.pos.2 then
      match b with
      | some (_, w) => if d.pos.2 - d.pos.1 < w then some (i, d.pos.2 - d.pos.1) else b
      | none => some (i, d.pos.2 - d.pos.1)
    else b) none
  return i

/-- **The sites some storage holds, some code returns, some code throws,
some binding of a module or a closure holds, some module exports, some
store writes, or some native or outside code is given** (`confined`). -/
def Ctx.escaping (cx : Ctx) : Std.HashSet Nat :=
  let F := cx.F
  let vs : List Nat := F.sites.map (·.contents) ++ F.codes.map (·.result) ++ F.thrown.toList ++
    F.throws.map (·.value) ++ F.holds.map (·.value) ++ F.exports.map (·.value) ++ F.stores.filterMap (·.stored) ++
    F.calls.flatMap fun c => if c.native.isSome || !(cx.outsideOf c).isEmpty then c.receiver.toList ++ c.args.map (·.value) else []
  Std.HashSet.ofList (vs.flatMap fun v => (cx.value v).sites)

/-- **A closure confined to the frames that hold it**: its site is local or
internal for every component, and none of `escaping`: no storage holds it,
no code returns it, no code throws it, no binding of a module or a closure
holds it, no module exports it, no store writes it, no native is given it
and no outside code is passed it. It is then called only while a frame of
the code that created it is active: the frames holding it are that frame's
and those of the calls it makes. -/
def Ctx.confined (cx : Ctx) (escaping : Std.HashSet Nat) (k : Nat) : Bool :=
  match (cx.F.codes[k]?).bind (·.site) with
  | none => false
  | some s => !escaping.contains s && (cx.F.sites[s]?).any fun x => x.marks.all fun (_, m) => m == .local || m == .internal

/-- **A value fresh in a frame of the codes `scope`**: every location it may
hold was allocated by a frame of one of them, the first frame of the last
code and those its call creates. It is no value a frame receives from
another code (a parameter, a receiver, a result, a caught value), enters
from no outside code, is computed in a code of `scope`, and each of its
possible sites is of a code of `scope`; it is the result of a call in such a
code of a standard array method whose reviewed contract allocates its
result, or every source of it is a site of such a code or another such
value. -/
def Ctx.freshIn (cx : Ctx) (boundary : Std.HashSet Nat) (scope : List Nat) : Nat → Nat → Bool
  | 0, _ => false
  | n + 1, v => match cx.F.values[v]? with
    | none => false
    | some x =>
      let inScope (o : Option Nat) : Bool := o.any scope.contains
      let siteIn (t : Nat) : Bool := match cx.F.sites[t]? with
        | some s => inScope (cx.codeAt s.module s.pos)
        | none => false
      x.incoming.isEmpty && x.incomingReadOnly.isEmpty && !boundary.contains v && inScope (cx.codeAt x.module x.pos) &&
      x.sites.all siteIn &&
      match cx.F.calls.find? (·.result == v) with
      | some c => inScope (cx.codeAt c.module c.place) && c.native.any fun nt => nt.member && nt.array && nt.fresh
      | none => !x.sources.isEmpty && x.sources.all fun
        | .site t => siteIn t
        | .value u => cx.freshIn boundary scope n u
        | _ => false

/-- **The scope a value is fresh in at a place**: the frame of the code at
the place, or, through closures confined to their frames (`confined`), the
frame of an enclosing code. A store of a confined closure runs while a
frame of the code that created it is active, and inside every call of a
component from outside code that the store is in, since outside code holds
no confined closure. -/
def Ctx.freshScope (cx : Ctx) (boundary : Std.HashSet Nat) (module : String) (place : Span) (v : Nat) :
    Option (List Nat) :=
  match cx.codeAt module place with
  | none => none
  | some k =>
    let fuel := cx.F.values.length + 1
    let rec up : Nat → Nat → List Nat → Option (List Nat)
      | 0, _, _ => none
      | n + 1, cur, scope =>
        if cx.freshIn boundary scope fuel v then some scope
        else if cx.confined cx.escaped cur then match cx.parentCode cur with
          | some p => up n p (p :: scope)
          | none => none
        else none
    up (cx.F.codes.length + 1) k [k]

/-- Whether a value is fresh at a place (`freshScope`). -/
def Ctx.freshAt (cx : Ctx) (boundary : Std.HashSet Nat) (module : String) (place : Span) (v : Nat) : Bool :=
  (cx.freshScope boundary module place v).isSome

/-- **A store into storage its frame allocated before any outside code
could run**: its receiver fresh at the store in a scope of quiet codes
(`quiet`). No outside code runs in those frames, so no crossing into a
component can have reached the storage, and no history protects it. -/
def Ctx.unreached (cx : Ctx) (boundary quiet : Std.HashSet Nat) (module : String) (place : Span)
    (receiver : Nat) : Bool :=
  (cx.freshScope boundary module place receiver).any (·.all quiet.contains)

/-! ## The protocol Ψ and the guarantee G -/

/-- **A charge** (the draft, "The protocol"): a write may change the part
of the site `site` (`none` storage of code outside the component) of kind
`kind`, at the key `key` of a field part (`none` every key), by `change`. -/
structure Charge where
  site : Option Nat
  kind : PartKind
  key : Option String
  change : Footprints.Change
  deriving Repr

def partKindName : PartKind → String
  | .field => "fields"
  | .spine => "spines"
  | .cell => "cells"

def changeName : Footprints.Change → String
  | .keep => "keep"
  | .init => "init"
  | .scalar => "scalar"
  | .extend => "extend"
  | .grow => "grow"
  | .any => "any"

def Ctx.partName (cx : Ctx) (site : Option Nat) (kind : PartKind) (key : Option String) : String :=
  let where_ := match site with
    | some t => s!"the site {cx.siteName t}"
    | none => "storage of code outside the component"
  let k := match kind, key with
    | .field, some k => s!" at {k}"
    | .field, none => " at every key"
    | _, _ => ""
  s!"the {partKindName kind} of {where_}{k}"

/-- **The storage a write to a value may change in `C`'s protected
region**: its possible sites exposed or released for `C` (a local site's
storage that a call of `C` from outside code writes is storage the call
allocated, which its frames alone hold, by (K); an internal site's is never
in the region), and, where it may enter `C` from outside, every exposed and
released site of `C` and storage of code outside `C` (the draft, *Incoming
values*). -/
def Ctx.targets (cx : Ctx) (C : Nat) (r : Tokens) : List (Option Nat) :=
  let lent (t : Nat) : Bool := match cx.mark t C with
    | some .exposed | some .released => true
    | _ => false
  let own := (r.sites.filter lent).map some
  if r.components.contains C then
    own ++ ((List.range cx.F.sites.length).filter lent).map some ++ [none]
  else own

/-- **The parts a store changes at one target, and by what**: a field at
its key (every key at a computed one), and of an array an element's cell
and the spine, which an element's write may lengthen (`grow`, keeping each
dense prefix) and a write of no value (`delete`, an update) or of `length`
may change arbitrarily. Every field and cell write is `any`. A native's
site, and storage of code outside `C`, may be a record or an array. -/
def storeParts (kind : Option SiteKind) (key : Option String) (element : Bool) (valued : Bool) :
    List (PartKind × Option String × Footprints.Change) :=
  let numeric := match key with
    | some k => !k.isEmpty && k.all Char.isDigit
    | none => false
  let arr : List (PartKind × Option String × Footprints.Change) :=
    if element || numeric then [(.cell, none, .any), (.spine, none, if valued then .grow else .any)]
    else match key with
      | some "length" => [(.spine, none, .any)]
      | some k => [(.field, some k, .any)]
      | none => [(.cell, none, .any), (.spine, none, .any), (.field, none, .any)]
  let rec_ : List (PartKind × Option String × Footprints.Change) :=
    if element then [(.field, none, .any)] else [(.field, key, .any)]
  match kind with
  | some .array => arr
  | some .native | none => arr ++ rec_
  | some _ => rec_

/-- **A native's change of its receiver**: its spine, its cells and its
fields at every key, arbitrarily. The reviewed contracts of the standard
library's methods state no exceptional effect (`onThrow`), so at a throw
every location they reach may change. -/
def nativeParts : List (PartKind × Option String × Footprints.Change) :=
  [(.spine, none, .any), (.cell, none, .any), (.field, none, .any)]

/-- A write of the family's code: its component, module and place, its
receiver's value, the parts it changes at a target of a site kind, and
whether it is an initial value of the record it allocates. -/
structure Write where
  component : Nat
  module : String
  place : Span
  receiver : Nat
  parts : Option SiteKind → List (PartKind × Option String × Footprints.Change)
  initial : Bool
  /-- The value written: a store's (`none` a primitive), what a native's
  arguments pass. -/
  stored : Option Nat

/-- **The family's writes**: each store, and each native's call with a
receiver. -/
def Ctx.writes (cx : Ctx) : List Write :=
  cx.F.stores.map (fun s => ⟨s.component, s.module, s.place, s.receiver,
    fun k => storeParts k s.key s.element s.stored.isSome, s.initial, s.stored⟩) ++
  cx.F.calls.filterMap fun c => do
    let n ← c.native
    let r ← c.receiver
    return ⟨c.component, c.module, c.place, r, fun _ => nativeParts, false, some n.passed⟩

/-- **A write's charges to `C`**: none for an initial value (the record is
allocated by the write) or a receiver fresh in its frame (`freshIn`: storage
allocated after the entry of every call of `C` the write is in); else each
part it changes at each target. -/
def Ctx.chargesOf (cx : Ctx) (C : Nat) (w : Write) : List Charge :=
  if w.initial then []
  else (cx.targets C (cx.value w.receiver)).flatMap fun t =>
    (w.parts (t.bind fun i => (cx.F.sites[i]?).map (·.kind))).map fun (k, key, δ) => ⟨t, k, key, δ⟩

def Ctx.charges (cx : Ctx) (boundary : Std.HashSet Nat) (C : Nat) (w : Write) : List Charge :=
  if cx.freshAt boundary w.module w.place w.receiver then [] else cx.chargesOf C w

/-- **A proposed protocol covers a charge**: an entry at its site and kind,
at its key or every key, with a change at least its. -/
def covers (entries : List ProtocolEntry) (ch : Charge) : Bool :=
  entries.any fun e => e.site == ch.site && e.kind == ch.kind &&
    (e.key.isNone || (ch.key.isSome && e.key == ch.key)) && ch.change.le e.change

/-- The entries proposed for `C`'s protocol. -/
def Ctx.proposed (cx : Ctx) (C : Nat) : List ProtocolEntry :=
  cx.F.protocols.filter (·.component == C) |>.flatMap (·.entries)

/-- **The protocol's failures** (Ψ): `C`'s proposed protocol bounds the
members, each write of `C`'s code (the members' and the code they run,
on either exit, the changes at a throw included) charged within it; an
entry names a site of `C`'s code or storage of code outside it. Runs of
code outside `C` inside a member are bounded by the protocol itself
(`ReadOnlyCert.Cert.ofBody`), so the writes alone are the fixed point's
least solution. -/
def protocolDiags (cx : Ctx) (boundary : Std.HashSet Nat) : List Diag := Id.run do
  let mut out : List Diag := []
  for p in cx.F.protocols do
    for e in p.entries do
      for t in e.site do
        if (cx.mark t p.component).isNone then
          out := ⟨p.component, "Ψ", (cx.F.sites[t]?.map (·.module)).getD "", (cx.F.sites[t]?.map (·.pos)).getD (0, 0),
            s!"the protocol names the site {cx.siteName t}, of no code of the component"⟩ :: out
  for w in cx.writes do
    for C in cx.chain w.component do
      let entries := cx.proposed C
      for ch in cx.charges boundary C w do
        if !covers entries ch then
          out := ⟨C, "Ψ", w.module, w.place,
            s!"the protocol omits the change {changeName ch.change} of {cx.partName ch.site ch.kind ch.key}"⟩ :: out
  return out

/-- A component's protocol as text, one entry per line. -/
def Ctx.protocolText (cx : Ctx) (C : Nat) : List String :=
  (cx.proposed C).map fun e => s!"{changeName e.change} at {cx.partName e.site e.kind e.key}"

/-- **The paths an index fact reads of position 0**, with what each reads at
its end; `none` where the fact's form is not read path by path (its support
is then all storage reachable from the value). -/
partial def factPaths : HeapKnowledge.IndexFact → Option (List (HeapKnowledge.Term.Kind × List String))
  | .linear F => some (F.vars.filter (·.slot == 0) |>.map fun t => (t.kind, t.path))
  | .either a b => do return (← factPaths a) ++ (← factPaths b)
  | .guarded 0 path _ body => do return (.value, path) :: (← factPaths body)
  | .guarded _ _ _ body => factPaths body
  | _ => none

/-- **A guarantee candidate's support** at `C`: the parts its paths read
from a record of a site of `C` that may have its first keys, or from
storage of code outside `C`; of every site reachable from them, where a
fact is not read path by path. -/
def Ctx.supportOf (cx : Ctx) (C : Nat) (g : Guarantee) : Charge → Bool :=
  let ofC (t : Nat) : Bool := (cx.mark t C).isSome
  match g.facts.mapM factPaths |>.map List.flatten with
  | some paths =>
    let firsts := paths.filterMap (·.2.head?)
    let roots := (List.range cx.F.sites.length).filter fun t => ofC t && match cx.F.sites[t]? with
      | some s => s.kind != .array && (s.anyKey || firsts.all s.keys.contains)
      | none => false
    let parts := paths.flatMap fun (kind, path) => Id.run do
      let mut level := roots
      let mut acc : List (Option Nat × PartKind × Option String) := []
      for f in path do
        acc := acc ++ (level.map fun t => (some t, PartKind.field, some f)) ++ [(none, .field, some f)]
        level := (cx.closure (.ofSites (level.flatMap (cx.contents · |>.sites)))).sites.filter ofC
      if kind == .length || kind == .view then
        acc := acc ++ (level.map fun t => (some t, PartKind.spine, none)) ++ [(none, .spine, none)]
      return acc
    fun ch => parts.any fun (s, k, key) => s == ch.site && k == ch.kind && (ch.key.isNone || key.isNone || key == ch.key)
  | none =>
    let reach := (cx.closure (.ofSites ((List.range cx.F.sites.length).filter ofC))).sites
    fun ch => ch.site.all reach.contains

/-- The guarantee candidates of `C`: the type invariants of its modules. -/
def Ctx.candidates (cx : Ctx) (C : Nat) : List Guarantee :=
  cx.F.guarantees.filter fun g => (cx.F.components.zipIdx.find? fun (k, i) =>
    k.kind == .module && k.location == g.module && (cx.chain i).contains C).isSome

/-- **The guarantee `G_C`** (the draft, (L4)): each candidate with the
writes of `C`'s code that change its support beyond the client obligation
(`keep`), none where it is kept. A write is construction, free, where its
receiver is fresh at the write in a scope of quiet codes (`unreached`), where the boundary obligations
establish it (ARITHMETIC.md, "Type invariants"). -/
def Ctx.guarantee (cx : Ctx) (boundary quiet : Std.HashSet Nat) (C : Nat) : List (Guarantee × List (String × Span × String)) :=
  (cx.candidates C).map fun g =>
    let supp := cx.supportOf C g
    (g, cx.writes.filter (fun w => (cx.chain w.component).contains C &&
        !cx.unreached boundary quiet w.module w.place w.receiver) |>.flatMap fun w =>
      (cx.chargesOf C w).filter (fun ch => supp ch && !ch.change.le .keep) |>.map fun ch =>
        (w.module, w.place, s!"changes {cx.partName ch.site ch.kind ch.key} by {changeName ch.change}"))

/-- A component's guarantee as text: each candidate kept, or the first
write that changes its support. -/
def Ctx.guaranteeText (cx : Ctx) (boundary quiet : Std.HashSet Nat) (C : Nat) : List String :=
  (cx.guarantee boundary quiet C).map fun (g, ws) => match ws with
    | [] => s!"kept: {g.name}"
    | (m, p, msg) :: _ => s!"not kept: {g.name}: a write at {m} {p.1}-{p.2} {msg}"

/-! ## (O), the stores -/

/-- **The sites an install into `C`'s protected storage may not reach**
(O): of the storage reachable from the stored value, a site of `C` neither
local nor exposed, and storage of code outside `C`. -/
def installBad (cx : Ctx) (C : Nat) (stored : Tokens) : List Nat :=
  (cx.closure stored).sites.filter fun t => match cx.mark t C with
    | some .local | some .exposed => false
    | _ => true

/-- **The values entering from outside an install into `C`'s protected
storage may reach** (O): values that crossed into `C` at a read-only type,
which are protected (the paper's "storage already protected"), and values
entering a component strictly nested in `C` from outside it, which are
`C`'s own code's values, each stated by its own tokens, or values entering
`C` too, through a member of both, each stated by `C`'s. -/
def installIncoming (cx : Ctx) (C : Nat) (stored : Tokens) : Bool :=
  let reach := cx.closure stored
  let inner (D : Nat) : Bool := D != C && (cx.chain D).contains C
  reach.incoming.all inner && reach.ro.all fun D => D == C || inner D

/-- **A shape no value of which holds storage**: a primitive, a union of
such shapes, or a named type whose definition is one. -/
def primitiveShape (types : List TypeRow) : Nat → ComponentWire.Shape → Bool
  | 0, _ => false
  | n + 1, s => match s with
    | .primitive => true
    | .union ps => ps.attach.all fun ⟨e, _⟩ => primitiveShape types n e
    | .named i => match types[i]? with
      | some r => primitiveShape types n r.definition
      | none => false
    | _ => false

/-- **Whether released storage may come back into `C`** (the draft,
"Protection"): released and outside storage is protected only from a
crossing into `C`, and a value crossing in at a position whose declared
type is not primitive may hold any storage, each own field its type does not
mention a position of type `unknown`, read-only (Paper I, "Crossing"). The
crossings in are a member's parameters and receiver, a call's result of
code outside `C` and a caught value; a parameter of a primitive declared
type holds no storage, callers passing values of the declared types. -/
def mayComeBack (cx : Ctx) (C : Nat) : Bool :=
  let fuel := ComponentWire.shapeLimit * (cx.F.types.length + 1)
  (cx.members C).any (fun m => match cx.F.codes[m]? with
    | some code => !code.arrow || code.params.any fun (_, _, ty) => match ty with
      | some t => !primitiveShape cx.F.types fuel t
      | none => true
    | none => false) ||
  cx.F.calls.any (fun c => (cx.outsideOf c).contains C) ||
  cx.F.catches.any (fun k => (cx.chain k.component).contains C)

/-- **A store into storage of `C` that may be protected**: an exposed
site's, a local site's where the possible support of a guarantee candidate
may read the part it writes (`supported`), a released site's where released storage may come back into
`C` (`mayComeBack`) but a field's initial value in the record it allocates
and a store into storage its frame allocated before any outside code could
run (`unreached`), or a value entering `C` from outside. -/
def protectedInto (cx : Ctx) (C : Nat) (r : Tokens) (initial unreached : Bool) (supported : Nat → Bool) : Bool :=
  r.components.contains C && !initial || r.sites.any fun t => match cx.mark t C with
    | some .local => supported t
    | some .exposed => true
    | some .released => !initial && !unreached && mayComeBack cx C
    | _ => false

/-- **Whether a write may change, at the local site `t`, a part the
possible support of a guarantee candidate of `C` reads** (`Ctx.supportOf`). -/
def Ctx.supported (cx : Ctx) (C : Nat) (w : Write) (t : Nat) : Bool :=
  (cx.candidates C).any fun g =>
    let supp := cx.supportOf C g
    (w.parts ((cx.F.sites[t]?).map (·.kind))).any fun (k, key, δ) => supp ⟨some t, k, key, δ⟩

/-- **The ownership failures** (O): a store into storage that may be
protected, of a value whose reachable storage is not all of the
component's local or exposed sites. Storage that may be protected is
exposed, released or outside storage of the region, and local storage the
possible support of a guarantee candidate may read; a store into other
local storage is not constrained: by (K) no outside code reaches it, a fact
reading through it to unprotected storage is bounded by the callback's own
effect there, and a re-entrant member could redirect a path of an
invariant's support. -/
def ownershipDiags (cx : Ctx) (boundary quiet : Std.HashSet Nat) : List Diag := Id.run do
  let mut out : List Diag := []
  for w in cx.writes do
    let r := cx.value w.receiver
    let stored := (w.stored.map cx.value).getD .empty
    let unreached := cx.unreached boundary quiet w.module w.place w.receiver
    for C in cx.chain w.component do
      if protectedInto cx C r w.initial unreached (cx.supported C w) then
        for t in installBad cx C stored do
          match cx.mark t C with
          | some m => out := ⟨C, "O", w.module, w.place,
              s!"a store into storage that may be protected installs the {markName m} site {cx.siteName t}"⟩ :: out
          | none => out := ⟨C, "O", w.module, w.place,
              s!"a store into storage that may be protected installs storage of code outside the component, {cx.siteName t}"⟩ :: out
        if !(installIncoming cx C stored) then
          out := ⟨C, "O", w.module, w.place,
            "a store into storage that may be protected installs a value entering from outside other than read-only into the component"⟩ :: out
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

/-- **Each component's outcome**: its kind, its location, the failures
refusing its certificate, each once, its protocol and its guarantee. -/
def familyOutcome (F : Components) (file : String) (fns : List (String × Span × Bool)) :
    List (Nat × Component × List String × List String × List String) :=
  let cx := Ctx.of F
  let cx := { cx with escaped := cx.escaping }
  let boundary := cx.boundaryValues
  let quiet := cx.quiet cx.runsOutside
  let flow := flowDiags cx
  let diags := suspensionDiags cx file fns ++ marksDiags cx ++ ownershipDiags cx boundary quiet ++ protocolDiags cx boundary
  F.components.zipIdx.map fun (k, C) =>
    let own := flow.filterMap fun (c, module, place, message) =>
      if c.all (cx.chain · |>.contains C) then some s!"(flow) {module} {place.1}-{place.2}: {message}" else none
    (C, k, (own ++ (diags.filter (·.component == C)).map Diag.render).eraseDups, cx.protocolText C,
      cx.guaranteeText boundary quiet C)

def kindName : ComponentWire.Kind → String
  | .package => "package"
  | .module => "module"
  | .klass => "class"

end Verification.ComponentChecks
