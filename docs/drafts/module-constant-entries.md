# Entries for module constants holding functions

An importer reads a function of a module with a body at the interface
entry that module's own check establishes, and otherwise at its declared
type with the ordinary effect, nothing stated assumed
([module linking](../SINGLE-PASS.md#10-module-linking), `import-body` in
[imported values](../SOURCE-CONTRACTS.md#imported-ambient-and-global-values)).
A `const` binding of a module initialised by a function literal,
`export const f = (x: A): B => e`, gets no entry
(`blocker-compiler-api-token-subtype`, tools/fragment-support.mts's
`skipParentheses`). This draft states what an entry for it is over, what
the importer may assume of it, and why the exporter's check establishes it.

## The existing mechanism this extends

The module layout and its interface entries
([the module layout](../SINGLE-PASS.md#the-module-layout),
[module interfaces](../SINGLE-PASS-THEOREM.md#7-module-interfaces)): a
module step publishes an entry for a function laid out
(`FilePlans.laidOut`), each row of its interface realized by a member's
request (`RowRealized`, `rowSpec_of_requestSafe`); `entry_met` carries the
function's value in the module's environment (`approx`) to the importer's
slot through the store map. Within its module, a constant holding a
literal is a binding of the top-level code: the literal's body is checked
as a closure of the `:init` request at the signature its annotation states,
and the module's functions read the constant at its type
(`Front.withInitTypes`), a slot of kind `moduleCell` whose contract is the
initialization's postcondition (`KindMet` at `moduleCell`, H5b, a named
hypothesis).

## The route: the constant's literal laid out as a module function

**What the entry is over.** The constant's slot holds a closure value whose
code is the literal's. Where the literal is eligible, its code is a unit of
its own, laid out as a module function: its captures are slots of the
module's environment (`Slot.linked` for the module's functions,
`Slot.outside` for its cells and constants), and its interface rows are
realized by its request (`RowRealized`), as a declaration's are. The entry
is then the existing one, `entry_met` unchanged.

**Eligibility** (a restricted subset, checked where the literal is
lowered): a `const` declarator of the module's top level whose initializer
is the literal alone, an arrow (no own `this`, no `arguments`) or a
function expression reading no `this`, of fixed arity, no binders, no rest
and no defaults, with a written result; the binding is not early (no
mention of it in a closure created before its initialization point, the
module's initialization order check passing); a self-reference in its
body is a linked slot of its own, as a recursive declaration's.

**Why it is the same as a declared function for linking, and where it
differs.** After its initialization point the binding holds the closure
for ever: a `const` is written once, and creating a literal runs nothing.
A declared function's binding holds its closure from the module's
instantiation; the constant's from its initialization point, before which
a read throws a `ReferenceError`. Every certified read of the constant must
therefore occur after that point, its captures meeting their contracts:
the [linking obligation](../SOURCE-CONTRACTS.md#certified-imports)'s
runtime invariant extended from a declaration's binding to the constant's
initialization point. Within the module the initialization order check
refuses an initialization step that may reach the constant unbound; across
modules, an importer's code runs before the exporter's initialization only
in a runtime module cycle, which the model does not state. This is a review
obligation, the same limit the module's own constants have
([lexical bindings before initialization](../SOURCE-ELABORATION.md#lexical-bindings-before-initialization)),
not evidence; the acyclic order of publication does not imply acyclic
runtime evaluation.

**What changes.** The lowering of an eligible constant (trusted, the
source-to-graph lowering): the literal's code becomes a unit, its captures
the module's slots rather than values of `:init`'s frame, and `:init`'s
binding of the constant holds that unit's closure. Lexical `this`,
self-reference, capture identity (one closure object per module) and the
initialization point are audited at that change.

## The route considered and set aside

An entry over the `:init` group, the importer's slot of a new outside kind
whose contract is the exporter's `moduleCell` contract carried through the
store map. `KindMet` at `moduleCell` quantifies over outside captures of
laid-out functions, so an exported constant no laid-out function captures
has no witness; and `init_asserted` gives knowledge facts at `:init`'s
finish states, not the typed contract at every world the slot needs. This
route needs a realization of each exported value (its binding, type and
value at each depth, with store agreement) beside `EntryRealized`,
duplicating entry realization, publication and transport, and a typed
initialization guarantee that would be a new hypothesis.

## Cases

- Positive: `blocker-compiler-api-token-subtype`.
- Negative: an imported constant arrow whose body breaks its stated effect,
  read by an importer relying on it, refused because no entry is
  published (run under Node).
