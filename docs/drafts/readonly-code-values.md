# Draft: code values that reach no local site

A change to the read-only frame's typing by sets of sites
([read-only handles](readonly-handles.md), "The sites a value may reach"
and "The sites of a term"): the fact that no value held in the code of a
bound function or of a closure of outside code reaches a local site moves
from the heap of sites to the value judgment. Claims are labelled as in
that draft; everything here is conjectured until the Lean named below
exists.

## The existing mechanism this extends

The read-only frame's checks read each value of an execution at a set of
sites ([read-only handles](readonly-handles.md), "The sites a value may
reach", cited): a heap of sites $`H`$ (`SiteHeap`) gives, per site $`s`$,
the sites its storage may reference, $`H.\mathsf{contents}(s)`$, and the
sites the values held in the code of a closure of outside code or of a
bound function stored there may reach first, $`H.\mathsf{bindings}(s)`$. A
write of a value meeting $`S`$ into storage of site $`s`$ requires
$`S\subseteq H.\mathsf{contents}(s)`$ and $`S\subseteq
H.\mathsf{bindings}(s)`$ (`Stores`); a heap meets the flow when each
location's value meets its site's contents and its code's values its
site's bindings (`HeapInv`, `HeapSites`). The bindings component serves
one clause of (M), `BindingsClosed`: no value held in the code of a stored
bound function or closure of outside code reaches a local location in its
paths' first step, obtained from $`\forall s.\ \mathrm{NoLocal}(H.\mathsf{bindings}(s))`$
(`localBindings_of_sites`, `FFlow.bindingsB`). With `LocalClosed`, no path
from such a binding reaches local storage (`binding_no_local`, proved).

This design keeps the mechanism, the clause and its use; it changes where
the clause's evidence lives.

## Why the change

`Stores` charges every write to the bindings of the written site, whatever
the value written. Storage of a local site holding a local object (a
local record `h` whose fields are local arrays) then has local sites among
its bindings, and $`\mathrm{NoLocal}(H.\mathsf{bindings}(s))`$ fails,
although no bound function or closure of outside code is ever stored
there (observed: the handle fixture
`bounds-pattern-unreachable-handle-refused.ts`, where `frameCheckAt`
passes both length facts and `FFlow.bindingsB` fails). The bindings bound
a property of the values written, not of the storage.

## The definitions

Write $`\mathrm{cv}(w)`$ for the values held in the code of $`w`$
(`codeVals`): a bound function's saved target, receiver and arguments; a
closure of outside code's node expressions' values and captures; nothing
for any other value. Write $`v \succeq w`$ when $`w`$ is within $`v`$
(`Within`: $`v`$ itself, a capture, a node expression's value of graph
code, a part of a bound function, transitively). Write
$`\mathrm{NL}_{g,n}(x)`$ when every first location $`l`$ that $`x`$ reaches
(`Leaves`) is allocated, $`l < n`$, and has an origin other than local at
the ghost $`g`$. Both halves are needed: a closure of $`C`$'s code holds
its node expressions' values in no leaf of its own (its `codeVals` are
none), so `VJ.below` bounds no leaf of a bound function among them, and a
leaf past the heap's length, outside storage at $`g`$, becomes local when
a later allocation gives it a local site (proved as a counter-model to the
origin half alone: `Within`, `codeVals` and `Leaves` of the closure
$`v`$ with node expression $`b`$ = a bound function whose receiver is
`.arr [some 1]`).

- **Value judgment.** $`\mathrm{VJ}_{g,n}(S, v)`$ gains one conjunct
  (`VJ.codeNL`), displayed below the list. It does not mention $`S`$: it is
  a property of the value at the ghost and the heap's length.
- **Heap of sites.** $`H`$ is $`H.\mathsf{contents}`$ alone. A heap meets
  it (`HeapSites`) when each location's value meets its site's contents
  and its code's values satisfy $`\mathrm{NL}_{g,n}`$ at the heap's length (the clause in place of
  the bindings clause, stated of values, as `BindingsClosed` states it).
- **Stores.** $`\mathrm{Stores}(s, S) := S \subseteq H.\mathsf{contents}(s)`$,
  inclusion in one set, so closed under union of the stored sets.
- **HeapInv.** Each location holds a value meeting its site's contents
  (`VJ` at $`H.\mathsf{contents}(g.\mathsf{site}(w))`$); the code values'
  clause follows from `VJ.codeNL` at $`w = v`$.

The conjunct of the value judgment:

```math
\forall w.\ v \succeq w \Rightarrow \forall x \in \mathrm{cv}(w).\ \mathrm{NL}_{g,n}(x)
```

## The rules that change

Every rule that makes a value whose code holds values requires them
$`\mathrm{NL}`$; every other rule makes values whose code values are those
of values it already has (a read, a substitution, a call's result), or
none.

- **makeBound** (a bound function made by any frame): the target, receiver
  and arguments meet a set $`S_b \subseteq S`$ with $`\mathrm{NoLocal}(S_b)`$,
  $`S`$ the bound function's own set (which holds the bound function's
  site and may be local): the parts still meet $`S`$, as the rule requires
  today, since the bound function's leaves are its parts' leaves.
- **makeGraphOut** (a closure of outside code made by any frame): its
  captures meet a set $`S_c \subseteq S`$ with $`\mathrm{NoLocal}(S_c)`$;
  its node expressions are lowered (`Lowered`), holding no located value.
- **Outside code**: every value it holds meets $`O`$; a flow's facts gain
  $`\mathrm{NoLocal}(O)`$ (`Flow.Facts.noLocal`), which `Lendable O`
  implies at the marks a flow gives (`FFlow.MarksFrom`). So a bound
  function or closure of outside code made by outside code meets the two
  rules above at $`S_b = S_c = O`$.
- **Entry**: at the entry history every location is outside storage, so
  every value meets the conjunct (`VJ.entry`).

A local site is a site whose storage no binding of a module or closure
holds ([read-only handles](readonly-handles.md), "Marks"); a bound function
or closure of outside code binding a local value contradicts that mark
wherever it is held, a local variable included. So the conjunct asks of
every value what (M) asks of stored ones, and the rules refuse a bound
function of $`C`$'s code binding a local value even when it is never
stored: a stated limit, chosen by the behaviour it excludes (a binding
that outside code may run, holding local storage). (M) itself asks it of
stored values only; a check at each write would ask less, but needs
evidence of the written value's code values that a set of sites does not
carry, which is what the bindings component was.

## What must be proved

- `VJ.alloc`: allocation keeps the conjunct (old locations keep their
  sites and origins, and every leaf the conjunct reads is below the old
  length).
- `VJ.mono`, `VJ.sub`: the conjunct is independent of the set.
- `fits_step`, `fitsAt_reached`: every value a step makes meets the
  conjunct: by the two rules above for `makeBound` and `makeGraphOut`
  (at a frame of $`C`$'s code from $`\mathrm{NoLocal}(S_b)`$, $`\mathrm{NoLocal}(S_c)`$;
  at outside code from $`\mathrm{NoLocal}(O)`$), and by `Within`'s closure
  for every value a step reads out of another (a field, a capture, a bound
  part, a substituted variable).
- `HeapInv.set`, `HeapInv.append`, `HeapInv.fresh`: the bindings premise
  removed; the code values' clause from the written value's `VJ.codeNL`.
- `HeapSites`, `localBindings_of_sites`, `chkSound_of_sites`,
  `escapeAt_of_sites`: the premise $`\forall s.\ \mathrm{NoLocal}(H.\mathsf{bindings}(s))`$
  removed; `BindingsClosed` from the heap's code values' clause.
- `OutsideWritable`, `sites_outside`: the bindings half removed; an
  outside step stores values meeting $`O`$, whose code values meet $`O`$,
  so $`\mathrm{NL}`$ by $`\mathrm{NoLocal}(O)`$.
- `FFlow.marks_of_marksFrom`: gives `Lendable O`, `LocalHeld H`, and
  $`\mathrm{NoLocal}(O)`$; `FFlow.bindingsB` and `FFlow.bindings` go.
- The decider (`syn`, `storesB`): `storesB` reads the contents alone;
  `makeBound` and `makeGraphOut` decide $`\mathrm{NoLocal}`$ of their parts'
  sets from the marks, so the checks run at the marks the flow gives
  (`remark`, `FFlow.MarksFrom`), not at a package marking every site
  released.

Proof scope: to be stated when the Lean exists. The headline statements
(`FFlow.check_sound`, `ClientFrame.framed_at_call`, `codeChkB_sound`)
keep their conclusions; their premises lose the bindings condition.
