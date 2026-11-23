// Counterexamples to decisions the prototype once took beyond the paper's
// rules, each refused now. The walker is W1's (w1.ts); each negative says
// whether its program is unsafe or only unprovable, and which rule refuses
// it.
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" | true };
type AtMost<P extends Footprint> = Footprint;
type LineVisitor<E extends Footprint> = (width: number, start: number, end: number) => Modifies<E, void>;
type Prepared = { widths: number[]; flags: number[] };
type Cursor = { segmentIndex: number };
type Flow = { data: Prepared; wholeWidth: number };
interface Widths { widths: number[] }
interface Extended extends Widths { flags: number[] }

const shared: number[] = [];

export function walkLines<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {
    const start = cursor.segmentIndex;
    onLine(prepared.widths[start]!, start, start + 1);
    lines += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}

// 1. Negative, unsafe (Inst's disjointness): `box` is allocated by the
// caller, but its alias `alias` is the handle, so the field the instance
// writes is the handle's `widths`, which the walker reads past the end of
// the new empty array.
export function freshAlias(): number {
  const box = { widths: [1, 2, 3], flags: [0, 0, 0] };
  const alias = box;
  return walkLines<{ "box.widths": "any" }>(alias, () => { box.widths = []; });
}

// 1. Negative, only unprovable (Inst's disjointness): a module-level
// constant is no storage the caller allocated; the handle's array may be
// it.
export function moduleConst(p: Prepared): number {
  return walkLines<{ "shared[*]": "extend" }>(p, () => { shared.push(0); });
}

// 4. Negative, unsafe (Fresh-Eff): the callback allocates `h`, but `h.a`
// is the handle; replacing its `widths` is a change of older storage.
export function freshHolder(p: Prepared): number {
  return walkLines<{}>(p, () => { const h = { a: p }; h.a.widths = []; });
}

// 3. A walker whose bound lets the visitor change anything old: the
// walker relies on its cursor alone, which the visitor cannot reach (Anch).
export function walkAny<E extends AtMost<{ else: "any" }>>(xs: number[], onLine: LineVisitor<E>): number {
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < 10) {
    const start = cursor.segmentIndex;
    onLine(0, start, start + 1);
    lines += xs.length > 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}

// 3. Negative, only unprovable (instances and anchoring): an instance has
// `else: keep` and no class key; `values` is no anchored region.
export function classInstance(xs: number[]): number {
  const out: number[] = [];
  return walkAny<{ "out[*]": "extend"; values: "scalar" }>(xs, (w) => { out.push(w); });
}

// 9. Negative, only unprovable (Field-Write): a logical assignment may
// write a non-primitive value, so it is no scalar write.
export function logicalWrite(flow: Flow): number {
  return walkLines<{ "flow.wholeWidth": "scalar" }>(flow.data, (w) => { flow.wholeWidth ||= w; });
}

// 7. Negative, unsafe (declared reach): `widths` is a key the handle's type
// declares through `extends`, so the field is in the reach.
export function walkExtended<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Extended, onLine: LineVisitor<E>): number {
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {
    const start = cursor.segmentIndex;
    onLine(0, start, start + 1);
    lines += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}

export function extendedKey(p: Extended): number {
  return walkExtended<{ "p.widths": "any" }>(p, () => { p.widths = []; });
}

function scramble(c: { n: number }): Modifies<{ values: "any" }, void> {
  c.n = 1e9;
}

// 6. The walker's own effect changes any value (`scramble`); its bound
// keeps `c.n`. The call's effect is the union of the two: `c.n` is in the
// bound's entries, but the own effect's `else` changes it.
export function walkOwn<E extends AtMost<{ "c.n": "keep"; "xs[*]": "keep"; else: "any" }>>(
  c: { n: number }, xs: number[], onLine: LineVisitor<E>): number {
  onLine(0, 0, 0);
  scramble(c);
  return xs.length;
}

// 6. Negative, unsafe (Inst's conclusion): `c.n` is 1e9 after the call.
/** @requires safeInteger(c.n) */
export function ownElse(c: { n: number }, xs: number[]): number {
  if (c.n < 0 || c.n >= xs.length) return 0;
  walkOwn<{}>(c, xs, () => { return; });
  return xs[c.n]!;
}

// 10. The walker writes an element of its argument (Elem-Write: the spine
// and the cells). Its bound keeps the cells of `xs` (`"xs[#]"`, the
// prototype's key for `xs.cells`).
export function walkCells<E extends AtMost<{ "xs[#]": "keep"; "xs[*]": "keep"; else: "any" }>>(
  xs: number[], onLine: LineVisitor<E>): number {
  onLine(0, 0, 0);
  if (xs.length > 0) xs[0] = 1e9;
  return xs.length;
}

// 10. Negative, unsafe (Inst's conclusion): the walker's own effect
// changes `xs[0]`, which indexes `ys`; the fact about the cells of `xs` does
// not survive the call.
/** @requires forall i in xs: safeInteger(xs[i]) && 0 <= xs[i] && xs[i] < ys.length */
export function cellsCaller(xs: number[], ys: number[]): number {
  if (xs.length === 0) return 0;
  walkCells<{}>(xs, () => { return; });
  return ys[xs[0]!]!;
}

// 10. Positive control: the same read without the call.
/** @requires forall i in xs: safeInteger(xs[i]) && 0 <= xs[i] && xs[i] < ys.length */
export function cellsNoCall(xs: number[], ys: number[]): number {
  if (xs.length === 0) return 0;
  return ys[xs[0]!]!;
}

// 8. Negative, unsafe (the callback's type): the callback's type, a union of
// a visitor of effect E and one changing every value, states an effect besides
// its variable, which replaces the handle's array the walker reads; the layer
// reads the variable alone at the callback's calls.
export function walkPlus<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onLine: ((w: number) => Modifies<E, void>) | ((w: number) => Modifies<{ values: "any" }, void>)): number {
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {
    const start = cursor.segmentIndex;
    onLine(0);
    lines += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}

// 8. Negative, unsafe (forwarding): the adapter forwards E, but its closure
// calls the callback of F, whose bound lets it replace the handle's array.
export function twoVars<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>,
    F extends AtMost<{ else: "any" }>>(prepared: Prepared, onA: LineVisitor<E>, onB: LineVisitor<F>): number {
  onA(0, 0, 0);
  return walkLines<E>(prepared, (w, s, e) => { onB(w, s, e); });
}

// 5. Negative, only unprovable (Bound's second premise): the walker's own
// steps replace a field of the handle, so the reach the bound reads at the
// callback's call is not the one read at the walker's entry.
export function walkSwap<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, spare: number[], onLine: LineVisitor<E>): number {
  prepared.widths = spare;
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {
    const start = cursor.segmentIndex;
    onLine(0, start, start + 1);
    lines += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}

// 2. Negative (a signature holds for every call): the walker is held by a
// constant, through which a call's instance is not checked.
export function walkAliased<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {
    const start = cursor.segmentIndex;
    onLine(0, start, start + 1);
    lines += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}

export function viaAlias(p: Prepared): number {
  const w = walkAliased;
  return w(p, () => { p.widths = []; });
}

// 2. Negative (a signature holds for every call): the walker is called in a
// file importing it (review-importer.ts), in a top-level constant closure no
// unit's verdict covers.
export function walkImported<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {
    const start = cursor.segmentIndex;
    onLine(0, start, start + 1);
    lines += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}
