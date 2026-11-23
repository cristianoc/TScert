// W1 of "An effect language for TScert", reduced from Pretext's
// walkPreparedLinesRaw (src/line-break.ts at 0dafecb3): a walker that
// allocates a cursor, reads its handle's array under a guard on its length,
// and calls its visitor between steps. Pretext reads a local copy of the
// handle's field (`const { segmentFlags } = prepared`); that form is in
// w1-snapshot.ts. The bound keeps the handle's
// declared reach. Each caller's instance states its visitor's effect; the
// prototype checks it against the bound (rule Inst). Negative callers say
// whether the program is unsafe or only unprovable.
type AtMost<P> = unknown;
type LineVisitor<E> = (width: number, start: number, end: number) => void;
type Prepared = { widths: number[]; flags: number[] };
type Cursor = { segmentIndex: number };
type Flow = { data: Prepared; wholeWidth: number; widths: number[] };

export function walkLines<E extends AtMost<'{ "prepared.**": "keep", "else": "any" }'>>(
  prepared: Prepared, onLine: LineVisitor<E>): number {
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {
    const start = cursor.segmentIndex;
    onLine(prepared.widths[start]!, start, start + 1);
    // After the visit: the cursor, the handle's field and its array are
    // read again, relying on the facts the visit kept.
    lines += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}

// Positive: a visitor appending to a fresh list.
export function collect(p: Prepared): number {
  const out: number[] = [];
  return walkLines<'{ "out[*]": "extend" }'>(p, (w) => { out.push(w); });
}

// Positive: a visitor incrementing a field of a fresh captured object.
export function count(p: Prepared): number {
  const seen = { n: 0 };
  return walkLines<'{ "seen.n": "scalar" }'>(p, () => { seen.n++; });
}

// Positive (W3): a visitor writing a field of the object holding the handle,
// at a key the handle's type does not declare.
export function findWhole(flow: Flow): number {
  return walkLines<'{ "flow.wholeWidth": "any" }'>(flow.data, (w) => { flow.wholeWidth = w; });
}

// Positive: a visitor doing nothing.
export function quiet(p: Prepared): number {
  return walkLines<'{}'>(p, () => { return; });
}

// Positive: a visitor only reading the handle, into a fresh accumulator.
export function peek(p: Prepared): number {
  const acc = { sum: 0 };
  return walkLines<'{ "acc.sum": "any" }'>(p, () => { acc.sum += p.widths[0] ?? 0; });
}

// Negative, only unprovable: growing the walked array keeps every read in
// bounds (the loop runs until push throws at the maximal length).
export function pushHandle(p: Prepared): number {
  return walkLines<'{ "p.widths[*]": "extend" }'>(p, (w) => { p.widths.push(w); });
}

// Negative, unsafe: after the visit the walker reads p.widths at the cursor,
// past the end of the new empty array.
export function replaceField(p: Prepared): number {
  return walkLines<'{ "p.widths": "any" }'>(p, () => { p.widths = []; });
}

// Negative, only unprovable: writing an element changes no length.
export function writeElement(p: Prepared): number {
  return walkLines<'{ "p.widths[*]": "any" }'>(p, () => { p.widths[0] = 1; });
}

// Negative, only unprovable: growing the handle's array through an alias.
export function aliasPush(p: Prepared): number {
  const ws = p.widths;
  return walkLines<'{ "ws[*]": "extend" }'>(p, () => { ws.push(0); });
}

// Negative, only unprovable: growing the handle's array through its holder.
export function holderPush(flow: Flow): number {
  return walkLines<'{ "flow.data.widths[*]": "extend" }'>(flow.data, () => { flow.data.widths.push(0); });
}

// Negative, only unprovable: the holder's own field `widths` is another
// location than the handle's, but its key is one the handle's type declares,
// so disjointness by key cannot separate them.
export function holderDeclaredKey(flow: Flow): number {
  return walkLines<'{ "flow.widths": "any" }'>(flow.data, () => { flow.widths = []; });
}
