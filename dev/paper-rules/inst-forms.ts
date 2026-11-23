// Two forms of rule Inst: a call passing no callback instantiates the
// effect variable with the empty effect, and a call inside a function with
// its own effect variable may forward it (θ(ε') = ε), checked by including the
// outer bound, read at the inner call's arguments, in the inner one.
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" | true };
type AtMost<P extends Footprint> = Footprint;
type LineVisitor<E extends Footprint> = (width: number, start: number, end: number) => Modifies<E, void>;
type Range = { width: number; start: number; end: number };
type RangeVisitor<E extends Footprint> = (range: Range) => Modifies<E, void>;
type Prepared = { widths: number[]; flags: number[] };
type Cursor = { segmentIndex: number };

export function walkLines<E extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onLine?: LineVisitor<E>): number {
  const cursor: Cursor = { segmentIndex: 0 };
  let lines = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < prepared.widths.length) {
    const start = cursor.segmentIndex;
    onLine?.(prepared.widths[start]!, start, start + 1);
    lines += prepared.widths[cursor.segmentIndex]! >= 0 ? 1 : 0;
    cursor.segmentIndex = start + 1;
  }
  return lines;
}

// Positive: no callback is passed, so the instance is the empty effect, and
// the call changes the heap at most by the walker's own effect: the lengths'
// equality survives.
/** @requires safeInteger(i) && 0 <= i */
export function countOnly(p: Prepared, i: number): number {
  if (p.flags.length !== p.widths.length) return 0;
  walkLines(p, undefined);
  if (i < p.widths.length) return p.flags[i]!;
  return 0;
}

// Positive: an adapter forwards its own effect variable. Its bound is the
// inner walker's at the actual arguments, so the forwarded instance is within
// the inner bound; the closure's only effect on old storage is the outer
// callback's, besides the range it allocates.
export function walkRanges<F extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onRange: RangeVisitor<F>): number {
  return walkLines<F>(prepared, (w, s, e) => { onRange({ width: w, start: s, end: e }); });
}

// Positive: a caller of the adapter with a true claim keeps its fact.
/** @requires safeInteger(i) && 0 <= i */
export function rangesCaller(p: Prepared, i: number): number {
  if (p.flags.length !== p.widths.length) return 0;
  const seen: number[] = [];
  walkRanges<{ "seen[*]": "extend" }>(p, (r) => { seen.push(r.width); });
  if (i < p.widths.length) return p.flags[i]!;
  return 0;
}

// Negative, refused at Inst (safe but unprovable): the adapter's bound lets
// its callback change anything, the handle included, which the inner
// walker's bound keeps.
export function widerAdapter<F extends AtMost<{ else: "any" }>>(
  prepared: Prepared, onRange: RangeVisitor<F>): number {
  return walkLines<F>(prepared, (w, s, e) => { onRange({ width: w, start: s, end: e }); });
}

// Negative, refused at the callback's check (safe but unprovable): the
// closure also writes a captured counter, which the forwarded variable does
// not allow.
export function countingAdapter<F extends AtMost<{ "prepared.**": "keep"; else: "any" }>>(
  prepared: Prepared, onRange: RangeVisitor<F>, tally: { n: number }): number {
  return walkLines<F>(prepared, (w, s, e) => { tally.n++; onRange({ width: w, start: s, end: e }); });
}
