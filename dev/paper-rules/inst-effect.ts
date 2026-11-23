// The conclusion of rule Inst at the caller: a call of a walker whose
// instance is within its bound changes the heap at most by the bound and the
// walker's own effect, read at the actual arguments, so the caller keeps the
// facts the bound keeps (here, about the handle `p`).
type Footprint = { [location: string]: "keep" | "init" | "scalar" | "extend" | "grow" | "any" | true };
type AtMost<P extends Footprint> = Footprint;
type LineVisitor<E extends Footprint> = (width: number, start: number, end: number) => Modifies<E, void>;
type Prepared = { widths: number[]; flags: number[] };
type Cursor = { segmentIndex: number };

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

// Positive: the lengths' equality, established before the call, is kept
// across it, and gives the bound on `p.flags[i]`.
/** @requires safeInteger(i) && 0 <= i */
export function caller(p: Prepared, i: number): number {
  if (p.flags.length !== p.widths.length) return 0;
  const lines: number[] = [];
  walkLines<{ "lines[*]": "extend" }>(p, (w) => { lines.push(w); });
  if (i < p.widths.length) return p.flags[i]!;
  return 0;
}

// Negative, safe but unprovable: a fact about `q`, outside the bound's
// reach, which the bound's `else: any` lets the call change.
/** @requires safeInteger(i) && 0 <= i */
export function outside(p: Prepared, q: number[], i: number): number {
  if (i >= q.length) return 0;
  const lines: number[] = [];
  walkLines<{ "lines[*]": "extend" }>(p, (w) => { lines.push(w); });
  return q[i]!;
}

// Negative, refused at Inst: the instance grows the handle, which the bound
// keeps.
/** @requires safeInteger(i) && 0 <= i */
export function badInst(p: Prepared, i: number): number {
  if (p.flags.length !== p.widths.length) return 0;
  walkLines<{ "p.widths[*]": "extend" }>(p, (w) => { p.widths.push(w); });
  if (i < p.widths.length) return p.flags[i]!;
  return 0;
}

// Two walker calls with the same number of arguments, each with its own
// instance: the layer finds each call by its source span (two calls whose
// lowered nodes it cannot tell apart keep what both keep), and the fact
// survives both.
/** @requires safeInteger(i) && 0 <= i */
export function callerTwoCalls(p: Prepared, i: number): number {
  if (p.flags.length !== p.widths.length) return 0;
  const lines: number[] = [];
  const marks: number[] = [];
  walkLines<{ "lines[*]": "extend" }>(p, (w) => { lines.push(w); });
  walkLines<{ "marks[*]": "extend" }>(p, (w) => { marks.push(w); });
  if (i < p.widths.length) return p.flags[i]!;
  return 0;
}

function touch(p: Prepared, n: number): void {
  p.flags = [n];
}

// Control: a walker call and a call of another function with the same
// number of arguments, which may change the handle. The second call is no
// walker call, so the layer gives it nothing, and the fact is lost there:
// refused at the read. (Unsafe: `touch` shortens `p.flags`.)
/** @requires safeInteger(i) && 0 <= i */
export function callerTouched(p: Prepared, i: number): number {
  if (p.flags.length !== p.widths.length) return 0;
  const lines: number[] = [];
  walkLines<{ "lines[*]": "extend" }>(p, (w) => { lines.push(w); });
  touch(p, 0);
  if (i < p.widths.length) return p.flags[i]!;
  return 0;
}
