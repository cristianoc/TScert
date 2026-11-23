// The conclusion of rule Inst at the caller: a call of a walker whose
// instance is within its bound changes the heap at most by the bound and the
// walker's own effect, read at the actual arguments, so the caller keeps the
// facts the bound keeps (here, about the handle `p`).
type AtMost<P> = unknown;
type LineVisitor<E> = (width: number, start: number, end: number) => void;
type Prepared = { widths: number[]; flags: number[] };
type Cursor = { segmentIndex: number };

export function walkLines<E extends AtMost<'{ "prepared.**": "keep", "else": "any" }'>>(
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
  walkLines<'{ "lines[*]": "extend" }'>(p, (w) => { lines.push(w); });
  if (i < p.widths.length) return p.flags[i]!;
  return 0;
}

// Negative, safe but unprovable: a fact about `q`, outside the bound's
// reach, which the bound's `else: any` lets the call change.
/** @requires safeInteger(i) && 0 <= i */
export function outside(p: Prepared, q: number[], i: number): number {
  if (i >= q.length) return 0;
  const lines: number[] = [];
  walkLines<'{ "lines[*]": "extend" }'>(p, (w) => { lines.push(w); });
  return q[i]!;
}

// Negative, refused at Inst: the instance grows the handle, which the bound
// keeps.
/** @requires safeInteger(i) && 0 <= i */
export function badInst(p: Prepared, i: number): number {
  if (p.flags.length !== p.widths.length) return 0;
  walkLines<'{ "p.widths[*]": "extend" }'>(p, (w) => { p.widths.push(w); });
  if (i < p.widths.length) return p.flags[i]!;
  return 0;
}

// Control: `caller` with a second call of arity 2 in its body, so the layer
// cannot tell the walker's call apart and gives it nothing; refused as the
// ordinary verifier refuses `caller`.
/** @requires safeInteger(i) && 0 <= i */
export function callerUntold(p: Prepared, i: number): number {
  if (p.flags.length !== p.widths.length) return 0;
  const lines: number[] = [];
  walkLines<'{ "lines[*]": "extend" }'>(p, (w) => { lines.push(w); });
  const m = Math.max(0, 1);
  if (i < p.widths.length) return p.flags[i]! + m;
  return 0;
}
