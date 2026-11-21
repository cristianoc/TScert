// Pretext (src/line-break.ts at the bounds annotations):
// normalizePreparedLineStart, stepPreparedSimpleLineGeometry.
// A fact guarded by a null test of a field of a field, stated at entry, then
// a write of another object's field: every location the guard's path reads
// has a key other than the written one, so the write keeps the guarded fact
// and the return establishes it; so too across a loop writing that field.
type Lines = { ys: number[] | null };
type Handle = { widths: number[]; lines: Lines };
type Cursor = { i: number };

/** @requires h.lines.ys === null || h.lines.ys.length === h.widths.length
 *  @ensures h.lines.ys === null || h.lines.ys.length === h.widths.length */
export function reset(h: Handle, c: Cursor): boolean {
  c.i = 0;
  return true;
}

// The same fact across a loop whose body writes the cursor's field: the
// loop head carries the guarded fact, as no write reaches its guard's path.
/** @requires h.lines.ys === null || h.lines.ys.length === h.widths.length
 *  @ensures h.lines.ys === null || h.lines.ys.length === h.widths.length */
export function seek(h: Handle, c: Cursor): boolean {
  let i = 0;
  /** @invariant safeInteger(i) && 0 <= i */
  while (i < h.widths.length) {
    c.i = i;
    if (h.widths[i]! === 0) return true;
    i++;
  }
  return false;
}
