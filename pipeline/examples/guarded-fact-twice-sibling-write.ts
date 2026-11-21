// A fact under two guards, an `undefined` test of a field and a `null` test
// of a field of it, then a write of another object's field: the write keeps
// what each guard's path reads, so it keeps the fact under both guards, of an
// array's length and of a typed array's length read through two fields.
type Lines = { ys: number[] | null; ends: Uint8Array | null };
type Handle = { widths: number[]; lines: Lines | undefined };
type Cursor = { i: number };

/** @requires h.lines === undefined || h.lines.ys === null || h.lines.ys.length === h.widths.length
 *  @requires h.lines === undefined || h.lines.ends === null || h.lines.ends.length === h.widths.length
 *  @ensures h.lines === undefined || h.lines.ys === null || h.lines.ys.length === h.widths.length
 *  @ensures h.lines === undefined || h.lines.ends === null || h.lines.ends.length === h.widths.length */
export function reset(h: Handle, c: Cursor): boolean {
  c.i = 0;
  return true;
}
