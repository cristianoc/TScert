// Facts read through two fields across a write of an object into another
// object's field: the write's frame is the written location alone, and every
// location the facts' paths read has another key, so the write keeps a
// linear fact over `h.lines.ys.length` and a spine separation of
// `h.lines.ys` from `h.lines.zs`, which keeps the length across the push.
type Lines = { ys: number[]; zs: number[] };
type Handle = { widths: number[]; lines: Lines };
type Cursor = { at: Lines };

/** @requires h.lines.ys.length === h.widths.length
 *  @ensures h.lines.ys.length === h.widths.length */
export function point(h: Handle, c: Cursor, to: Lines): boolean {
  c.at = to;
  return true;
}

/** @requires h.lines.ys !== h.lines.zs && h.lines.ys.length <= 1
 *  @ensures h.lines.ys.length <= 1 */
export function pointAndGrow(h: Handle, c: Cursor, to: Lines): boolean {
  c.at = to;
  h.lines.zs.push(1);
  return true;
}
