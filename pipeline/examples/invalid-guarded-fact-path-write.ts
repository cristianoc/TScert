// A fact guarded by a null test of `h.lines.ys`, then a write of the field
// `ys` of a parameter that may hold `h.lines`: the guard's path reads a
// location of the written key, so the write does not keep the fact. Under
// Node, `reset(h, h.lines)` with `h.lines.ys === null` and one width leaves
// `h.lines.ys.length === 0`, and the postcondition is false.
type Lines = { ys: number[] | null };
type Handle = { widths: number[]; lines: Lines };

/** @requires h.lines.ys === null || h.lines.ys.length === h.widths.length
 *  @ensures h.lines.ys === null || h.lines.ys.length === h.widths.length */
export function reset(h: Handle, other: Lines): boolean {
  other.ys = [];
  return true;
}
