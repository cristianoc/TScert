// A bound stated at a field, `cursor.at < flags.length`, kept across a call
// whose stated effect may change the spine of `out`: the field read is a
// field or a cell of an object and the length read is a typed array's view
// spine, and the spine of an ordinary array is neither, so the bound still
// holds at the read.
type Cursor = { at: number };
function note(out: number[], v: number): Modifies<{ values: "keep"; spines: "keep"; "out[*]": "any" }, void> {
  out.push(v);
}
/** @requires safeInteger(cursor.at) && 0 <= cursor.at && cursor.at < flags.length */
export function read(flags: Uint8Array, cursor: Cursor, out: number[]): number {
  note(out, 1);
  return flags[cursor.at]!;
}
