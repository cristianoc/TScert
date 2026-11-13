// Bounds pattern P5, the supported neighbour of
// `bounds-pattern-generated-table-refused`: the decoded table read at an
// index bounded by its stated length.
// Pretext: line-breaks.ts's tables read at a checked state.
/** @ensures result.length === 4 */
function decode(): Uint8Array {
  const packed = "\u0003\u0001\u0002\u0000";
  const out = new Uint8Array(4);
  for (let i = 0; i < 4; i++) out[i] = packed.charCodeAt(i) & 0xff;
  return out;
}

/** @requires safeInteger(state) && 0 <= state && state < 4 */
export function direct(state: number): number {
  const t = decode();
  return t[state]!;
}
