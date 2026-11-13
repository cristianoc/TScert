// Bounds pattern P5, the unsafe neighbour of
// `bounds-pattern-generated-table-refused`: a table whose first entry is 9,
// past its end (run under Node: `undefined` at `number`). Trusting generated
// data must name the data it trusts; the decoder tests nothing.
/** @ensures result.length === 4 */
function decode(): Uint8Array {
  const packed = "\u0009\u0001\u0002\u0000";
  const out = new Uint8Array(4);
  for (let i = 0; i < 4; i++) out[i] = packed.charCodeAt(i) & 0xff;
  return out;
}

/** @requires safeInteger(state) && 0 <= state && state < 4 */
export function next(state: number): number {
  const t = decode();
  return t[t[state]!]!;
}
