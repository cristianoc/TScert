// A `let` assigned a view of `s.length + 1` elements, read one past its last
// element: `breaks[s.length + 1]!` is `undefined` at `number` (run under Node:
// `pastBreak("ab")` is `undefined`).
/** @ensures result.length === s.length + 1 */
function lineBreaks(s: string): Uint8Array {
  return new Uint8Array(s.length + 1);
}
export function pastBreak(s: string): number {
  let breaks: Uint8Array;
  breaks = lineBreaks(s);
  return breaks[s.length + 1]!;
}
