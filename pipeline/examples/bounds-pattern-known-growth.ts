// Bounds pattern P2, the supported neighbour of
// `bounds-pattern-known-growth-refused`: the pushes in the caller's own body,
// where `push` states widths.length = old(widths.length) + 1.
// Pretext: rich-inline.ts prepareRichInline's lists.
/** @requires safeInteger(cap) && 0 <= cap && cap <= 100000 */
export function pushedHere(cap: number): number {
  const widths: number[] = [];
  const flags = new Uint8Array(cap);
  let s = 0;
  /** @invariant safeInteger(j) && 0 <= j && safeInteger(cap) && widths.length === j && j <= cap */
  for (let j = 0; j < cap; j++) {
    widths.push(j);
    s += flags[widths.length - 1]!;
  }
  return s;
}
