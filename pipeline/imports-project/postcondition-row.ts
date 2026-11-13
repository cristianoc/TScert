// A module whose function states a postcondition of its result over its
// parameter (pretext's line-breaks.ts `getWebKitLineBreaks`).
/** @ensures result.length === source.length + 1 */
export function breaksOf(source: string): Uint8Array {
  return new Uint8Array(source.length + 1);
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function at(xs: number[], i: number): number {
  return xs[i]!;
}
