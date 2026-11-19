// A precondition on a function with an optional parameter: `at` reads
// `xs[i]` below the length its `@requires` states, and its last parameter is
// optional. The clause names the required parameters as the call passes
// them, and the optional one admits `undefined`.
// Pretext: line-break.ts walkPreparedLinesRaw (an optional visitor and a
// defaulted stats) and walkPreparedComplexLines, whose cursor and handle
// relations are their callers' to establish.
/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function at(xs: number[], i: number, scale?: number): number {
  return xs[i]! * (scale ?? 1);
}
