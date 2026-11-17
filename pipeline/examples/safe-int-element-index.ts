// An element of a `SafeInt[]` used as an index under a quantified
// precondition: `forall j in idx: …` bounds every element of `idx` by
// `xs.length` with no `safeInteger(idx[j])`, the element type stating each a
// safe integer.

/** @requires forall j in idx: 0 <= idx[j] && idx[j] < xs.length */
export function gather(xs: number[], idx: SafeInt[]): number {
  let s = 0;
  for (let j = 0; j < idx.length; j++) s = s + xs[idx[j]!]!;
  return s;
}
