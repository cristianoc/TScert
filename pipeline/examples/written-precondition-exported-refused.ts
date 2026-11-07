// A precondition on an exported function: a caller outside its module
// establishes nothing, so the front end refuses it.

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function at(xs: number[], i: number): number {
  return xs[i]!;
}
