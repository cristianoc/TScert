// pretext's break builders: a typed array built at `source.length + 1` has
// exactly that length. The sum of the string's length and 1 is a safe integer
// or the double 2^53, at which the construction throws a RangeError
// (ToIndex), so a normal return's view has length `length + 1`, and the
// reads below it are its elements.
/** @ensures result.length === source.length + 1 */
export function breaksOf(source: string): Uint8Array {
  const length = source.length;
  const breaks = new Uint8Array(length + 1);
  return breaks;
}

export function lastBreak(source: string): number {
  const breaks = breaksOf(source);
  return breaks[source.length]!;
}
