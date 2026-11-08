// A push into an array that may be the one whose length bounded the read:
// a parameter no region fact keeps apart. `texts.push(…)` grows `flags` too
// when the two are one array, so `count === flags.length` does not survive
// and the read of `other` at `flags.length - 1` is refused. Under Node,
// `fill(xs, xs, [5])` with `xs = [1]` reads `other[1]`, `undefined` at
// `number`, and answers `undefined`.

/** @requires other.length === flags.length && 1 <= flags.length */
export function fill(
  texts: number[],
  flags: number[],
  other: number[],
): number {
  texts.push(flags.length);
  return other[flags.length - 1]!;
}
