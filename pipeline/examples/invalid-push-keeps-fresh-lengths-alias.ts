// A push into a constant that may hold an older array: only a constant
// holding an array literal's object has its store field apart from the older
// arrays', and `texts`, initialized by a conditional, may be `flags` itself.
// `texts.push(…)` then grows `flags`, so `other.length === flags.length` does
// not survive and the read of `other` at `flags.length - 1` is refused. Under
// Node, `fill([1], [5], false)` reads `other[1]`, `undefined` at `number`.

/** @requires other.length === flags.length && 1 <= flags.length */
export function fill(flags: number[], other: number[], fresh: boolean): number {
  const texts: number[] = fresh ? [] : flags;
  texts.push(0);
  return other[flags.length - 1]!;
}
