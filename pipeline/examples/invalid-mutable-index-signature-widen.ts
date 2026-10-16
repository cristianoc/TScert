// TypeScript lets a mutable dictionary of `true` pass as one of `boolean`,
// through which a `false` could be stored where `true` is promised.
function widen(x: { [key: string]: true }): { [key: string]: boolean } {
  return x;
}
