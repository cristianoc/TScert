// An instantiation TypeScript accepts only through array covariance:
// `string[]` is not a `(string | number)[]`, since the callee may store a
// number into it, and a string array reader would then read a number.
function push<T>(xs: T[], x: T): T[] {
  return xs;
}

export function widen(words: string[]): (string | number)[] {
  return push<string | number>(words, 1);
}
