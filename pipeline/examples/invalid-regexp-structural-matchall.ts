// `matchAll` reads its argument's `Symbol.match` and `flags` and converts
// `flags` before dispatching, which only a native regex makes free of client
// code: a `RegExp` parameter is no native regex, and the call is refused.
export function count(re: RegExp, s: string): number {
  return [...s.matchAll(re)].length;
}
