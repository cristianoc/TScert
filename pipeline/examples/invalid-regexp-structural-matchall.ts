// `matchAll` reads its argument's `Symbol.match` and `flags` and converts
// `flags` before dispatching, which only a literal's regex makes free of
// client code: a `RegExp` parameter states no `[Symbol.matchAll]`, and the
// call is refused.
export function count(re: RegExp, s: string): number {
  return [...s.matchAll(re)].length;
}
