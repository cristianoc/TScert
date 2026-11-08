// A `RegExp` parameter is a native regex: its `[Symbol.replace]` at a string
// replacement writes at most its `lastIndex`, a location holding a number,
// so the dispatch at it keeps every store and `map`'s result is dense.
export function rewrite(xs: string[], re: RegExp): string[] {
  return xs.map((s) => s.replace(re, "x"));
}
