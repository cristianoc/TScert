// A `RegExp` parameter may be any object of its members' types, whose
// `[Symbol.replace]` may run any code, here a `pop` of the array being
// mapped: the member states no footprint, so neither does the dispatch at
// it, and `map`'s result may hold holes.
export function rewrite(xs: string[], re: RegExp): string[] {
  return xs.map((s) => s.replace(re, "x"));
}
