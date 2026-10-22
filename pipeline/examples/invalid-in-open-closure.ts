// In a callback as in a function, an open record may own a key its type does
// not name: `{ b: "", a: "x" }` is a `{ b: string }`. The passed test keeps
// that arm, so `x` is not an `{ a: number }` there.
export function first(xs: ({ a: number } | { b: string })[]): { a: number }[] {
  return xs.map((x) => ("a" in x ? x : { a: 0 }));
}
