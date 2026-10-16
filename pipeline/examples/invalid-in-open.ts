// An open record may own a key its type does not name, at any type:
// `{ b: "", a: "x" }` is a `{ b: string }`. The passed test keeps that arm,
// so `x` is not an `{ a: number }` there (TypeScript narrows to it).
export function first(x: { a: number } | { b: string }): { a: number } {
  if ("a" in x) {
    return x;
  }
  return { a: 0 };
}
