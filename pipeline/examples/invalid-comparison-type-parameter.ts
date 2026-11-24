// A type parameter's members are no clause's: `x === y` may hold, as at
// `f("a", "a", [])`, and the read past the empty array returns `undefined`.
export function f<T>(x: "a" | "b", y: T, xs: number[]): number {
  if (x === y) {
    return xs[0]!;
  }
  return 0;
}
