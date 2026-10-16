// The copied `b` is a string: the result is no `{ a: number; b: number }`.
export function copy(): { a: number; b: number } {
  return Object.assign({ a: 1 }, { b: "s" });
}
