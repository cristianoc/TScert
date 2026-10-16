// A kept member keeps its optional field: `x` of `Extract<S, { k: "a" }>`
// may be `undefined`, no value of `number`.
type S = { k: "a"; x?: number } | { k: "b" };
export function f(s: Extract<S, { k: "a" }>): number {
  return s.x;
}
