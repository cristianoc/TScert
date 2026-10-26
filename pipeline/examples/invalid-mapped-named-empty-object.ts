// A mapped type over an empty named record admits primitives (`f(1)`), so a
// value at it is no object.
interface Empty {}
export function f(x: Readonly<Empty>): object {
  return x;
}
