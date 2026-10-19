// A default import binds the module's `default` export: here a function
// declaration of the program, certified as a named import's is, so a `map`
// callback calling it is preserving and the result is dense.
import scale from "@fixture/default-function";

export function twice(n: number): number {
  return scale(scale(n));
}
export function scaled(xs: number[]): number[] {
  return xs.map((x) => scale(x));
}
