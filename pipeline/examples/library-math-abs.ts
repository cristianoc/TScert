// `Math.abs` of a number runs no conversion code and writes nothing: the
// absolute difference of two numbers is a number. The ReScript backend's
// `Math.abs` compiles to this call.
export function absDiff(a: number, b: number): number {
  return Math.abs(a - b);
}
