// A written `let` pattern binding is a cell whose contract is its initial
// value's type, widened: a string is no number (TypeScript rejects the
// write too).
export function write(o: { a: number }): number {
  let { a } = o;
  // @ts-expect-error a string is not a number
  a = "x";
  return 0;
}
