// `<number>x` asserts what `x` is not known to be: an obligation on the
// operand, which an `unknown` does not meet.
export function downcast(x: unknown): number {
  return <number>x;
}
