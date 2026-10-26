// A mapped type over an empty named record is `{}`, every value but null
// and undefined: a number meets it.
interface Empty {}
export function make(): Readonly<Empty> {
  return 1;
}
