// An importer violating an imported function's precondition: `at` requires
// `i < xs.length` and is passed `xs.length`. The call is checked at the
// signature the import is read at, so it is refused; under Node, `past([1])`
// returns `undefined`, not a number.
import { at } from "@fixture/postcondition-row";

export function past(xs: number[]): number {
  return at(xs, xs.length);
}
