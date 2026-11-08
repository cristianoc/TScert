// An imported function's precondition violated by its caller:
// `at(xs, xs.length)` reads past the end, so `at` returns `undefined` at
// `number`; under Node, `last([1, 2])` is `undefined`.
import { at } from "@fixture/bounded";

export function last(xs: number[]): number {
  return at(xs, xs.length);
}
