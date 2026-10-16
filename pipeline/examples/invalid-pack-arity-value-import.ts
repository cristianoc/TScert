// A class taking a number does not meet a construct signature whose rest is
// the empty pack: `new (...params: []) => Box` constructs with no actual.
import { maker, Box } from "@fixture/lib";
export function build(): number {
  // @ts-expect-error: Box's constructor needs its number
  return maker.make(Box).v;
}
