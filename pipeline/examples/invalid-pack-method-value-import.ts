// A pack parameter's instance must lie within its bound, position by
// position: `Params extends number[]` admits no string actual.
import { maker, Box } from "@fixture/lib";
export function build(): number {
  // @ts-expect-error: a string is no number
  return maker.make(Box, "a").v;
}
