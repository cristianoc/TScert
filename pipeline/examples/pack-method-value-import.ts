// A library method whose rest is a pack parameter: the call passes a class
// and the one number its constructor takes, so `Params` is `[number]`.
import { maker, Box } from "@fixture/lib";
export function build(): number {
  return maker.make(Box, 1).v;
}
