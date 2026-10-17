// The file writes no array type; `map`'s contract still applies to the array
// the imported value's declaration states. A callback shrinking the array it
// maps leaves holes in the result, which is no `Numbers` (`number[]`, every
// element a number): under Node, `shrunk()` is `[1, 2, <1 empty item>]`.
import { fresh, type Numbers } from "@fixture/lib";

export function shrunk(): Numbers {
  const xs = fresh();
  return xs.map((x: number): number => {
    xs.pop();
    return x;
  });
}
