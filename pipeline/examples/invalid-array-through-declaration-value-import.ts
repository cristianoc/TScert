// The file writes no array type; `map`'s contract still applies to the array
// the imported value's declaration states. A callback writing a captured
// `let` is no heap-preserving one, so `map` promises a sparse result, which
// is no `Numbers` (`number[]`, every element a number).
import { trio, type Numbers } from "@fixture/lib";

export function counted(): Numbers {
  let calls = 0;
  return trio().map((x: number): number => {
    calls = calls + 1;
    return x + calls;
  });
}
