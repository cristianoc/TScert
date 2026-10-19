// `throws` calls its block, code of the client's that may shrink the array
// `map` reads (run under Node: the result has a hole): it states no effect,
// even on a passing call.
import assert from "node:assert/strict";

export function rows(xs: number[], block: () => unknown): number[] {
  return xs.map((x) => {
    assert.throws(block);
    return x;
  });
}
