// A failing `equal` builds its error by running a program's
// `Error.prepareStackTrace`, which may shrink the array `map` reads (run
// under Node: the result has a hole): the throw edge preserves nothing, so a
// callback that catches the failure and goes on is not preserving.
import assert from "node:assert/strict";

export function rows(xs: number[], probe: unknown): number[] {
  return xs.map((x) => {
    try {
      assert.equal(probe, 1, "differs");
    } catch {
      return x;
    }
    return x;
  });
}
