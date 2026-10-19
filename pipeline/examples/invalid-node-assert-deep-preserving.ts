// A passing deep comparison traverses enumerable symbol properties, whose
// getters are code of the client's that may shrink the array `map` reads
// (run under Node: the result has a hole): it states no effect, and a `map`
// calling it is not preserving.
import assert from "node:assert/strict";

type Row = { readonly a: number };
export function checked(xs: Row[], probe: Row): Row[] {
  return xs.map((x: Row) => {
    assert.deepEqual(x, probe);
    return x;
  });
}
