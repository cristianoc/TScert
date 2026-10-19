// A namespace import of `node:assert/strict`: its members would be read at
// their declarations, refused.
import * as assert from "node:assert/strict";

export function first(xs: readonly (number | undefined)[]): number {
  const x = xs[0];
  assert.ok(x !== undefined, "a first element");
  return x;
}
