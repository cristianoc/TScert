// `equal` returns only where its actual is the expected value, so `v` is `3`
// after it, as its declaration's `asserts actual is T` says. The promise is
// generic, and the producer encodes no generic promise signature: the
// motivating program waits on it.
import assert from "node:assert/strict";

export function three(v: unknown): 3 {
  assert.equal(v, 3);
  return v;
}
