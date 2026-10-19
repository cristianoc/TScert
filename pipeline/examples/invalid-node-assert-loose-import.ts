// `node:assert`, whose `equal` is loose equality, is not reviewed: its import
// is refused.
import assert from "node:assert";

export function check(n: number): void {
  assert.equal(n, 1);
}
