// `node:assert/strict` read through its reviewed entries: `assert` with a
// literal message is the calculus's own test, so the value narrows as an
// `if` narrows it; `ifError` promises its value is `null` or `undefined`; a
// passing `equal` writes nothing, so a `map` calling it stays dense, the
// failure leaving the callback by its throw.
import assert from "node:assert/strict";

export function first(xs: readonly (number | undefined)[]): number {
  const x = xs[0];
  assert(x !== undefined, "a first element");
  return x;
}
export function cleared(e: string | null | undefined): null | undefined {
  assert.ifError(e);
  return e;
}
export function same(xs: number[]): number[] {
  return xs.map((x) => {
    assert.equal(x, x);
    return x;
  });
}
// A failure may throw whatever a hook throws: the handler holds it at
// `unknown` (run under Node: a number a program's `prepareStackTrace` throws).
export function reason(probe: unknown): string {
  try {
    assert.equal(probe, 1, "differs");
    return "same";
  } catch (thrown) {
    return typeof thrown === "number" ? "a number" : "other";
  }
}
