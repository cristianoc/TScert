// A present `undefined` at an optional field: `x?: number` is absent or holds
// a number, the exact reading (as `exactOptionalPropertyTypes`), so the
// literal does not meet it; `x?: number | undefined` would.
type Opt = { x?: number };
export function make(): Opt {
  const o: Opt = { x: undefined };
  return o;
}
