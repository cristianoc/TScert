// P22's walker serializing its array with a replacer, `JSON.stringify(xs,
// keep)`: `JSON.stringify` passes a wrapper object it allocates to the
// replacer as `this` (ECMA-262, SerializeJSONProperty), so its contract
// states `passesOwnAllocations` and the framed plan reads the call as a call
// of outside code (SOURCE-CONTRACTS.md, "A built-in's trust fields"). No
// contract states `JSON.stringify` at a function replacer, so the call is
// refused.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

function keep(_key: string, value: unknown): unknown {
  return value;
}

export function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 };
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    s += JSON.stringify(xs, keep).length;
    s += xs[c.i]!;
    c.i++;
  }
  return s;
}
