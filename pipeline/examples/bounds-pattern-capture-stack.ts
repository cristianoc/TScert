// P22's walker recording a stack on an object it allocates,
// `Error.captureStackTrace(o)`: the native installs the realm's accessor
// functions on `o`, storage that existed before its call (V8; `@types/node`
// declares it), so it is outside row (b) of the trust rows on standard
// natives and is read as outside code (SOURCE-CONTRACTS.md, "A built-in's
// trust fields"). No contract states it, so the call is refused.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

export function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 };
  const o = {};
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    Error.captureStackTrace(o);
    s += xs[c.i]!;
    c.i++;
  }
  return s;
}
