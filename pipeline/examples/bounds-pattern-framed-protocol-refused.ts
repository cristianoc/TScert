// The walker of bounds-pattern-unreachable-field beside an exported
// function that writes an element of a caller's array. The component's
// protocol Ψ_C (docs/drafts/framed-acceptance.md, "Charges") changes the
// elements of storage outside code may hold: a framed plan states it on
// the wire, and the pass checks the wire's at least that
// (`protocolAtLeastB`). The walker's framed plan passes its binding checks
// and its framed walk is refused at the visit; its ordinary plan is refused
// at the read after the visit.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

export function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 };
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    s += xs[c.i]!;
    c.i++;
  }
  return s;
}

export function clear(xs: number[]): void {
  if (xs.length > 0) xs[0] = 0;
}
