// A fact survives a callback that cannot reach what the fact is about.
//
// This module is a component: the code in it is inside, all other code is
// outside, and outside code enters only through its exports, here `walk`.
// The visitor `visit` is outside code. Its type states its effect with the
// verifier's annotation `Modifies<{ values: "any"; spines: "grow" }, void>`
// (`void` is its return type): of what it can reach, it may change any
// element or field to a value its type allows (`values`), and may lengthen,
// never shorten, any array (`spines`: array lengths).
//
// Across the call `visit(c.i)` the verifier keeps `c.i < xs.length`, checking
// the two locations the fact depends on:
// - `c.i`: `c` is allocated in `walk` and never given to outside code, so no
//   outside code can reach it, and its field is unchanged;
// - the length of `xs`: `xs` came from outside, so the visitor may reach it,
//   and its stated effect lets it only grow.
// With `0 <= c.i` from the loop invariant, the read `xs[c.i]` after the call
// is in bounds.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

export function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 }; // never given to outside code
  let s = 0;
  // `@invariant`: a loop invariant the verifier checks; `safeInteger(c.i)`:
  // `c.i` is an integer within Number.MAX_SAFE_INTEGER, so `c.i++` is exact.
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i); // c.i unchanged; xs may only grow
    s += xs[c.i]!;
    c.i++;
  }
  return s;
}
