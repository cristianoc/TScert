// The Read-only frames note's Example "A member that shortens", its record
// a parameter (docs/drafts/framed-acceptance.md, "Milestone 2", the natives
// the realm does not model): trim pops the array of the record it is given,
// a native call whose steps are the component's, so the node protocol is
// any at the spine of outside storage and walk is refused by the protocol.
// A visitor calling trim(h) makes walk read past the array (NaN under
// Node, tests/node-runs.mts).
export type H = { readonly widths: readonly number[] };
export type Rep = { readonly widths: number[] };
export function trim(r: Rep): void {
  r.widths.pop();
}
export function walk(h: H, visit: () => void): number {
  const w = h.widths;
  const n = w.length;
  let sum = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && w.length === n */
  for (let i = 0; i < n; i++) {
    visit();
    sum += w[i]!;
  }
  return sum;
}
