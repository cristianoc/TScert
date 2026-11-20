// A walker of a record passed writable (docs/drafts/framed-acceptance.md,
// "Milestone 2", the protected reading): h at no read-only position, so no
// crossing protects the spine of h.flags, and h.flags.length === n across a
// visitor letting every spine change is refused. A client popping the
// array it passed under the walker makes it read past it (NaN under Node,
// tests/node-runs.mts).
export type W = { flags: number[] };
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;

export function walk(h: W, visit: Visitor): number {
  const n = h.flags.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && h.flags.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += h.flags[i]!;
  }
  return s;
}
