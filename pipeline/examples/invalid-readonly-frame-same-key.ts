// The Read-only frames note, Example "A member writing the same key"
// (docs/drafts/readonly-frames-note/note.tex): the member writes the
// handle's own key flags, replacing its array. Its write is charged at the
// key flags of outside storage, so the component's protocol is any at a
// part of h.flags, above the invariant's grow, and walk is refused by the
// protocol. A visitor that calls reset(h) at its first visit makes walk
// read past the new array (NaN under Node, tests/node-runs.mts).
export type H = { readonly widths: readonly number[]; readonly flags: readonly number[] };

export function reset(h: { flags: readonly number[] }): void {
  h.flags = [];
}

type Visitor = (i: number) => Modifies<{ values: "any"; spines: "grow" }, void>;

/** @requires h.flags.length === h.widths.length */
export function walk(h: H, visit: Visitor): number {
  const n = h.widths.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && h.flags.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += h.flags[i]!;
  }
  return s;
}
