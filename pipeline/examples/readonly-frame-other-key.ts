// The Read-only frames note, Example "A member writing another key"
// (docs/drafts/readonly-frames-note/note.tex): the member writes the key
// label of a record a caller passes writable, so the component's protocol
// changes outside storage only at the key label and keeps the parts of
// h.flags and its spine. The fact h.flags.length === n across visit(i)
// holds: both regions, of outside storage, are read as protected, the
// crossing of h at H their witness (§4.1), and the unit is accepted under
// the client obligation of its component.
export type H = { readonly widths: readonly number[]; readonly flags: readonly number[] };
export type Note = { label: string };

export function rename(n: Note, s: string): void {
  n.label = s;
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
