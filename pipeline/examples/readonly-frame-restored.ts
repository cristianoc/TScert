// A member that breaks a handle's invariant and restores it before it
// returns: `swap` empties the widths, then installs the old ones again.
// The guarantee is the invariants every member keeps at each write to its
// support (docs/drafts/readonly-frames-note/note.tex, "Protocol"), so the
// invariant is not kept.
/** @invariant this.widths.length === this.flags.length */
export type H = {
  readonly widths: readonly number[];
  readonly flags: readonly number[];
};
type Rep = { widths: readonly number[]; readonly flags: readonly number[] };

const handles: Rep[] = [];

export function prepare(): H {
  const r: Rep = { widths: [1, 1, 1], flags: [0, 0, 0] };
  handles.push(r);
  return r;
}

export function swap(i: number): void {
  const r = handles[i];
  if (r === undefined) return;
  const old = r.widths;
  r.widths = [];
  r.widths = old;
}
