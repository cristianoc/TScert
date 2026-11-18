// Paper I's guarantee example (docs/drafts/readonly-frames-note/note.tex,
// "A guarantee"): `install` replaces a handle's widths by a copy of the
// caller's array when its length is the flags'. The protocol has `any` at
// the replaced field; the invariant equating the two lengths is the
// guarantee's candidate, and every write to its support is checked.
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

export function install(i: number, xs: number[]): void {
  const r = handles[i];
  if (r !== undefined && xs.length === r.flags.length) r.widths = xs.slice();
}

export function walk(h: H, visit: () => void): number {
  let sum = 0;
  for (let i = 0; i < h.flags.length; i++) {
    visit();
    sum += h.widths[i] ?? 0;
  }
  return sum;
}
