// Paper I's guarantee example (docs/drafts/tolerant-frames-note/note.tex,
// "A guarantee"): `install` replaces a handle's widths by a copy of the
// caller's array of the flags' length. The copy is the array `slice()`
// allocates, holding numbers, stored at a field of a handle the module
// keeps and gives out at its read-only type, so outside code reaches it
// read-only: (O) admits the store, and the module's certificate holds.
/** A handle: widths and flags of one length. */
export type H = {
  readonly widths: readonly number[];
  readonly flags: readonly number[];
};
type Rep = { widths: readonly number[]; readonly flags: readonly number[] };

const handles: Rep[] = [];

export function prepare(n: number): H {
  const widths: number[] = [];
  const flags: number[] = [];
  for (let i = 0; i < n; i++) {
    widths.push(1);
    flags.push(0);
  }
  const r: Rep = { widths, flags };
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
