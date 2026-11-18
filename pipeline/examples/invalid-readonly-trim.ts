// Paper I's member that shortens (docs/drafts/readonly-frames-note/note.tex,
// "A member that shortens"): `trim` pops the array a handle exposes, so the
// protocol has `any` at that array's spine, and a visitor that calls `trim`
// makes `walk` read past the array (under Node, `walk(h, () => trim(0))`
// reads `undefined`, tests/node-runs.mts).
/** A handle: the widths a walker reads. */
export type H = { readonly widths: readonly number[] };
type Rep = { readonly widths: number[] };

const handles: Rep[] = [];

export function prepare(n: number): H {
  const widths: number[] = [];
  for (let i = 0; i < n; i++) widths.push(1);
  const r: Rep = { widths };
  handles.push(r);
  return r;
}

export function trim(i: number): void {
  const r = handles[i];
  if (r !== undefined) r.widths.pop();
}

export function walk(h: H, visit: () => void): number {
  const w = h.widths;
  const n = w.length;
  let sum = 0;
  for (let i = 0; i < n; i++) {
    visit();
    sum += w[i] as number;
  }
  return sum;
}
