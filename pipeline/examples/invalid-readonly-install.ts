// The walker's module of readonly-frame-walker, with a member that installs
// a caller's array in a handle: `install` stores the `xs` it is given into
// the record `prepare` exposed, which the module keeps, so the caller may
// truncate the array `walk` reads through the handle (under Node,
// `install(0, xs)` then `walk(h, () => { xs.length = 0; })` reads
// `undefined`, tests/node-runs.mts). (O) refuses the store.
/** A handle: the widths a walker reads. */
export type H = { readonly widths: readonly number[] };
type Rep = { widths: readonly number[] };

const handles: Rep[] = [];

export function prepare(n: number): H {
  const widths: number[] = [];
  for (let i = 0; i < n; i++) widths.push(1);
  const r: Rep = { widths };
  handles.push(r);
  return r;
}

export function install(i: number, xs: number[]): void {
  const r = handles[i];
  if (r !== undefined) r.widths = xs;
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
