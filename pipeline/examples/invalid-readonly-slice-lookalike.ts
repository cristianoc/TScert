// The install of readonly-frame-install-copy, of a copy no standard
// library array makes: `xs.slice()` calls the caller's own method, which
// returns the caller's array, so the caller may truncate the array `walk`
// reads (under Node, `install(0, { slice() { return a; } })` then
// `walk(h, () => { a.length = 0; })` reads `undefined`,
// tests/node-runs.mts). The call is of code outside the module, its result
// a value entering it: (O) refuses the store.
/** A handle: widths and flags of one length. */
export type H = {
  readonly widths: readonly number[];
  readonly flags: readonly number[];
};
type Rep = { widths: readonly number[]; readonly flags: readonly number[] };
/** Anything with a `slice()`. */
export type Sliced = { slice(): number[] };

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

export function install(i: number, xs: Sliced): void {
  const r = handles[i];
  if (r !== undefined) r.widths = xs.slice();
}

export function walk(h: H, visit: () => void): number {
  const n = h.widths.length;
  let sum = 0;
  for (let i = 0; i < n; i++) {
    visit();
    sum += h.widths[i] as number;
  }
  return sum;
}
