// A visitor typed `() => void` may return any value, which TypeScript
// admits: `walk` stores what its visitor returns into the handle it reads,
// so a visitor returning an array the caller holds writable, and truncating
// it at the next visit, makes the walker read `undefined` (under Node,
// tests/node-runs.mts). The visitor's result is a value entering the
// module, at a position whose declared type bounds nothing: (O) refuses the
// store.
/** A handle: the widths a walker reads. */
export type H = { readonly widths: readonly number[] };
type Rep = { widths: readonly number[] };

const handles: Rep[] = [];

export const prepare = (n: number): H => {
  const widths: number[] = [];
  for (let i = 0; i < n; i++) widths.push(1);
  const r: Rep = { widths };
  handles.push(r);
  return r;
};

export const walk = (h: H, visit: () => void): number => {
  const got: unknown = visit();
  const r = handles[0];
  if (r !== undefined && Array.isArray(got)) r.widths = got;
  const n = h.widths.length;
  let sum = 0;
  for (let i = 0; i < n; i++) {
    visit();
    sum += h.widths[i] as number;
  }
  return sum;
};
