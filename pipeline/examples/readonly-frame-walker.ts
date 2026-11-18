// A module whose handle a walker reads across a visitor
// (docs/drafts/tolerant-frames-note/note.tex, "Calls of code outside a
// component"): `prepare` allocates the widths the handle exposes at a
// read-only type, and `walk` changes nothing. The checks (S), (K) and (O) of
// the read-only frame hold of the module's code.
/** A handle: the widths a walker reads. */
export type H = { readonly widths: readonly number[] };

export function prepare(n: number): H {
  const widths: number[] = [];
  for (let i = 0; i < n; i++) widths.push(1);
  return { widths };
}

export function walk(h: H, visit: () => void): number {
  const w = h.widths;
  let sum = 0;
  for (let i = 0; i < w.length; i++) {
    visit();
    sum += w[i] ?? 0;
  }
  return sum;
}
