// Object spread `{ ...p, widths: [] }` overrides `widths`, so `p`'s invariant
// `flags.length === widths.length` does not transfer to the result: refused.
// Under Node, `extend({ flags: new Uint8Array(2), widths: [1, 2] })` returns
// `flags.length === 2` beside `widths.length === 0`.
/** @invariant this.flags.length === this.widths.length */
type Base = { flags: Uint8Array; widths: number[] };

export function extend(p: Base): Base {
  const result = { ...p, widths: [] };
  return result;
}
