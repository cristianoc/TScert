// A function claiming `base !== null || result.flags.length === result.widths.length`
// returns mismatched arrays when `base === null`: refused. Under Node, calling
// `build(null)` returns `{ flags: Uint8Array(2), widths: [] }`, violating the
// postcondition so `widths[0]` is `undefined`.
type Pair = { flags: Uint8Array; widths: number[] };

/** @ensures base !== null || result.flags.length === result.widths.length */
export function build(base: Pair | null): Pair {
  if (base !== null) return base;
  return { flags: new Uint8Array(2), widths: [] };
}
