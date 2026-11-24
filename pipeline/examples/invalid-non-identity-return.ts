// A function returning another parameter `alt` does not alias its first
// argument `p`: learning `picked.flags.length > 0` does not justify indexing
// `p.widths[0]`: refused. Under Node, `firstWrong({ flags: new Uint8Array(0),
// widths: [] }, { flags: new Uint8Array(1), widths: [1] })` returns `undefined`
// at `number`.
/** @invariant this.flags.length === this.widths.length */
type Pair = { flags: Uint8Array; widths: number[] };

function pickSecond(_p: Pair, alt: Pair): Pair {
  return alt;
}

export function firstWrong(p: Pair, alt: Pair): number {
  const picked = pickSecond(p, alt);
  if (picked.flags.length === 0) return 0;
  return p.widths[0]!;
}
