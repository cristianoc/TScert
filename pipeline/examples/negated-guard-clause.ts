// Negated guard tag (`!== null`) in `@ensures` and automatic guard discharge at
// a call site passing `null`: when `base === null`, the callee builds parallel
// arrays so `result.flags.length === result.widths.length`, and the caller
// discharges `base !== null` from the `null` argument and indexes safely.
type Pair = { flags: Uint8Array; widths: number[] };

/** @ensures base !== null || result.flags.length === result.widths.length */
function build(base: Pair | null, x: number): Pair {
  if (base !== null) return base;
  const flags = new Uint8Array(2);
  const widths = [x, x + 1];
  return { flags, widths };
}

export function firstWidth(x: number): number {
  const pair = build(null, x);
  if (pair.flags.length === 0) return 0;
  return pair.widths[0]!;
}
