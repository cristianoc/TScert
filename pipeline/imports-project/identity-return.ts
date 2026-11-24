// Exported identity-shaped functions whose return-alias postconditions are
// inferred by the pass and published across module interfaces: direct return,
// local alias binding, and multi-return branches.
/** @invariant this.flags.length === this.widths.length */
export type Pair = { flags: Uint8Array; widths: number[] };

export function directId(p: Pair): Pair {
  return p;
}

export function localId(p: Pair): Pair {
  const y = p;
  return y;
}

export function branchId(p: Pair, flag: boolean): Pair {
  if (flag) return p;
  const y = p;
  return y;
}
