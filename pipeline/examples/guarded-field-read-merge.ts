// Guarded nullable parallel-array length invariant through an optional nested
// object field (`opt === undefined || opt.extras === null || ...`): extracting
// `const extras = opt === undefined ? null : opt.extras` preserves the guarded
// length bound across the ternary merge and a loop.

export type OptionalExtras = {
  extras: number[] | null;
};

/** @invariant this.opt === undefined || this.opt.extras === null || this.widths.length <= this.opt.extras.length */
export type Handle = {
  widths: number[];
  opt?: OptionalExtras;
};

export function totalWithOptionalExtras(h: Handle): number {
  const { widths } = h;
  const opt = h.opt;
  const extras = opt === undefined ? null : opt.extras;
  let total = 0;
  /** @invariant safeInteger(i) && 0 <= i
   *  @invariant extras === null || widths.length <= extras.length */
  for (let i = 0; i < widths.length; i++) {
    total += widths[i]! + (extras === null ? 0 : extras[i]!);
  }
  return total;
}
