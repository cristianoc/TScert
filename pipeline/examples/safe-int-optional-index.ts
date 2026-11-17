// An index typed `SafeInt | undefined`, narrowed by a test before the
// comparisons that bound it: past `i !== undefined` the slot's type is
// `SafeInt`, which states it a safe integer.

/** @requires 0 <= i && i < xs.length */
function at(xs: number[], i: SafeInt): number {
  return xs[i]!;
}

export function maybe(xs: number[], i: SafeInt | undefined): number {
  if (i !== undefined && 0 <= i && i < xs.length) return at(xs, i);
  return 0;
}
