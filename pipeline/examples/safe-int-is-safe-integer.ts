// `Number.isSafeInteger(v)` answering other than `false` states `v` a safe
// integer (SOURCE-CONTRACTS.md, "Library globals"): on its true branch
// `v` is bound at `SafeInt` and bounds an index with no `safeInteger(v)`.

export function asInt(v: number): SafeInt {
  if (Number.isSafeInteger(v)) {
    const k: SafeInt = v;
    return k;
  }
  return 0;
}

export function get(xs: number[], v: number): number {
  if (Number.isSafeInteger(v)) {
    if (0 <= v && v < xs.length) return xs[v]!;
  }
  return 0;
}

// A union of a safe literal and a fraction, tested: read within `int` on
// the true branch.
export function pick(b: boolean): SafeInt {
  const x = b ? 1 : 0.5;
  if (Number.isSafeInteger(x)) return x;
  return 0;
}
