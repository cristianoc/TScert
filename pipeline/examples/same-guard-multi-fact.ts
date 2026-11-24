// Multiple facts guarded by the same condition (`p === null`) combine in
// `guardEntails` (`sameGuardBodies`) to establish a combined guarded postcondition.
export type Out = {
  readonly flags: Uint8Array;
  readonly widths: number[];
};

/**
 * @requires safeInteger(to) && 0 <= to && to <= 1000
 * @ensures p !== null || result.flags.length === result.widths.length
 */
export function build(
  p: { readonly widths: Dense<number[]>; readonly flags: Uint8Array } | null,
  to: number,
): Out {
  const widths: Dense<number[]> = p === null ? [] : p.widths;
  const flags = p === null ? new Uint8Array(to) : p.flags;
  const base = widths.length;
  /**
   * @invariant safeInteger(i) && safeInteger(to) && safeInteger(base) && safeInteger(at) && 0 <= i && i <= to && to <= 1000 && 0 <= base && base <= 4294967295 && at === base + i && widths.length === at
   * @invariant p !== null || base === 0 && flags.length === to
   */
  for (let i = 0, at = base; i < to; i++, at++) {
    const idx = at;
    if ((idx & 0x7fffffff) !== idx || idx > widths.length)
      throw new RangeError("index");
    widths[idx] = i;
  }
  return { flags, widths };
}
