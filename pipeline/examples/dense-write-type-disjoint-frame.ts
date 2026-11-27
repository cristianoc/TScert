// An in-bounds element write on a `Dense<number[]>` has footprint
// `{arr[#]: any}` (spines untouched) and its element cells are type-disjoint
// from arrays of `(number[] | null)` (including unions of distinct array
// clauses and `null`), so quantified invariants over those arrays survive
// without any `!==` / `apart` precondition between `number[]` and
// `(number[] | null)[]`.

/**
 * @requires safeInteger(count) && 0 <= count
 * @ensures result.length === count
 */
function zeros(count: number): Modifies<{}, Fresh<Dense<number[]>>> {
  const out: Dense<number[]> = [];
  /** @invariant safeInteger(count) && safeInteger(i) && 0 <= i && i <= count && out.length === i */
  for (let i = 0; i < count; i++) out.push(0);
  return out;
}

/**
 * @requires safeInteger(base) && safeInteger(count) && 0 <= base && 0 <= count && base + count <= advances.length
 * @ensures result.length === count
 * @ensures forall k in result: advances[base + k] === null || result[k] === null || advances[base + k].length <= result[k].length
 */
function emptyExtras(
  advances: (number[] | null)[],
  base: number,
  count: number,
): Modifies<{}, Fresh<Dense<(number[] | null)[]>>> {
  const out: Dense<(number[] | null)[]> = [];
  const nil: number[] | null = null;
  let i = 0;
  /** @invariant safeInteger(base) && safeInteger(count) && safeInteger(i) && 0 <= base && 0 <= i && i <= count && base + count <= advances.length && out.length === i
   *  @invariant forall k in out: advances[base + k] === null || out[k] === null || advances[base + k].length <= out[k].length */
  for (; i < count; i++) {
    const idx = base + i;
    const a = advances[idx];
    if (a === undefined) throw new RangeError("index");
    if (a === null) out.push(nil);
    else out.push(nil);
  }
  return out;
}

/**
 * @requires safeInteger(base) && safeInteger(n) && 0 <= base && 0 <= n && n <= 4294967295 && widths.length === base + n && bfa.length === base + n
 * @requires forall i in bfa: bfa[i] === null || 1 <= bfa[i].length
 * @ensures forall i in bfa: bfa[i] === null || 1 <= bfa[i].length
 * @ensures result === null || result.length === n
 * @ensures result === null || forall k in result: bfa[base + k] === null || result[k] === null || bfa[base + k].length <= result[k].length
 */
export function denseWritePreservesDisjointQuantified(
  widths: Dense<number[]>,
  bfa: (number[] | null)[],
  extrasInit: Dense<(number[] | null)[]> | null,
  base: number,
  n: number,
  flag: boolean,
): Dense<(number[] | null)[]> | null {
  let extras: Dense<(number[] | null)[]> | null =
    extrasInit !== null && extrasInit.length === n ? emptyExtras(bfa, base, n) : null;
  let dhc: Dense<number[]> | null = null;
  /**
   * @invariant safeInteger(base) && safeInteger(n) && safeInteger(s) && 0 <= base && 0 <= s && s <= n && n <= 4294967295 && widths.length === base + n && bfa.length === base + n
   * @invariant dhc === null || dhc.length === n
   * @invariant extras === null || extras.length === n
   * @invariant forall i in bfa: bfa[i] === null || 1 <= bfa[i].length
   * @invariant extras === null || forall k in extras: bfa[base + k] === null || extras[k] === null || bfa[base + k].length <= extras[k].length
   */
  for (let s = 0; s < n; s++) {
    widths[base + s] = s + 1;
    if (flag) {
      if (extras === null) {
        extras = emptyExtras(bfa, base, n);
      }
      dhc ??= zeros(n);
      dhc[s] = 99;
    }
  }
  return extras;
}
