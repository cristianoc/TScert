// Bounds pattern P8: the length after a write at the length.
// Fact: after xs[k] = v at k <= xs.length, xs.length = max(old length, k + 1)
// and the element at k is present.
// Pretext: prepare.ts measureAnalysis (9 sites: widths, breakableFitAdvances,
// segments, discretionaryHyphenContexts appended by index);
// rich-inline.ts prepareRichInline (1).
// The write states the index below the length (`write-bound`) and, at the
// length, the length one longer (`write-append`), so `readWritten` reads at
// the written index and the builders keep at <= widths.length at the loop head.
function note(out: number[], v: number): Modifies<{ values: "any"; stores: "grow" }, void> {
  out.push(v);
}

/** @requires safeInteger(k) && 0 <= k && k <= xs.length && k <= 1000000 */
export function readWritten(xs: number[], k: number): number {
  xs[k] = 1;
  return xs[k]!;
}

/** @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= 1000000 && widths.length <= 1000000 */
export function append(widths: number[], from: number, to: number, scratch: number[]): number {
  const base = widths.length;
  /** @invariant safeInteger(from) && safeInteger(to) && safeInteger(mi) && safeInteger(at) && safeInteger(base) && 0 <= base && base <= 1000000 && to <= 1000000 && from <= mi && at === base + mi - from && at <= widths.length */
  for (let mi = from, at = base; mi < to; mi++, at++) {
    note(scratch, mi);
    widths[at] = mi;
    if (at > base) widths[at - 1] = widths[at - 1]! + 1;
  }
  return widths.length;
}

/** @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= 1000000 && widths.length <= 1000000 */
export function appendNoCall(widths: number[], from: number, to: number): number {
  const base = widths.length;
  /** @invariant safeInteger(from) && safeInteger(to) && safeInteger(mi) && safeInteger(at) && safeInteger(base) && 0 <= base && base <= 1000000 && to <= 1000000 && from <= mi && at === base + mi - from && at <= widths.length */
  for (let mi = from, at = base; mi < to; mi++, at++) {
    widths[at] = mi;
    if (at > base) widths[at - 1] = widths[at - 1]! + 1;
  }
  return widths.length;
}
