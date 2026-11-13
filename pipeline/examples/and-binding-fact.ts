// A Boolean binding of a conjunction whose left side compares
// (`const before = mi > from && …`): the merge of its two arms keeps the
// comparison guarded by the binding's `false` (`before === false || from <
// mi`), and a later test of the binding releases it for the read at `mi - 1`
// (pretext's `measureAnalysis`, its `spaceBefore`).
function isSpace(n: number): boolean {
  return n === 1;
}

/** @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= flags.length */
export function laterTest(flags: number[], from: number, to: number): number {
  let s = 0;
  for (let mi = from; mi < to; mi++) {
    const before = mi > from && isSpace(flags[mi - 1]!);
    if (before && flags[mi]! > 2) s += flags[mi - 1]!;
  }
  return s;
}
