// The conjunction's comparison inclusive (`mi >= from`): at `mi = from = 0`
// the binding is true and the read at `mi - 1` is at `-1` (run under Node:
// `laterTest([1], 0, 1)` reads `flags[-1]`, `undefined` at `number`, and
// returns `NaN`).
function isSpace(n: number | undefined): boolean {
  return n === undefined || n === 1;
}

/** @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= flags.length */
export function laterTest(flags: number[], from: number, to: number): number {
  let s = 0;
  for (let mi = from; mi < to; mi++) {
    const before = mi >= from && isSpace(flags[mi]);
    if (before) s += flags[mi - 1]!;
  }
  return s;
}
