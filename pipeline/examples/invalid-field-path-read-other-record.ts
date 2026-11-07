// A read bounded by another record's field: the clause bounds `i` by
// `a.widths.length`, the body reads `b.widths[i]!`, `undefined` at `number`
// past `b`'s end (run under Node: `across({ widths: [1, 2] }, { widths: [3] })`
// is `undefined`).
type Row = { widths: number[] };

/** @requires safeInteger(i) && 0 <= i && i < a.widths.length */
function other(a: Row, b: Row, i: number): number {
  return b.widths[i]!;
}

export function across(a: Row, b: Row): number {
  if (a.widths.length > 1) return other(a, b, 1);
  return 0;
}
