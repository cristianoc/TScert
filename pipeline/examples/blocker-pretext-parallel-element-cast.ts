// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// after its rewrites of element reads elsewhere): line-break.ts#countPreparedLines.
// Refusal: reject: closure expression claim: evidence search failed.
// An element read asserted with `as` to the element type without
// `undefined`, `advances[i] as number[] | null` with `i < widths.length`:
// nothing relates the two lengths, so the read past `advances`' end is
// `undefined`, which passes the test against `null` and throws at its
// `length` (run under Node). The read that verifies checks the element,
// `defined(advances[i])`.
export function advanceCount(
  widths: number[],
  advances: (number[] | null)[],
): number {
  let count = 0;
  for (let i = 0; i < widths.length; i++) {
    const fit = advances[i] as number[] | null;
    if (fit !== null) count += fit.length;
  }
  return count;
}
