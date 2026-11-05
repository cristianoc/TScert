// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// after its rewrites of element reads elsewhere):
// line-break.ts#stepPreparedSimpleLineGeometry.
// Refusal: reject: source expression obligation: no derivation of its cast
// claim.
// A non-null assertion of an element whose presence another argument is
// taken to imply, `startAdvances!` where `graphemeIndex > 0` (a cursor inside
// a segment has its grapheme advances): nothing relates the two arguments,
// so a `null` element reaches the assertion and its `length` throws (run
// under Node). The read that verifies checks the value,
// `present(startAdvances)`.
export function firstAdvanceCount(
  advances: (number[] | null)[],
  start: number,
  graphemeIndex: number,
): number {
  const startAdvances = advances[start];
  if (graphemeIndex > 0 || startAdvances !== null) {
    const fit = startAdvances!;
    return fit.length;
  }
  return 0;
}
