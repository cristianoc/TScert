// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#getExtraSpacings,
// gecko-line-breaks.ts#markWordBreaks (`cache[cacheAt++]` in a loop's body,
// then `cache = segmentComplex(units)`).
// A `for` loop whose update writes its bindings inside an expression
// (`start = ends[i++]`, here `start = i, i++`): no closure mentions them,
// so they are slots the update rebinds (SOURCE-ELABORATION.md, "Slot or
// cell"), and a binding given a call's result, `extras = zeros(count)`,
// needs no fact stating it apart from them.
function zeros(count: number): number[] {
  return new Array<number>(count).fill(0);
}

export function extraSpacings(count: number): number[] {
  let extras: number[] = [];
  for (let i = 0, start = 0; i < count; start = i, i++) {
    if (extras.length === 0) extras = zeros(count);
    extras.push(start);
  }
  return extras;
}
