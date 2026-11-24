// `nameToField` with the field written between the test and the call: the
// test's bound is over the name `i`, which the field no longer holds, so
// nothing bounds `box.at` at the call (run under Node:
// `nameToField([1], { at: 0 })` returns `undefined` at `number`).
type Box = { at: number };

/** @requires safeInteger(box.at) && 0 <= box.at && box.at < xs.length */
function at(xs: number[], box: Box): number {
  return xs[box.at]!;
}

export function nameToField(xs: number[], box: Box): number {
  const i = box.at;
  if (Number.isSafeInteger(i) && i >= 0 && i < xs.length) {
    box.at = i + 1;
    return at(xs, box);
  }
  return 0;
}
