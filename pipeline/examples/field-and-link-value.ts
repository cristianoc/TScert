// A field path and the name its read link says it holds are one term: a
// fact is stored over the name, and a check reads it over either.
// `fieldToName`'s precondition states the bound over the field `box.at`;
// the read `const i = box.at` gives the name `i`, and the element read
// `xs[i]` is bounded by the field's fact. `nameToField`'s test states the
// bound over the name `i`; the call `at(xs, box)` requires it over the
// field `box.at`, which the link `box.at ↦ i` gives.
type Box = { at: number };

/** @requires safeInteger(box.at) && 0 <= box.at && box.at < xs.length */
export function fieldToName(xs: number[], box: Box): number {
  const i = box.at;
  return xs[i]!;
}

/** @requires safeInteger(box.at) && 0 <= box.at && box.at < xs.length */
function at(xs: number[], box: Box): number {
  return xs[box.at]!;
}

export function nameToField(xs: number[], box: Box): number {
  const i = box.at;
  if (Number.isSafeInteger(i) && i >= 0 && i < xs.length) return at(xs, box);
  return 0;
}
