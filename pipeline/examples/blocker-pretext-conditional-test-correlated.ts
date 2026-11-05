// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// after its rewrites of element reads elsewhere):
// line-break.ts#stepPreparedSimpleLineGeometry, past its first refusal
// (blocker-pretext-argument-implied-assertion).
// Refusal: reject: source expression obligation: no derivation of its cast
// claim.
// A non-null assertion of a field under a conditional whose test repeats
// that of the `if` before it: `g > 1 ? extras.inside !== null : extras.fill
// !== null` holds, and nothing is written in between, so where `g > 1` holds
// again `extras.inside` is not `null`. The join after the condition keeps
// only what both of its arms state, so the correlation of `g > 1` with each
// field's test is not known.
type Extras = { inside: number[] | null; fill: number[] | null };

export function extraCount(extras: Extras, g: number): number {
  if (g > 1 ? extras.inside !== null : extras.fill !== null)
    return g > 1 ? extras.inside!.length : extras.fill!.length;
  return 0;
}
