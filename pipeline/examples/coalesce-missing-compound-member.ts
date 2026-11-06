// A compound assignment to a member of a checked read written inline,
// `(x ?? missing()).f -= d` with `missing(): never` (pretext's `createLine`,
// rich-inline.ts): on the path where `x` is nullish the receiver is the
// result of `missing()`, which holds no value, so no write is reached there;
// on the other the member is read and written at the record's field.
export function missing(): never {
  throw new RangeError("missing value");
}

type Fragment = { occupiedWidth: number };

export function trimLast(fragments: (Fragment | undefined)[], rest: number): void {
  if (rest < 0 && fragments.length > 0)
    (fragments[fragments.length - 1] ?? missing()).occupiedWidth -= rest;
}

export function widen(fragment: Fragment | undefined, by: number): number {
  return ((fragment ?? missing()).occupiedWidth += by);
}
