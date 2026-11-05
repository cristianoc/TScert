// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// rich-inline.ts#prepareRichInline.
// `new Array<T>(n).fill(v)`: the construct written directly as the receiver
// of `fill` of one argument is a fresh dense `T[]` of the filled value
// (SOURCE-CONTRACTS.md, "`new Array` filled at once").
export function slots(n: number): (number[] | null)[] {
  return new Array<number[] | null>(n).fill(null);
}
