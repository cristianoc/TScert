// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// rich-inline.ts#prepareRichInline.
// Refusal: gate: new Array(…) is not in the reviewed overlay of library
// globals.
// `new Array<T>(n).fill(v)`: the `Array` constructor of a length is not in
// the reviewed overlay of library globals.
export function slots(n: number): (number[] | null)[] {
  return new Array<number[] | null>(n).fill(null);
}
