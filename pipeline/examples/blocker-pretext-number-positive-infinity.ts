// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// layout.ts#measureNaturalWidth, rich-inline.ts#findWholeLine,
// rich-inline.ts#prepareRichInline.
// Refusal: gate: Number.POSITIVE_INFINITY is not in the reviewed overlay of
// library globals: readonly POSITIVE_INFINITY: number;.
// `Number.POSITIVE_INFINITY`, not in the reviewed overlay of library
// globals.
export function widest(): number {
  return Number.POSITIVE_INFINITY;
}
