// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// layout.ts#measureNaturalWidth, rich-inline.ts#findWholeLine,
// rich-inline.ts#prepareRichInline.
// `Number.POSITIVE_INFINITY`, a non-writable data property of `Number`: its
// read runs no code and is a number.
export function widest(): number {
  return Number.POSITIVE_INFINITY;
}
