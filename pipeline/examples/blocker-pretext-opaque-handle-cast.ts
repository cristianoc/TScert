// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of TScert issue #94):
// rich-inline.ts#getInternalPreparedRichInline. layout.ts states its
// handle's type as the record preparation builds, and asserts none.
// Refusal: reject: closure expression claim.
// A branded opaque handle asserted with `as` to its internal record: no
// claim of the handle meets the internal type's fields.
declare const handleBrand: unique symbol;
export type Handle = { readonly [handleBrand]: true };
type Internal = Handle & { widths: number[] };

function internal(handle: Handle): Internal {
  return handle as Internal;
}

export function count(handle: Handle): number {
  return internal(handle).widths.length;
}
