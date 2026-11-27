// An object literal that includes an optional property `items` must not be
// treated as omitting it: when `items.extras` is shorter than `widths`, the
// guarded invariant is false.
type Items = {
  extras: number[] | null;
};

/** @invariant this.items === undefined || this.items.extras === null || this.widths.length <= this.items.extras.length */
type Data = {
  widths: number[];
  items?: Items;
};

export function makeWithShortExtras(): Data {
  const result: Data = { widths: [1, 2], items: { extras: [10] } };
  return result;
}
