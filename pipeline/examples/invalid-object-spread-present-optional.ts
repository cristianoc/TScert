// An object spread `{ ...base, widths: [1, 2] }` may copy `items` from `base`
// even though the literal part omits `items`, so it must not claim
// `result.items === undefined`.
type Items = {
  extras: number[] | null;
};

/** @invariant this.items === undefined || this.items.extras === null || this.widths.length <= this.items.extras.length */
type Data = {
  widths: number[];
  items?: Items;
};

type Raw = {
  widths: number[];
  items?: Items;
};

export function spreadWithItems(base: Raw): Data {
  const result: Data = { ...base, widths: [1, 2] };
  return result;
}
