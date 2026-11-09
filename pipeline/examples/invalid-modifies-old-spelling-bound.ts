// `Within`'s spelling where the module binds `value` and `store`: a bare key
// is never a cell (a cell is `"cell(value)"`), so the reader refuses it
// whatever the module binds.
let value: number | null = null;
let store: number | null = null;

export function size(
  xs: number[],
): Modifies<{ value: "init"; store: "init" }, number> {
  value ??= xs.length;
  store ??= 0;
  return value + store;
}
