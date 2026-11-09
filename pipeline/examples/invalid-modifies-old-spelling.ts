// A frame in `Within`'s spelling, `{ value: …; store: … }`: the class keys
// are `values` and `stores`, and a bare key is never a module cell, so the
// reader refuses `value` as a key of no location.
export function size(
  xs: number[],
): Modifies<{ value: "keep"; store: "keep" }, number> {
  return xs.length;
}
