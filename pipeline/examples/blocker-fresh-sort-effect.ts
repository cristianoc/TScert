// Sorting within {value: any, store: grow}: at a comparator whose store
// changes are at most `grow`, `sort` grows its receiver's store over the
// whole call, whether the receiver is the fresh result of `filter` or a
// parameter. A closure calling `Number`, which the module also reads as an
// object (`Number.isFinite`), is within the call signature's footprint.
// Census functions:
// intrinsics.mts#enumIntrinsic, intrinsics.mts#enumMembersTerm,
// fragment-classes.mts#enumEntries, fragment-classes.mts#enumStmt,
// fragment-classes.mts#enumObjectTerm.
export function use(
  values: number[],
): Modifies<{ values: "any"; stores: "grow" }, number[]> {
  return values.filter((x) => x > 0).sort((a, b) => a - b);
}

export function inPlace(
  values: number[],
): Modifies<{ values: "any"; stores: "grow" }, number> {
  return values.sort((a, b) => b - a).length;
}

export function indexKeys(
  keys: string[],
): Modifies<{ values: "any"; stores: "grow" }, string[]> {
  const index = (k: string) => Number.isFinite(Number(k));
  return keys.filter((k) => index(k)).sort((a, b) => Number(a) - Number(b));
}

export function dense(xs: number[]): number[] {
  return xs.map((x) => use(xs).length + inPlace(xs) + x);
}
