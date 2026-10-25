// Sorting the fresh result of filter needs its store mutation recognised as
// confined to fresh storage.
// Census functions:
// intrinsics.mts#enumIntrinsic, intrinsics.mts#enumMembersTerm.
export function use(
  values: number[],
): Within<{ value: "any"; store: "grow" }, number[]> {
  return values.filter((x) => x > 0).sort((a, b) => a - b);
}
