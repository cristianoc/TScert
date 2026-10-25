// A binding pattern needs its written annotation checked.
// Census functions:
// claim-text.mts#lift, claim-text.mts#liftClause, claim-text.mts#liftLabels,
// claim-text.mts#liftSignatures, claim-text.mts#liftType,
// claim-text.mts#treeAtom, intrinsics.mts#iterationIntrinsic,
// regexp.mts#dispatchIntrinsic.
export function use(pair: [number, number]): number {
  const [x, y]: [number, number] = pair;
  return x + y;
}
