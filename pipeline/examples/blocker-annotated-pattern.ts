// A binding pattern under an annotation: the initializer meets the
// annotation, and the pattern reads its parts at the annotation's type.
// Census functions:
// claim-text.mts#lift, claim-text.mts#liftClause, claim-text.mts#liftLabels,
// claim-text.mts#liftSignatures, claim-text.mts#liftType,
// claim-text.mts#treeAtom, intrinsics.mts#iterationIntrinsic,
// regexp.mts#dispatchIntrinsic,
// array-prototype.mts#nativeCollectionViewDefinition.
export function use(pair: [number, number]): number {
  const [x, y]: [number, number] = pair;
  return x + y;
}

export function first(
  list: boolean,
  xs: readonly string[],
): string | undefined {
  const [head, rest]: readonly (string | undefined)[] = list ? xs : [];
  return rest ?? head;
}

export function fields(o: { a: number; b: string }): string {
  const { a, b }: { a: number; b: string } = o;
  let [n, s]: [number, string] = [a, b];
  return s + n;
}
