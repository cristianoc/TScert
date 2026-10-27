// A key-adding write at a key known only at run time, in a loop, on a local's
// own fresh dictionary, as a type's metadata is collected key by key.
// Census functions:
// claim-text.mts#atomText, claim-text.mts#bareAtomText,
// claim-text.mts#typeText, claim-text.mts#printType,
// claim-text.mts#liftClause, claim-text.mts#liftSignatures,
// claim-text.mts#liftType, claim-text.mts#liftLabels,
// claim-text.mts#treeAtom, claim-text.mts#lift.
export function lengths(names: readonly string[]): { [key: string]: number } {
  const metadata: { [key: string]: number } = {};
  for (const key of names) metadata[key] = key.length;
  return metadata;
}
