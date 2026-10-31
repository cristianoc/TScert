// String conversion of an unknown value.
// Census functions:
// claim-text.mts#atomText
// claim-text.mts#bareAtomText
// claim-text.mts#typeText
// claim-text.mts#printType
// claim-text.mts#liftClause
// claim-text.mts#liftSignatures
// claim-text.mts#liftType
// claim-text.mts#liftLabels
// claim-text.mts#treeAtom
// claim-text.mts#lift
export function print(value: unknown): string {
  return String(value);
}
