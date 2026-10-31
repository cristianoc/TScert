// Census functions: claim-text.mts#atomText, claim-text.mts#bareAtomText,
// claim-text.mts#typeText, claim-text.mts#printType, claim-text.mts#liftClause,
// claim-text.mts#liftSignatures, claim-text.mts#liftType, claim-text.mts#liftLabels,
// claim-text.mts#treeAtom, claim-text.mts#lift; type-probe.mts#makeProbe.
// A callback with an ordinary effect gives map a result with holes;
// the following join needs a dense array.
export function render(xs: string[], text: (x: string) => string): string {
  return xs.map((x) => text(x)).join(", ");
}
