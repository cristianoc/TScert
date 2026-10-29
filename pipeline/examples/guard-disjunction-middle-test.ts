// A user guard's narrowing of a binding survives a disjunction whose middle
// operand tests another value: where
// `!isRow(claim) || typeof other === "number" || a` is false, `claim` is a
// `Row`. Stands for the census function diagnostic.mts#readDiagnostic
// (`!isRecord(claim) || !Array.isArray(available) || !Array.isArray(claim.context)`).
// invalid-guard-disjunction-mixed-prettier-ignore is its twin, of the same spans.
type Row = { readonly context: readonly number[] };
function isRow(v: Row | number): v is Row {
  return typeof v !== "number";
}
export function size(
  claim: Row | number,
  other: number | string,
  a: boolean,
): number {
  if (!isRow(claim) || typeof other === "number" || a) return 0;
  return claim.context.length;
}
