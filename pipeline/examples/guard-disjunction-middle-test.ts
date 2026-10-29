// A user guard's narrowing of a binding needs to survive a disjunction whose
// middle operand is a computed test of another value: where
// `!isRow(claim) || typeof other === "number" || a` is false, `claim` is a
// `Row`. Two operands, or a middle operand that is a plain binding, keep it.
// Census functions:
// diagnostic.mts#readDiagnostic
// (`!isRecord(claim) || !Array.isArray(available) || !Array.isArray(claim.context)`).
type Row = { readonly context: number | readonly number[] };
function isRow(v: Row | number): v is Row {
  return typeof v !== "number";
}
export function size(
  claim: Row | number,
  other: number | string,
  a: boolean,
): number {
  if (!isRow(claim) || typeof other === "number" || a) return 0;
  return claim.context === 0 ? 1 : 2;
}
