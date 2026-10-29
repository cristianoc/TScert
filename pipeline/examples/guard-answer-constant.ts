// A guard's answer held in a constant: where the constant is `true`, the
// guarded binding is at the guard's promise, by the implication of the
// constant's slot, in a later statement's `if` and in a conditional.
type Row = { readonly context: readonly number[] };
function isRow(v: Row | number): v is Row {
  return typeof v !== "number";
}
export function size(claim: Row | number): number {
  const ok = isRow(claim);
  if (ok) return claim.context.length;
  return 0;
}
export function sizeOr(claim: Row | number, other: number): number {
  const ok = isRow(claim) && other > 0;
  return ok ? claim.context.length : other;
}
