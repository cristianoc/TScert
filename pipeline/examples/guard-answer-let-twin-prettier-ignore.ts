// A constant holding a guard's answer, read alone between the test and
// the use: where it is `true`, `claim` is a `Row`. The twin, of the same
// spans, whose claims `pipeline/test.mts` gives the negative
// invalid-guard-answer-let-prettier-ignore, which reassigns a `let`.
// Its claims state the constant's implication across the statement.
type Row = { readonly context: readonly number[] };
function isRow(v: Row | number): v is Row {
  return typeof v !== "number";
}
export function size(claim: Row | number): number {
  const ok = isRow(claim);
  ok;       
  return ok ? claim.context.length : 0;
}
