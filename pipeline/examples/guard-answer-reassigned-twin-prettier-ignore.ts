// A constant holding a guard's answer of a constant, read between the
// test and the use: where the answer is `true`, `c` is a `Row`. The twin,
// of the same spans, whose claims `pipeline/test.mts` gives the negative
// invalid-guard-answer-reassigned-prettier-ignore, which reassigns `c`,
// a `let` there.                                                  
type Row = { readonly context: readonly number[] };
function isRow(v: Row | number): v is Row {
  return typeof v !== "number";
}
export function size(claim: Row | number): number {
  const c = claim;
  const ok = isRow(c);
  c;    
  return ok ? c.context.length : 0;
}
