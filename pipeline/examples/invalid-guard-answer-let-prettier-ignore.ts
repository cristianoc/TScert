// A guard's answer held in a `let`, reassigned between the test and the
// use: where it is `true`, `claim` may be the number, whose `context` is
// `undefined`, so `length` throws a TypeError: `size(1)` under Node.
// TypeScript refuses the read. Its twin, of the same spans, is
// guard-answer-let-twin-prettier-ignore.                        
type Row = { readonly context: readonly number[] };
function isRow(v: Row | number): v is Row {
  return typeof v !== "number";
}
export function size(claim: Row | number): number {
  let   ok = isRow(claim);
  ok = true;
  return ok ? claim.context.length : 0;
}
