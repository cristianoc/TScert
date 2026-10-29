// A constant holding a guard's answer, the guarded `let` reassigned
// between the test and the use: where the constant is `true`, `c` holds
// 1, whose `context` is `undefined`, so `length` throws a TypeError:
// `size({ context: [] })` under Node. TypeScript refuses the read. Its
// twin, of the same spans, is guard-answer-reassigned-twin-prettier-ignore.
type Row = { readonly context: readonly number[] };
function isRow(v: Row | number): v is Row {
  return typeof v !== "number";
}
export function size(claim: Row | number): number {
  let   c = claim;
  const ok = isRow(c);
  c = 1;
  return ok ? c.context.length : 0;
}
