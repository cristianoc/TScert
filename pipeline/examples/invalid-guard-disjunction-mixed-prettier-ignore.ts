// A conjunction inside a disjunction is no disjunct to regroup: where
// `!isRow(claim) && typeof other === "number" || a` is false, `claim` may
// be the number, whose `context` is `undefined`, so `length` throws a
// TypeError: `size(1, "s", false)` under Node. TypeScript refuses the read.
// guard-disjunction-middle-test is its twin, of the same spans; prettier
// would add brackets around the conjunction and move the span.
type Row = { readonly context: readonly number[] };
function isRow(v: Row | number): v is Row {
  return typeof v !== "number";
}
export function size(
  claim: Row | number,
  other: number | string,
  a: boolean,
): number {
  if (!isRow(claim) && typeof other === "number" || a) return 0;
  return claim.context.length;
}
