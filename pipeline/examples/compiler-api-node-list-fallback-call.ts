// A method call on a node list or a fresh empty array, `(n.arguments ?? [])`,
// each alternative reading `some` from the one array prototype: the call is
// the one an array gets, the member read and invoked without a dispatch on
// the object, so its footprint is the one `some` and its callback give, and
// a caller's narrowed field outlives it.
// Census functions: fragment-support.mts#runsCode,
// fragment-support.mts#selfConstructs.
import * as ts from "typescript/unstable/ast";

export function positioned(n: ts.NewExpression): boolean {
  const visit = (c: ts.Expression): boolean => c.pos > 0;
  return (n.arguments ?? []).some(visit);
}

export function kept(
  n: ts.NewExpression,
  box: { v: number | undefined },
): number {
  if (box.v === undefined) return 0;
  positioned(n);
  return box.v;
}
