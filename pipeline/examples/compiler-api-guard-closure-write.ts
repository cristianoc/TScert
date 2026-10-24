// A family guard on a parameter a nested closure assigns: the write names
// the binding, so the guard is an ordinary call at its promise signature,
// not the inline membership test (`pipeline/test.mts` reads the lowering).
import * as ts from "typescript/unstable/ast";

export function f(
  e: ts.Identifier | ts.OmittedExpression,
  other: ts.OmittedExpression,
): number {
  const reset = (): void => {
    e = other;
  };
  reset();
  return ts.isOmittedExpression(e) ? 0 : 1;
}
