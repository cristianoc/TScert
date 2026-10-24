// A family guard on a parameter its function never assigns, beside another
// function assigning its own `e`: the guard is the inline membership test
// of `f`'s `e`, decided by the binding, so its `false` branch leaves `e` an
// `Identifier`, which has the field `text`.
import * as ts from "typescript/unstable/ast";

export function f(e: ts.Identifier | ts.OmittedExpression): string {
  return ts.isOmittedExpression(e) ? "" : e.text;
}

export function w(e: ts.Node): ts.Node {
  if (ts.isParenthesizedExpression(e)) e = e.expression;
  return e;
}
