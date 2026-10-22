// A loop binding written after the test: the element the test excluded is
// replaced by another, a spread (run under Node).
import * as ts from "typescript/unstable/ast";

export function names(
  o: ts.ObjectLiteralExpression,
  other: ts.ObjectLiteralElementLike,
): ts.PropertyName[] {
  const out: ts.PropertyName[] = [];
  for (let p of o.properties) {
    if (ts.isSpreadAssignment(p)) continue;
    p = other;
    out.push(p.name);
  }
  return out;
}
