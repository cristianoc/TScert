// A `finally` block runs after the `continue` it encloses: there, the
// binding may be the spread the test answered `true` of (run under Node).
import * as ts from "typescript/unstable/ast";

export function names(o: ts.ObjectLiteralExpression): ts.PropertyName[] {
  const out: ts.PropertyName[] = [];
  for (const p of o.properties) {
    try {
      if (ts.isSpreadAssignment(p)) continue;
    } finally {
      out.push(p.name);
    }
  }
  return out;
}
