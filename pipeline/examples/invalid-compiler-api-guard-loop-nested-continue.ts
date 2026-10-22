// A `continue` inside a nested loop continues that loop: past it, the outer
// binding may still be a spread, which has no `name` (run under Node).
import * as ts from "typescript/unstable/ast";

export function names(o: ts.ObjectLiteralExpression): ts.PropertyName[] {
  const out: ts.PropertyName[] = [];
  for (const p of o.properties) {
    for (let i = 0; i < 1; i++) {
      if (ts.isSpreadAssignment(p)) continue;
    }
    out.push(p.name);
  }
  return out;
}
