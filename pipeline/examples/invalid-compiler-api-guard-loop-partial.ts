// A guard whose tag set excludes another arm than the spread: past its
// `continue`, the binding may still be a spread (run under Node).
import * as ts from "typescript/unstable/ast";

export function names(o: ts.ObjectLiteralExpression): ts.PropertyName[] {
  const out: ts.PropertyName[] = [];
  for (const p of o.properties) {
    if (ts.isShorthandPropertyAssignment(p)) continue;
    out.push(p.name);
  }
  return out;
}
