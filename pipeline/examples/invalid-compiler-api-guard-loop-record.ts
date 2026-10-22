// A loop binding holding a program record: the test is of the node its
// member holds, which the call may replace, so the read past the call is of
// the member's declared type (run under Node).
import * as ts from "typescript/unstable/ast";

export function names(
  entries: readonly { node: ts.ObjectLiteralElementLike }[],
  change: () => void,
): ts.PropertyName[] {
  const out: ts.PropertyName[] = [];
  for (const entry of entries) {
    if (ts.isSpreadAssignment(entry.node)) continue;
    change();
    out.push(entry.node.name);
  }
  return out;
}
