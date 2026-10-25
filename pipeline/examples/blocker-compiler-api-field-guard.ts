// A loop needs to preserve a host child field narrowing for the read after the
// loop.
// Census functions:
// fragment-support.mts#forInEntryReads.
import * as ts from "typescript/unstable/ast";
export function use(node: ts.ForInStatement): number {
  if (!ts.isBlock(node.statement)) return 0;
  for (const statement of node.statement.statements) {
    if (ts.isVariableStatement(statement)) return 0;
  }
  return node.statement.statements.length;
}
