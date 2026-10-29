// A compiler node's field narrowed by a guard is reread at the narrowed
// type after a `for...of` loop over its own list: a node's fields are
// stable members, whose read links every step keeps, the iterator's start
// and steps among them.
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
