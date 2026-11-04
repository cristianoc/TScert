// Census: fragment-statements.mts#patternStmt, #protocolPattern, #hoistTarget,
// #readScope, #unassigned, #block, #statements, #markEarly,
// #hoisting, #letPattern, #forStmt, #perIterationFor, #forInStmt,
// #protocolForOf, #switchStmt, #tryStmt, #abrupt, #stmt, #declarations,
// #declarator, #mutableList, #declarationsOf, #neverAssigned, #controlStmt.
// An exact-kind guard passes its node to an import-only function.
import * as ts from "typescript/unstable/ast";

function isImport(node: ts.Node): node is ts.ImportDeclaration {
  return node.kind === ts.SyntaxKind.ImportDeclaration;
}

const importedNames = (st: ts.ImportDeclaration): string[] => {
  const clause = st.importClause;
  return clause?.name ? [clause.name.text] : [];
};
export function imported(st: ts.Statement): string[] {
  return isImport(st) ? importedNames(st) : [];
}
