// Census: fragment-statements.mts#patternStmt, #protocolPattern, #hoistTarget,
// #readScope, #unassigned, #block, #statements, #markEarly,
// #hoisting, #letPattern, #forStmt, #perIterationFor, #forInStmt,
// #protocolForOf, #switchStmt, #tryStmt, #abrupt, #stmt, #declarations,
// #declarator, #mutableList, #declarationsOf, #neverAssigned, #controlStmt.
// The compiler guard also accepts kind 346, outside the callee's contract.
import * as ts from "typescript/unstable/ast";

const importedNames = (st: ts.ImportDeclaration): string[] => {
  const clause = st.importClause;
  return clause?.name ? [clause.name.text] : [];
};
export function imported(st: ts.Statement): string[] {
  return ts.isImportDeclaration(st) ? importedNames(st) : [];
}
