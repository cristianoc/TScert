// Census: fragment-statements.mts#patternStmt, #protocolPattern, #hoistTarget,
// #readScope, #readCannotThrow, #unassigned, #block, #statements, #markEarly,
// #hoisting, #letPattern, #forStmt, #perIterationFor, #forInStmt,
// #protocolForOf, #switchStmt, #tryStmt, #abrupt, #stmt, #declarations,
// #declarator, #mutableList, #declarationsOf, #neverAssigned, #controlStmt.
// A compiler guard's true branch passes its node to an import-only function.
import * as ts from "typescript/unstable/ast";

const importedNames = (st: ts.ImportDeclaration): string[] => {
  const clause = st.importClause;
  return clause?.name ? [clause.name.text] : [];
};
export function imported(st: ts.Statement): string[] {
  return ts.isImportDeclaration(st) ? importedNames(st) : [];
}
