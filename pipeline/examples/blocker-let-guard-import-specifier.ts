// The module specifier of the import or export statement a node lies in,
// read on a `let` the loop walks up through `parent` and a disjunction of
// `isImportDeclaration` and `isExportDeclaration` tests: the first guard
// also accepts a JSDoc `@import` (kind 346), whose audited shape
// (COMPILER-API.md, "Audited shapes") states `moduleSpecifier`, as
// `ImportDeclaration` does, so the read is of a member every arm states.
// Under Node, on an `@import` tag's node, it returns its specifier.
// Census functions:
// declaration-graph.mts#collectDeclarations, declaration-graph.mts#statementsOnPath.
import * as ts from "typescript/unstable/ast";

export function specifierOf(start: ts.Node | undefined): ts.Node | undefined {
  let node: ts.Node | undefined = start;
  while (
    node &&
    !ts.isImportDeclaration(node) &&
    !ts.isExportDeclaration(node) &&
    !ts.isSourceFile(node)
  )
    node = node.parent;
  if (node && (ts.isImportDeclaration(node) || ts.isExportDeclaration(node)))
    return node.moduleSpecifier;
  return undefined;
}
