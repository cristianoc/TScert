// Recursive parent walk checked at several signatures.
// Census functions:
// fragment-parse.mts#parseFile
// fragment-parse.mts#parseFragment
// fragment-parse.mts#lowerModule
// fragment-parse.mts#lowerModuleText
// fragment-parse.mts#parseModules
// fragment-parse.mts#lowerFile
import * as ts from "typescript/unstable/ast";
import type { Node, Identifier } from "typescript/unstable/ast";
export function walk(nodes: readonly Identifier[]): Node[] {
  const topStatement = (n: Node): Node =>
    n.parent && !ts.isSourceFile(n.parent) ? topStatement(n.parent) : n;
  return nodes.map(topStatement);
}
