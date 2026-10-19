// A listed guard's call of an immutable name is the test of its tag against
// the entry's tag set (HOST-FAMILIES.md, "Calls"), which narrows both edges:
// where `isIdentifier` answers `false`, `node` is the `BindingName` arms but
// `Identifier`, each of which has `elements`.
import * as ts from "typescript/unstable/ast";

export function count(node: ts.BindingName): number {
  if (ts.isIdentifier(node)) return 0;
  return node.elements.length;
}
