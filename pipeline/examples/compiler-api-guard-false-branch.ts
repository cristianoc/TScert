// A listed guard's call of an immutable name is the test of its tag against
// the entry's tag set (HOST-FAMILIES.md, "Calls"), which narrows both edges:
// where `isIdentifier` answers `true`, `node` is an `Identifier`; where it
// answers `false`, the `BindingName` arms but `Identifier`, each of which
// has `elements`.
import * as ts from "typescript/unstable/ast";

export function count(node: ts.BindingName): number {
  if (ts.isIdentifier(node)) return node.text.length;
  return node.elements.length;
}
