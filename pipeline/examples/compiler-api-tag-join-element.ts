// Tag tests on a host node, joined, then a guard and the last element of a
// node list: the producer types a receiver as holding a boolean where
// TypeScript gives it none, and refuses. A `switch (node.kind)` on the tag
// enum written with `case` labels tests the same way (type-term.mts#readTypeTerm,
// behind type-term.mts#typeParts in the census).
import * as ts from "typescript/unstable/ast";

export function rest(node: ts.TypeNode): number {
  if (node.kind !== ts.SyntaxKind.AnyKeyword) {
    if (node.kind === ts.SyntaxKind.NeverKeyword) return 0;
    if (node.kind === ts.SyntaxKind.VoidKeyword) return 0;
    if (node.kind === ts.SyntaxKind.ObjectKeyword) return 0;
  }
  if (ts.isFunctionTypeNode(node)) {
    const last = node.parameters[node.parameters.length - 1];
    if (last && last.dotDotDotToken) return 1;
  }
  return 2;
}
