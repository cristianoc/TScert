// Tag tests on a host node whose outcomes join, then a guard and the last
// element of a node list: the guard's `true` edge holds the node at the join
// of every path into it. A `switch (node.kind)` on the tag enum written with
// `case` labels tests the node at each label as the `===` test does
// (type-term.mts#readTypeTerm, behind type-term.mts#typeParts in the census).
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

export function arity(node: ts.TypeNode): number {
  switch (node.kind) {
    case ts.SyntaxKind.AnyKeyword:
    case ts.SyntaxKind.NeverKeyword:
      return 0;
    case ts.SyntaxKind.FunctionType:
      return node.parameters.length;
    case ts.SyntaxKind.TupleType:
      return node.elements.length;
    default:
      return -1;
  }
}
