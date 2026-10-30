// A `switch (node.kind)` on the compiler API's tag enum tests the node at
// each label: under `case ts.SyntaxKind.TupleType:` the node is a tuple
// type node, which has no `parameters`.
import * as ts from "typescript/unstable/ast";

export function arity(node: ts.TypeNode): number {
  switch (node.kind) {
    case ts.SyntaxKind.FunctionType:
      return node.parameters.length;
    case ts.SyntaxKind.TupleType:
      // @ts-expect-error: a tuple type node has no `parameters`
      return node.parameters.length;
    default:
      return -1;
  }
}
