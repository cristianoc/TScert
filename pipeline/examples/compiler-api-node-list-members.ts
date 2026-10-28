// A compiler-API node list's own members (COMPILER-API.md, "Node lists"):
// `pos` and `end` at `number`, `transformFlags` at `number` and
// `hasTrailingComma` at `boolean | undefined`, each read beside the list's
// readonly array members, through a union with another node list too.
import * as ts from "typescript/unstable/ast";

export function span(node: ts.FunctionDeclaration): number {
  const list = node.parameters;
  return list.end - list.pos + list.length;
}

export function trailing(node: ts.CallExpression): boolean {
  return (
    node.arguments.hasTrailingComma === true &&
    node.arguments.transformFlags >= 0
  );
}

export function head(node: ts.FunctionDeclaration): number {
  return (node.typeParameters ?? node.parameters).pos;
}
