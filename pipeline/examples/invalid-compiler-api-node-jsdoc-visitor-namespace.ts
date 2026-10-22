// The AST namespace exposes the handwritten property-tag builder too.
import * as ts from "typescript/unstable/ast";

export function visitorParent(
  tag: ts.JSDocPropertyTag,
  replacement: ts.Identifier,
): ts.Node {
  return ts.visitEachChildOfJSDocPropertyTag(tag, (node) =>
    node === tag.name ? replacement : node,
  ).parent;
}
