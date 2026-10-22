// The handwritten visitor builds a replacement root without the required parent.
import { visitEachChildOfJSDocParameterTag } from "typescript/unstable/ast/visitor";
import type {
  JSDocParameterTag,
  Identifier,
  Node,
} from "typescript/unstable/ast";

export function visitorParent(
  tag: JSDocParameterTag,
  replacement: Identifier,
): Node {
  return visitEachChildOfJSDocParameterTag(tag, (node) =>
    node === tag.name ? replacement : node,
  ).parent;
}
