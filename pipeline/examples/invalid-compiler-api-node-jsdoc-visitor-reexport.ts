// A program re-export resolves to the handwritten visitor's declaration.
import { visitEachChildOfJSDocParameterTag } from "./compiler-api-node-jsdoc-visitor-reexport.ts";
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
