// Census: tools/fragment-support.mts#jumpTarget.
import * as ts from "typescript/unstable/ast";
export function walk(node: ts.BreakStatement): ts.Node | undefined {
  let parent = node.parent;
  while (parent) parent = parent.parent;
  return parent;
}
