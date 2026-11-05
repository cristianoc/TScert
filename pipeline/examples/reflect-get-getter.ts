/// <reference path="../../tools/resolvable.d.ts" />
// Census: syntax.mts#childOf and #childrenOf.
// Representative single-child and child-list reads through declared kinds.
import * as ts from "typescript/unstable/ast";
import type { Node } from "typescript/unstable/ast";

export function childOf(
  node: Node,
): Within<{ value: "any"; store: "grow" }, Node | undefined> {
  if (ts.isBreakStatement(node)) return node.label;
  if (ts.isContinueStatement(node)) return node.label;
  if (ts.isLabeledStatement(node)) return node.label;
  return undefined;
}

export function childrenOf(
  node: Node,
): Within<{ value: "any"; store: "grow" }, readonly Node[]> {
  if (ts.isFunctionDeclaration(node)) return node.parameters.filter(() => true);
  return [];
}
