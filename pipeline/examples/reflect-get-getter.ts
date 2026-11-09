/// <reference path="../../tools/resolvable.d.ts" />
// Compiler children read through their declared kinds, retaining the host
// field contracts and copying child lists.
// Census functions:
// syntax.mts#childOf, syntax.mts#childrenOf.
import * as ts from "typescript/unstable/ast";
import type { Node } from "typescript/unstable/ast";

export function childOf(
  node: Node,
): Modifies<{ values: "any"; stores: "grow" }, Node | undefined> {
  if (ts.isBreakStatement(node)) return node.label;
  if (ts.isContinueStatement(node)) return node.label;
  if (ts.isLabeledStatement(node)) return node.label;
  return undefined;
}

export function childrenOf(
  node: Node,
): Modifies<{ values: "any"; stores: "grow" }, readonly Node[]> {
  if (ts.isFunctionDeclaration(node)) return node.parameters.filter(() => true);
  return [];
}
