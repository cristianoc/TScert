// A TypeNode found by the host guard needs its recursive host shape admitted
// at the declared TypeNode contract.
// Census functions:
// declaration-graph.mts#computedAt, declaration-graph.mts#typeNodeAt.
import * as ts from "typescript/unstable/ast";
export function use(node: ts.Node): ts.TypeNode | null {
  return ts.isTypeNode(node) ? node : null;
}
