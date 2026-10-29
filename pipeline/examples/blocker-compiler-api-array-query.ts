// A checker query at an array of nodes: the array overload's result, one
// entry per node, each a host object or `undefined`.
// Census functions:
// namespace-members.mts#namespaceMembers, unchecked.mts#check,
// unchecked.mts#findIn, unchecked.mts#typesOf.
import type { Checker, Type } from "typescript/unstable/sync";
import type { Identifier, Node } from "typescript/unstable/ast";
export function same(
  checker: Checker,
  ids: readonly Identifier[],
  id: number,
): boolean {
  const symbols = checker.getSymbolAtLocation(ids);
  return symbols[0]?.id === id;
}
export function typesOf(
  checker: Checker,
  nodes: Node[],
): readonly (Type | undefined | null)[] {
  return checker.getTypeAtLocation(nodes);
}
