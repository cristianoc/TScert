// A checker query at an array of nodes needs its array overload's result, one
// entry per node.
// Census functions:
// namespace-members.mts#namespaceMembers, unchecked.mts#check,
// unchecked.mts#findIn, unchecked.mts#typesOf.
import type { Checker } from "typescript/unstable/sync";
import type { Identifier } from "typescript/unstable/ast";
export function same(
  checker: Checker,
  ids: readonly Identifier[],
  id: number,
): boolean {
  const symbols = checker.getSymbolAtLocation(ids);
  return symbols[0]?.id === id;
}
