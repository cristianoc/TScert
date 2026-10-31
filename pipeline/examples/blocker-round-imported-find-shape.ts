// A host-declaration map/get/find result losing its node field in an importing module.
// Census functions:
// computed-types.mts#computedType
// computed-types.mts#aliasApplication
// computed-types.mts#unionMembers
// computed-types.mts#distributed

import type { Checker } from "typescript/unstable/sync";

import type {
  Node,
  TypeNode,
  TypeReferenceNode,
} from "typescript/unstable/ast";

// The imported module is part of the missing-field example's context.
import { computedAlias } from "../../tools/type-term.mts";

type ComputedContext = { checker: Checker };

type Member = { node: TypeNode; params: ReadonlyMap<Node, Member> };

export function unionMembers(
  context: ComputedContext,
  node: TypeReferenceNode,
  params: ReadonlyMap<Node, Member> = new Map(),
): Member[] {
  const declarations = (
    context.checker.getSymbolAtLocation(node.typeName)?.declarations ?? []
  ).map((d) => d.resolve());
  const standing = declarations
    .map((d) => d && params.get(d))
    .find((m) => m !== undefined);
  if (standing) return [{ node: standing.node, params: standing.params }];
  return [{ node, params }];
}
