// A member of a type alias read after `isTypeAliasDeclaration`, which also
// accepts a JSDoc `@typedef` (kind 345): the compiler-API description's
// audited shape of `JSTypeAliasDeclaration` states its `typeParameters`, as
// `TypeAliasDeclaration` does, so the read is of a member both arms state.
// Under Node, on a `@typedef` with two `@template` tags, it returns 2.
// Census functions:
// type-term.mts#typeTerm, type-term.mts#mapped, type-term.mts#expandMapped,
// type-term.mts#computedAlias, type-term.mts#members, type-term.mts#signatures,
// type-term.mts#readTypeTerm and 15 others of type-term.mts reaching typeTerm,
// computed-types.mts#computedType, computed-types.mts#aliasApplication,
// computed-types.mts#indexedAccess, type-probe.mts#makeProbe.
import * as ts from "typescript/unstable/ast";

export function arity(node: ts.Node): number {
  return ts.isTypeAliasDeclaration(node)
    ? (node.typeParameters?.length ?? 0)
    : 0;
}
