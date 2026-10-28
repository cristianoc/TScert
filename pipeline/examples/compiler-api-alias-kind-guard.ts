// A type alias declaration recognised by its kind (`isTypeAlias` of
// tools/syntax.mts): the test excludes the JSDoc `@typedef`, whose kind
// `isTypeAliasDeclaration` also accepts, so the guard's promise holds and
// its true edge reads the alias's members, alone or in a disjunction with
// another guard.
// Census functions:
// type-term.mts#mapped, type-term.mts#computedAlias,
// computed-types.mts#computedType, type-probe.mts#makeProbe,
// fragment-parse.mts#lowerFile.
import * as ts from "typescript/unstable/ast";

export function isTypeAlias(node: ts.Node): node is ts.TypeAliasDeclaration {
  return node.kind === ts.SyntaxKind.TypeAliasDeclaration;
}

export function arity(node: ts.Node): number {
  return isTypeAlias(node) ? (node.typeParameters?.length ?? 0) : 0;
}

export function declaredName(node: ts.Node): string | null {
  return isTypeAlias(node) || ts.isInterfaceDeclaration(node)
    ? node.name.text
    : null;
}
