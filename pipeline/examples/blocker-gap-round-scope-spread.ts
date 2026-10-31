// Scope spread overriding callbacks and a type alias's source file.
// Census functions:
// type-term.mts#typeParts
// type-term.mts#someType
// type-term.mts#visitType
// type-term.mts#validateAnnotation
// type-term.mts#typeTerm
// type-term.mts#readTypeTerm
// type-term.mts#constructorForms
// type-term.mts#mapped
// type-term.mts#expandMapped
// type-term.mts#expandIdentity
// type-term.mts#substitute
// type-term.mts#mapTypeParts
// type-term.mts#tuple
// type-term.mts#intersection
// type-term.mts#signature
// type-term.mts#quantified
// type-term.mts#signatures
// type-term.mts#statedResult
// type-term.mts#statementOf
// type-term.mts#promiseOf
// type-term.mts#members
// type-term.mts#sameIndex
// type-term.mts#sameTerm
// type-term.mts#sameTerms
// type-term.mts#sameOptionalTerm
// type-term.mts#sameOptionalIndex
// type-term.mts#sameStatics
// type-term.mts#indexKinds
// type-term.mts#classInstance
import * as ts from "typescript/unstable/ast";
import type {
  TypeAliasDeclaration,
  TypeReferenceNode,
  TypeParameterDeclaration,
} from "typescript/unstable/ast";
import type { TermScope } from "../../tools/type-term.mts";
import type { TypeTerm } from "../../tools/declaration-types.mts";
export function extend(
  scope: TermScope,
  alias: TypeAliasDeclaration,
  parameters: readonly TypeParameterDeclaration[],
  inputs: readonly TypeTerm[],
  expandingAliases: Set<TypeAliasDeclaration>,
): TermScope {
  const inner: TermScope = {
    ...scope,
    source: alias.getSourceFile(),
    expandingAliases,
    awaited: (reference) => {
      const name = reference.typeName;
      return (
        !(
          ts.isIdentifier(name) &&
          parameters.some((p) => p.name.text === name.text)
        ) &&
        (scope.awaited?.(reference) ?? false)
      );
    },
    associatedAlias: (reference) => {
      const name = reference.typeName;
      return ts.isIdentifier(name) &&
        parameters.some((p) => p.name.text === name.text)
        ? null
        : (scope.associatedAlias?.(reference) ?? null);
    },
    named(reference, position, read) {
      const name = reference.typeName;
      const index = ts.isIdentifier(name)
        ? parameters.findIndex((p) => p.name.text === name.text)
        : -1;
      if (index < 0) return scope.named(reference, position, read);
      const input = inputs[index];
      if (!input || reference.typeArguments?.length)
        return scope.fail(reference, "invalid alias argument");
      return input;
    },
  };
  return inner;
}
