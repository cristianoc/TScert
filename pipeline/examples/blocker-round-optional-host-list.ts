// An optional host typeParameters list passed after testing its length.
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
import type {
  FunctionTypeNode,
  TypeParameterDeclaration,
} from "typescript/unstable/ast";
function consume(xs: readonly TypeParameterDeclaration[]): number {
  return xs.length;
}
export function parameters(node: FunctionTypeNode): number {
  if (!node.typeParameters?.length) return 0;
  return consume(node.typeParameters);
}
