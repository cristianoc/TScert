// The kind of a signature's type predicate, `TypePredicateKind` of the
// compiler-API contract's host enums (COMPILER-API.md, reading rule 3), read
// as `declaration-graph.mts#collectDeclarations` reads it: a predicate about
// a parameter, asserted or tested, its index read where its kind states one.
import {
  TypePredicateKind,
  type Checker,
  type Signature,
  type Type,
} from "typescript/unstable/sync";

export function promisedIndex(
  checker: Checker,
  signature: Signature,
): number | undefined {
  const predicate = checker.getTypePredicateOfSignature(signature);
  if (!predicate) return undefined;
  if (
    predicate.kind !== TypePredicateKind.Identifier &&
    predicate.kind !== TypePredicateKind.AssertsIdentifier
  )
    return undefined;
  const asserts = predicate.kind === TypePredicateKind.AssertsIdentifier;
  const about = predicate.parameterIndex;
  const promised = predicate.type;
  return promised && !asserts ? about : undefined;
}

// A tested predicate about a parameter, `TypePredicateKind.Identifier`,
// states its type.
export function testedType(
  checker: Checker,
  signature: Signature,
): Type | null {
  const predicate = checker.getTypePredicateOfSignature(signature);
  if (
    predicate === undefined ||
    predicate.kind !== TypePredicateKind.Identifier
  )
    return null;
  return predicate.type;
}
