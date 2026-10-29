// An asserted predicate about a parameter, `TypePredicateKind.AssertsIdentifier`,
// may state no type: `asserts x` has none, so its `type` is `undefined`,
// which `!` does not rule out (run under Node).
import {
  TypePredicateKind,
  type Checker,
  type Signature,
  type Type,
} from "typescript/unstable/sync";

export function wrong(checker: Checker, signature: Signature): Type | null {
  const predicate = checker.getTypePredicateOfSignature(signature);
  if (
    predicate === undefined ||
    predicate.kind !== TypePredicateKind.AssertsIdentifier
  )
    return null;
  return predicate.type!;
}
