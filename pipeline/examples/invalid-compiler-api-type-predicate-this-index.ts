// A predicate about `this` is declared with `parameterIndex: undefined`, but
// the client copies the server's index, which is 0 for it: a test of the
// index tells no parameter's predicate from it, and its `parameterName` is
// `undefined` (run under Node). The contract's views of the `this`
// predicates state no `parameterIndex`.
import type { Checker, Signature } from "typescript/unstable/sync";

export function wrong(checker: Checker, signature: Signature): string {
  const predicate = checker.getTypePredicateOfSignature(signature);
  if (predicate === undefined || predicate.parameterIndex === undefined)
    return "";
  return predicate.parameterName;
}
