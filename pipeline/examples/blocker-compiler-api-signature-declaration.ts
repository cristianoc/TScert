// The declaration of a resolved signature needs a reading in the
// compiler-API contract's view of Signature.
// Census functions:
// declaration-graph.mts#globalFunction, declaration-graph.mts#selectGlobal.
import type { Checker } from "typescript/unstable/sync";
import type { CallExpression } from "typescript/unstable/ast";
export function declared(checker: Checker, call: CallExpression): boolean {
  return !!checker.getResolvedSignature(call)?.declaration?.resolve();
}
