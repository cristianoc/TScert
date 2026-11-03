// A disjunction whose first operand is a negated host guard: each operand
// is dispatched on its truth where the one before it failed, so the closure
// binding is reached only where `postfixToken` is undefined, which its entry
// claims.
// Census functions:
// declaration-graph.mts#overlaidInterface.
import * as ts from "typescript/unstable/ast";
export function use(
  member: ts.MethodSignatureDeclaration | ts.PropertySignatureDeclaration,
): void {
  if (
    !ts.isMethodSignatureDeclaration(member) ||
    member.typeParameters?.length ||
    member.postfixToken
  )
    throw Error("not plain");
  const nameOf = (p: ts.ParameterDeclaration): string =>
    ts.isIdentifier(p.name) ? p.name.text : "";
}
