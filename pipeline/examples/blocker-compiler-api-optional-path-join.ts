// A disjunction whose first operand is a negated host guard is lowered as a
// value, and the condition tests that value: where `typeParameters?.length`
// passed, the value is tested again, and a number's truthy slice is
// `number`, so the re-test's failing edge reaches the closure binding
// without the fact that `postfixToken` is undefined, which its entry claims.
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
