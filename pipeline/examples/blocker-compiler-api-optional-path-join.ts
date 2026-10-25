// A host optional-member test needs compatible path claims at the following
// closure binding.
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
