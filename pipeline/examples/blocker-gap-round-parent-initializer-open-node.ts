// Open-node initializer lookup expressed through compiler kind guards.
// Census functions:
// written-applications.mts#writtenApplications
import type { Node } from "typescript/unstable/ast";
import * as ts from "typescript/unstable/ast";
export function initializer(node: Node): boolean {
  const owner = node.parent;
  return (
    !!owner &&
    (ts.isVariableDeclaration(owner) ||
      ts.isParameterDeclaration(owner) ||
      ts.isBindingElement(owner) ||
      ts.isEnumMember(owner) ||
      ts.isPropertySignatureDeclaration(owner) ||
      ts.isPropertyDeclaration(owner) ||
      ts.isPropertyAssignment(owner) ||
      ts.isJsxAttribute(owner) ||
      ts.isForStatement(owner) ||
      ts.isForInStatement(owner) ||
      ts.isForOfStatement(owner)) &&
    owner.initializer === node
  );
}
