// Census functions: type-term.mts#typeTerm,#constructorForms and their callers.
// A nonempty type literal whose every member is a construct signature.
import * as ts from "typescript/unstable/ast";

export function constructorsOnly(node: ts.Node): boolean {
  if (ts.isTypeLiteralNode(node) && node.members.length &&
      node.members.every(ts.isConstructSignatureDeclaration)) return true;
  return false;
}
