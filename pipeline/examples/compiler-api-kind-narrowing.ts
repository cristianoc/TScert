// The compiler API's nodes are a host family (HOST-FAMILIES.md): `Node` is the
// union of the shapes the run names and one residual for the other kinds,
// so a test of `kind` against a constant gives the named shape, whose members
// it reads, on its true edge: the JavaScript typedef's, which no declaration
// states, the base declaration's. Each shape, a token's included, is a `Node`.
import * as ts from "typescript/unstable/ast";

export function nameOf(n: ts.Node): string {
  return n.kind === ts.SyntaxKind.Identifier ? n.text : "";
}

export function fileName(n: ts.Node): string {
  return n.kind === ts.SyntaxKind.SourceFile
    ? n.fileName
    : n.kind === ts.SyntaxKind.StringLiteral
      ? n.text
      : "";
}

export function asNode(i: ts.Identifier): ts.Node {
  return i;
}

export function token(t: ts.QuestionToken): ts.Node {
  return t;
}

export function typedefFlags(n: ts.Node): number {
  return n.kind === ts.SyntaxKind.JSTypeAliasDeclaration ? n.flags : 0;
}
