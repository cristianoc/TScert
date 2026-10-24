// A guard on a value that may be `undefined` (HOST-FAMILIES.md, "Undefined
// arguments") tests `undefined` first and keeps the domain obligation on
// the rest: a program object holding a parenthesized expression's kind is
// no node, refused at the call, which TypeScript refuses too. Under Node,
// `isParenthesizedExpression` answers `true` of it.
import * as ts from "typescript/unstable/ast";

export function parenthesized(
  o: { kind: ts.SyntaxKind.ParenthesizedExpression } | undefined,
): boolean {
  return ts.isParenthesizedExpression(o);
}

export function made(): boolean {
  return parenthesized({ kind: ts.SyntaxKind.ParenthesizedExpression });
}
