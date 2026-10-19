// The compiler API's guards, read from their audited entries
// (HOST-FAMILIES.md, "Calls"): a call of an immutable name is the test of its
// tag against the entry's exact tag set, which narrows both edges, through a
// namespace import or a named one, under `!`, `&&` and a conditional, for a
// set of one tag or of 167; a tag guard narrows the tag itself.
import * as ts from "typescript/unstable/ast";
import { isIdentifier, isStringLiteral } from "typescript/unstable/ast";

export function nameLength(node: ts.Node): number {
  if (ts.isIdentifier(node)) return node.text.length;
  return 0;
}

export function literalLength(node: ts.Node): number {
  if (!isStringLiteral(node)) return 0;
  return node.text.length;
}

export function elementCount(name: ts.BindingName): number {
  if (isIdentifier(name)) return 0;
  return name.elements.length;
}

export function both(a: ts.Node, b: ts.Node): number {
  return ts.isIdentifier(a) && ts.isStringLiteral(b) ? a.text.length + b.text.length : 0;
}

export function token(node: ts.Node): number {
  return ts.isToken(node) ? node.pos : node.end;
}

export function modifier(kind: ts.SyntaxKind): ts.ModifierSyntaxKind | null {
  return ts.isModifierKind(kind) ? kind : null;
}
