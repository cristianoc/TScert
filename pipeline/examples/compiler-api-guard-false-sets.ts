// A guard's false edge over an arm whose tag is a set (HOST-FAMILIES.md,
// "Calls"; PROGRAM-TYPING.md, "A membership test"): where `isToken` answers
// false, the `Token` arm of the set `DotToken | CommaToken`, all of which
// `isToken` accepts, is gone, so the node is the computed name; where
// `isDotToken` answers false, the same arm is read at its rest, a
// `CommaToken`, whose kind test then leaves the computed name too. Over
// `Node`, `isToken`'s false edge holds none of the arms of `Token`. The
// constant returns are the neighbours of `pipeline/test.mts`'s forged claims.
import * as ts from "typescript/unstable/ast";

type Punctuation = ts.Token<ts.SyntaxKind.DotToken | ts.SyntaxKind.CommaToken>;

export function nonToken(n: Punctuation | ts.ComputedPropertyName): number {
  if (ts.isToken(n)) return 0;
  return n.expression.pos;
}

export function afterDot(n: Punctuation | ts.ComputedPropertyName): number {
  if (ts.isDotToken(n)) return 0;
  if (n.kind === ts.SyntaxKind.CommaToken) return 1;
  return n.expression.pos;
}

export function anyNode(n: ts.Node): number {
  if (ts.isToken(n)) return 0;
  return n.pos;
}

export function nonTokenConstant(
  n: Punctuation | ts.ComputedPropertyName,
): number {
  if (ts.isToken(n)) return 0;
  return 1;
}

export function afterDotConstant(
  n: Punctuation | ts.ComputedPropertyName,
): number {
  if (ts.isDotToken(n)) return 0;
  return 1;
}

export function onTrue(n: Punctuation | ts.ComputedPropertyName): number {
  if (ts.isDotToken(n)) return n.pos;
  return 1;
}
