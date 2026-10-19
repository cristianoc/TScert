// A test of `kind` gives the shape the table selects for it, never a
// refinement sharing its tag: a property access whose kind is tested is no
// `PropertyAccessEntityNameExpression`, whose `expression` is an entity name.
import * as ts from "typescript/unstable/ast";

export function entity(
  e: ts.Expression,
): ts.PropertyAccessEntityNameExpression | undefined {
  return e.kind === ts.SyntaxKind.PropertyAccessExpression ? e : undefined;
}
