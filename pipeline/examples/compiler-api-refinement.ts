// A refinement, a declaration whose tag is a literal the table selects
// another declaration for (HOST-FAMILIES.md, "The family contract"), is read
// as its own flattened members with the marker: its requirements are kept.
import * as ts from "typescript/unstable/ast";

export function head(
  e: ts.PropertyAccessEntityNameExpression,
): ts.EntityNameExpression {
  return e.expression;
}

export function last(e: ts.PropertyAccessEntityNameExpression): string {
  return e.name.text;
}
