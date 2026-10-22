// A node method called on a union of nodes with an actual that runs code, as
// `collect` (tools/fragment-statements.mts) writes `${operand.getStart(gate.file)}`:
// `Expression` is a union of the nodes the module names, each a host of
// `getStart`; the member is read and bound to the node before `gate.file`
// is read, and the template converts the number it returns.
import * as ts from "typescript/unstable/ast";
import type { Expression, SourceFile } from "typescript/unstable/ast";

interface Gate {
  readonly file: SourceFile;
}

export function shape(n: Expression): number {
  if (ts.isIdentifier(n)) return 1;
  if (ts.isCallExpression(n)) return 2;
  if (ts.isPropertyAccessExpression(n)) return 3;
  if (ts.isKeywordExpression(n)) return 4;
  return 0;
}

export function tag(this: Gate, operand: Expression): string {
  const gate: Gate = this;
  return `${operand.getStart(gate.file)}`;
}
