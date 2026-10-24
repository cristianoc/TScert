// A guard on a union holding an alias of one declaration, as `readTypeTerm`
// (tools/type-term.mts) reads `numeric.text` past `ts.isBigIntLiteral`:
// `Expression` is declared as `ExpressionBase`, and the guard's true branch
// takes the alias's arms as the declaration's, so it holds only
// `BigIntLiteral`, which has the field `text`.
import * as ts from "typescript/unstable/ast";

export function bigintText(n: ts.Expression | ts.Node): string {
  if (ts.isBigIntLiteral(n)) return n.text;
  return "";
}
