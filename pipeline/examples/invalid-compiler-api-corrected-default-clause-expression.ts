// The expression of a default clause is a field the declarations state required and the runtime
// leaves absent (COMPILER-API.md, "Corrections"): its reading is optional,
// so it is no `Expression`. Under Node, on `default:` in a switch, the function returns
// `undefined`.
import * as ts from "typescript/unstable/ast";

export function read(c: ts.DefaultClause): ts.Expression {
  return c.expression;
}
