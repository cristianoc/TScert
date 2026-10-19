// The type of a shorthand property assignment is a field the declarations state required and the runtime
// leaves absent (COMPILER-API.md, "Corrections"): its reading is optional,
// so it is no `TypeNode`. Under Node, on `a` in `({ a })`, the function returns
// `undefined`.
import * as ts from "typescript/unstable/ast";

export function read(p: ts.ShorthandPropertyAssignment): ts.TypeNode {
  return p.type;
}
