// The type of a property assignment is a field the declarations state required and the runtime
// leaves absent (COMPILER-API.md, "Corrections"): its reading is optional,
// so it is no `TypeNode`. Under Node, on `a: 1` in an object literal, the function returns
// `undefined`.
import * as ts from "typescript/unstable/ast";

export function read(p: ts.PropertyAssignment): ts.TypeNode {
  return p.type;
}
