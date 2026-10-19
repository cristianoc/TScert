// The type of an export assignment is a field the declarations state required and the runtime
// leaves absent (COMPILER-API.md, "Corrections"): its reading is optional,
// so it is no `TypeNode`. Under Node, on `export default 1`, the function returns
// `undefined`.
import * as ts from "typescript/unstable/ast";

export function read(e: ts.ExportAssignment): ts.TypeNode {
  return e.type;
}
