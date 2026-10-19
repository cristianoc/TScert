// The parent of a source file is a field the declarations state required and the runtime
// leaves absent (COMPILER-API.md, "Corrections"): its reading is optional,
// so it is no `Node`. Under Node, on a source file, the function returns
// `undefined`.
import * as ts from "typescript/unstable/ast";

export function read(sf: ts.SourceFile): ts.Node {
  return sf.parent;
}
