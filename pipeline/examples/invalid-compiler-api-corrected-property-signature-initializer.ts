// The initializer of a property signature is a field the declarations state required and the runtime
// leaves absent (COMPILER-API.md, "Corrections"): its reading is optional,
// so it is no `Expression`. Under Node, on `x: number` in an interface, the function returns
// `undefined`.
import * as ts from "typescript/unstable/ast";

export function read(p: ts.PropertySignatureDeclaration): ts.Expression {
  return p.initializer;
}
