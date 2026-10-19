// The constraint of a JSDoc template tag is a field the declarations state required and the runtime
// leaves absent (COMPILER-API.md, "Corrections"): its reading is optional,
// so it is no `Node`. Under Node, on `/** @template T */`, the function returns
// `undefined`.
import * as ts from "typescript/unstable/ast";

export function read(t: ts.JSDocTemplateTag): ts.Node {
  return t.constraint;
}
