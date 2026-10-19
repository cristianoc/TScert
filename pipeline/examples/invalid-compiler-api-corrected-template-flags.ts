// The template flags of a template literal without substitutions is a field the declarations state required and the runtime
// leaves absent (COMPILER-API.md, "Corrections"): its reading is optional,
// so it is no `number`. Under Node, on `` `a` ``, the function returns
// `undefined`.
import * as ts from "typescript/unstable/ast";

export function read(t: ts.NoSubstitutionTemplateLiteral): number {
  return t.templateFlags;
}
