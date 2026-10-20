// A spread of a host node copies its own keys, which the model leaves
// unknown: refused at the spread (COMPILER-API.md, "Operations and their
// obligations"). Under Node the copy has `parent` and no `kind`, so `kind`
// reads `undefined`.
import * as ts from "typescript/unstable/ast";

export function copiedKind(n: ts.Node): number {
  return { ...n }.kind;
}
