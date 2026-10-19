// A spread of a host node copies its own keys, which the model leaves
// unknown (under Node it has `parent` and no `kind`): refused at the spread
// (COMPILER-API.md, "Operations and their obligations").
import * as ts from "typescript/unstable/ast";

export function copy(n: ts.Node): object {
  return { ...n };
}
