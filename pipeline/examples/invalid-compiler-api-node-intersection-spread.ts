// A spread of a host node met with a record copies the node's own keys,
// which the model leaves unknown: refused at the merge, whose operand admits
// a host object. Under Node the copy of an identifier has no `kind`.
import * as ts from "typescript/unstable/ast";

export function copiedKind(n: ts.Node & { text: string }): number {
  return { ...n }.kind;
}
