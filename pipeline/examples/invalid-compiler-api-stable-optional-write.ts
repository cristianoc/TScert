// A node's optional member written through a program alias: a node's
// members are readonly views, which a writable field's type does not
// admit, so the node is refused where the alias is formed, at the argument
// (COMPILER-API.md, "Stable members as readonly views"); and a write of an
// optional key through any alias is a key-adding write, refused at the
// write. No program code writes a stable member.
import type * as ts from "typescript/unstable/ast";

export function clear(w: { initializer: ts.Expression | undefined }): void {
  w.initializer = undefined;
}

export function clearNode(d: ts.VariableDeclaration): void {
  clear(d);
}
