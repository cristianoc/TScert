// A node list owns `hasTrailingComma` holding `undefined`: it is no value
// of the exact reading of `{ readonly hasTrailingComma?: boolean }`, absent
// or a Boolean, so passing it there is refused (run under Node: the key is
// in the list and its value is `undefined`).
import type * as ts from "typescript/unstable/ast";

function heldUndefined(r: { readonly hasTrailingComma?: boolean }): boolean {
  return "hasTrailingComma" in r && r.hasTrailingComma === undefined;
}

export function trailingHeld(node: ts.FunctionDeclaration): boolean {
  return heldUndefined(node.parameters);
}
