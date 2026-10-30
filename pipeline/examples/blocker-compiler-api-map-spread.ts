// A map of compiler nodes calling their text method on a parameter's name,
// a union of binding-name kinds each declaring the method: the callback keeps
// every array store, so the map's result is dense for a later spread.
// Census functions:
// unchecked.mts#unstated.
import type { SignatureDeclaration } from "typescript/unstable/ast";
export function use(node: SignatureDeclaration): string[] {
  const missing = node.parameters
    .filter((p) => p.type === undefined)
    .map((p) => `parameter ${p.name.getText()}`);
  return [...missing, "result"];
}
