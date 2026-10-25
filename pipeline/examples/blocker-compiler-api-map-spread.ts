// A map of compiler nodes using their text method needs a dense result for a
// later spread.
// Census functions:
// unchecked.mts#unstated.
import type { SignatureDeclaration } from "typescript/unstable/ast";
export function use(node: SignatureDeclaration): string[] {
  const missing = node.parameters
    .filter((p) => p.type === undefined)
    .map((p) => `parameter ${p.name.getText()}`);
  return [...missing, "result"];
}
