// The empty-array fallback has no node-list position metadata.
import type { FunctionDeclaration } from "typescript/unstable/ast";

export function position(n: FunctionDeclaration): number {
  return (n.typeParameters ?? []).pos;
}
